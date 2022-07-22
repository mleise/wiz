#include <algorithm>
#include <filesystem>
#include <map>

#include <wiz/ast/qualifiers.h>
#include <wiz/ast/statement.h>
#include <wiz/ast/type_expression.h>
#include <wiz/compiler/bank.h>
#include <wiz/compiler/compiler.h>
#include <wiz/compiler/definition.h>
#include <wiz/compiler/ir_node.h>
#include <wiz/compiler/symbol_table.h>
#include <wiz/compiler/version.h>
#include <wiz/format/output/output_format.h>
#include <wiz/format/debug/cdb_sym_debug_format.h>
#include <wiz/utility/misc.h>
#include <wiz/utility/path.h>
#include <wiz/utility/resource_manager.h>
#include <wiz/utility/scope_guard.h>
#include <wiz/utility/text.h>
#include <wiz/utility/writer.h>

/* See: https://k1.spdns.de/Develop/Hardware/AVR/mixed%20docs.../doc/cdbfileformat.pdf
 * SDCC behaves a little different from that PDF and some things are vague. Always compare SDCC output for similar C code.
 * A) Module names, are the file name stripped of the last extension (if any) and with all remaining dots replaced by underscores.
 *    The files `foo.bar.c` and `foo_bar.c` are both written as `foo_bar` in the CDB. SDCC also drops all path components in the
 *    Linker C-Line Record, but we will be liberal here and use relative paths, to two files in different sub-directories can
 *    share the same name. Emulicious has been tested to look up the correct "version" of the file.
 * B) Block, Level & Sub-Level: These can be 0 until inside a code block, where they are used to mark at which code address the
 *    debugger should make each local variable visible. They are formated as `$<level>_<sublevel>$block`.
 *    Block is a sequential number giving each scope an identity. Level is the nesting depth of the scope. Within each scope,
 *    every variable declaration creates its own "sub-level". This is done to enable the debugger to hide a variable until the
 *    code runs past its declaration point. The first variable in the scope has sub-level 1.
 * C) If a variable got eleminated by optimization, this can be indicated with an empty set of registers like so:
 *    S:Lsnake.main$i$1_0$109({1}SC:U),R,0,0,[] (Read: Local variable `i` in `main()` of type `unsigned char` is in no register.)
 *    Emulicious will display it as: "i: Eliminated by Optimization"
 * D) Enums don't have a representation. They are lowered to their underlying type.
 * 
 * In addition we define our own extensions to the format to allow local variables to always be shown in their correct scopes:
 * - V:<software>$<version>
 *   At the start of the file, this informs a consumer of the software used to write the .cdb. Software is the name of the program,
 *   e.g. "wiz", and version is a free-form string, but ideally just "1.5.2" or similar.
 * - N:<blocknum>$<parent>
 *   For every nested block of a function (identified by a sequential number) this establishes its parent. Top level function blocks
 *   will have the global, reserved parent "0". The scope of a simple `main()`-function might be given as "N:1$0". While in theory
 *   it's not necessary to explicitly state that a block has the "0" parent, in some programs that could mean that no "N:" line is
 *   written at all and a parser might be looking for such a line to switch to the new scheme of establishing nested blocks.
 */
namespace wiz {
    namespace {
        /// <summary> The dialect decides how local labels are prefixed. Emulicious will neatly put those away in a folder under the name of the parent function.
        /// While WLA-DX also supports sub-children, for this to be useful we'd have to emit a parent label before every code block and Emulicious for
        /// one is known to discards code labels that are never referenced.</summary>
        enum LabelDialect { RGBDS, WLADX };
        
        /// <summary>When re-writing namespaceTree as structs, we place the variable representing the namespace at this offset, hidden away outside of the ROM area.
        /// Any base address larger than the largest ROM should be fine. We'll use 1 GiB, the largest power of 2 that fits in an `int`. Emulicious internally
        /// recalculates addresses with their lower 16-bits less than 0xC000, so we add that on top to arrive at `0x4000C000`.</summary>
        const std::uint32_t NAMESPACE_OFFSET = 0x4000C000;
        /// This will be prefixed to the namespace struct names to make them stand out more. (It's a cardboard package.)
        const StringView NAMESPACE_ICON = u8"\U0001F4E6 "_sv;
        /// When `true`, this will add the contents of parent namespaceTree to a functions local variables list.
        const bool NAMESPACE_AS_LOCALS = true;
        /// The label dialect to be used when writing local labels.
        const LabelDialect LABEL_DIALECT = LabelDialect::WLADX;

        bool isSnesRelatedFormat(DebugFormatContext& context) {
            return context.outputContext->formatName == "sfc"_sv
                || context.outputContext->formatName == "smc"_sv;
        }

        bool isDebugLabelOutputRelative(const Definition* definition, const Address& address) {
            switch (definition->kind) {
                case DefinitionKind::Func:
                    return true;
                case DefinitionKind::Var:
                    return address.absolutePosition.hasValue() && ((definition->var.qualifiers & Qualifiers::Const) != Qualifiers::None);
                default: std::abort();
            }
        }

        std::string replaceNonAlphaNumerics(StringView text) {
            auto tmp = text.toString();
            for (std::size_t i = 0; i < tmp.length(); i++) {
                if (!isalnum(tmp[i])) {
                    tmp[i] = '_';
                }
            }
            return tmp;
        }

        struct Namespace {
            std::map<std::string, UniquePtr<Namespace>> namespaces;
            std::vector<const Definition*> memberVars;
        };

        // Keeps track of state specific to writing CDB symbol files.
        class CdbWriter {
            public:
                CdbWriter(DebugFormatContext& context, Writer* writer, StringView debugName)
                : context(context), writer(writer) {
                    // Source files will be referenced relative to the location of the .cdb file.
                    cdbPath = path::toNormalizedAbsolute(path::getDirectory(StringView(debugName)));
                    cdbPath += '/';
                    snes = isSnesRelatedFormat(context);
                }

                ~CdbWriter() {
                    free(buffer);
                }

                /// <summary>Version information is not part of the original CDB format, but it can be useful for debuggers to be able
                /// to adjust their parsing depending on the authoring software. If used, this should be the first line in a .cdb and
                /// the format is simply `V:&lt;software name&gt;$&lt;version string&gt;`. The version string is free form.</summary>
                void dumpVersion() {
                    // Stop at space, in case the version is followed by a qualifier like " (alpha)".
                    const auto spacePos = std::strchr(version::Text, ' ');
                    *this << "V:wiz$"_sv << StringView(version::Text, spacePos ? spacePos - version::Text : strlen(version::Text));
                    commitBuffer();
                }

                void dumpAndSetModuleName(StringView filePath) {
                    moduleName = replaceNonAlphaNumerics(path::stripExtension(path::getFilename(filePath)));
                    *this << "M:"_sv << moduleName;
                    commitBuffer();
                }

                void dumpDefinitions(const std::vector<const Definition*>& definitions) {
                    // Find each function's top level scope.
                    for (const auto definition : definitions) {
                        if (definition->kind == DefinitionKind::Func && definition->func.environment != nullptr) {
                            functionScopes.insert(std::pair(definition->func.environment, definition));
                        }
                    }

                    // Write out all relevant definitions (`var`s with bank relative address and `func`s).
                    for (const auto definition : definitions) {
                        switch (definition->kind) {
                            case DefinitionKind::Func: {
                                if (!definition->func.address.hasValue())
                                    continue;

                                getAndDumpScopeInfo(definition->parentScope);
        
                                // L:G$main$0$0:1209                            : standard linker address
                                writeLinkerRecord(definition, definition->func.address->absolutePosition.get(), false);

                                const auto isLabel = definition->func.body == nullptr;
                                if (!isLabel) {
                                    // S:G$main$0_0$0({2}DF,SV:S),C,0,0             : standard symbol type definition
                                    const std::size_t ptrSize = definition->func.far ? 3 : 2;
                                    writeSymbolRecord(definition, definition->func.resolvedSignatureType.get(), false, false, ptrSize);
                                    commitBuffer(false);

                                    // F:G$main$0_0$0({2}DF,SV:S),C,0,0,0,0,0       : same with 3 additional parameters for IRQs (not implemented here)
                                    buffer[0] = 'F';
                                    *this << ",0,0,0"_sv;
                                    commitBuffer();

                                    // L:XG$main$0$0:13A3                           : linker end address
                                    writeLinkerRecord(definition, definition->func.lastCodeNode->code.address.absolutePosition.get(), true);
                                }
                                break;
                            }
                            case DefinitionKind::Let: {
                                // Compile-time constants are not supported by CDB.
                                break;
                            }
                            case DefinitionKind::Namespace: {
                                // Handled on the fly when writing other symbols.
                                break;
                            }
                            case DefinitionKind::Struct: {
                                getAndDumpScopeInfo(definition->parentScope);
        
                                *this << "T:F"_sv << moduleName << '$';
                                writeNamespacePrefix();
                                *this << definition->name << '[';

                                for (std::size_t i = 0; i < definition->struct_.members.size(); i++) {
                                    const auto& member = definition->struct_.members[i]->structMember;
                                    const auto offset = member.offset.get();
                                    std::size_t size = getSizeForType(member.resolvedType.get());
                                    *this << "({"_sv << offset << '}';
                                    writeSymbolRecord(definition->struct_.members[i], member.resolvedType.get(), true, false, size);
                                    *this << ')';
                                }

                                *this << ']';
                                commitBuffer();
                                break;
                            }
                            case DefinitionKind::StructMember: {
                                // Handled above.
                                break;
                            }
                            case DefinitionKind::Var: {
                                std::size_t linkerAddress, size;
                                const Definition* registers;
                                if (getLinkerAddressAndSize(definition, linkerAddress, size, registers)) {
                                    // Don't write variables defined in inline functions. We are only interested in their duplicates at the actual inline site.
                                    if (definition->var.enclosingFunction && definition->var.enclosingFunction->func.inlined && !definition->var.enclosingFunction->func.stackFrame) {
                                        break;
                                    }

                                    // Finally, intercept global variables in namespaceTree, because we'll put them in magic structs.
                                    if (!definition->var.enclosingFunction) {
                                        const auto namespaceName = getNamespace(definition->parentScope);
                                        if (namespaceName.getLength() > 0) {
                                            const auto namespaceParts = text::split(StringView(namespaceName), "."_sv);
                                            auto currentNamespaces = &namespaceTree;
                                            Namespace* namespace_ = nullptr;
                                            for (const auto& name : namespaceParts) {
                                                const auto nameStr = name.toString();
                                                const auto finding = currentNamespaces->find(nameStr);
                                                if (finding == currentNamespaces->end()) {
                                                    namespace_ = ((*currentNamespaces)[nameStr] = makeUnique<Namespace>()).get();
                                                    nonEmptyNamespaces.insert(namespaceName);
                                                } else {
                                                    namespace_ = finding->second.get();
                                                }
                                                currentNamespaces = &namespace_->namespaces;
                                            }
                                            if (namespace_) {
                                                namespace_->memberVars.push_back(definition);
                                            }
                                            break;
                                        }
                                    }

                                    getAndDumpScopeInfo(definition->parentScope);
                                    writeSymbolRecord(definition, definition->var.resolvedType, false, registers, size);

                                    // For register storage append the decomposed register names.
                                    if (registers) {
                                        *this << ",["_sv;
                                        const auto decomposition = context.compiler->getBuiltins().findRegisterDecomposition(registers);
                                        if (decomposition.getLength() > 0) {
                                            *this << decomposition[0]->name;
                                            for (std::size_t i = 1; i < decomposition.getLength(); i++) {
                                                *this << ',' << decomposition[i]->name;
                                            }
                                        } else {
                                            *this << registers->name;
                                        }
                                        *this << ']';
                                    }

                                    commitBuffer();

                                    // For direct memory storage, write a symbol linker record, so the debugger knows our variable's location.
                                    if (!registers) {
                                        writeLinkerRecord(definition, linkerAddress);
                                    }
                                }
                                break;
                            }
                            case DefinitionKind::Bank:
                            case DefinitionKind::Enum:
                            case DefinitionKind::EnumMember:
                            case DefinitionKind::TypeAlias:
                                // Nothing to do for these.
                                break;
                            default: std::abort();
                        }
                    }
                }

                // Re-writes namespaceTree as structs to be able to access them as nested global variables.
                void dumpNamespaces() {
                    for (const auto& namespace_ : namespaceTree) {
                        dumpNamespace(namespace_.second.get(), StringView(namespace_.first));
                        *this << "S:G$"_sv << namespace_.first << "$0_0$0({0}ST"_sv << NAMESPACE_ICON << namespace_.first << ":S),Z,0,0"_sv;
                        commitBuffer();
                        useHex = true;
                        *this << "L:G$"_sv << namespace_.first << "$0$0:"_sv << NAMESPACE_OFFSET;
                        commitBuffer();
                    }

                    if (NAMESPACE_AS_LOCALS) {
                        std::vector<const Definition*> definitions;
                        std::map<StringView, const Definition*> namesToDefinitions;
                        for (const auto& functionScope : functionScopes) {
                            const auto scope = functionScope.first;
                            getAndDumpScopeInfo(scope);
                            for (auto currentScope = scope->getParent(); ; currentScope = currentScope->getParent()) {
                                bool isInNamespace = false;
                                for (auto parentScope = currentScope; parentScope; parentScope = parentScope->getParent()) {
                                    const auto namespaceName = parentScope->getFullName();
                                    if (namespaceName.length() > 0 && namespaceName[0] != '%') {
                                        isInNamespace = true;
                                        break;
                                    }
                                }
                                if (!isInNamespace) {
                                    break;
                                }
                                currentScope->getDefinitions(definitions);
                            }
                            for (auto it = definitions.rbegin(); it != definitions.rend(); it++) {
                                namesToDefinitions[(*it)->name] = *it;
                            }

                            for (const auto& nameToDefinition : namesToDefinitions) {
                                if (nameToDefinition.second->kind == DefinitionKind::Var && (nameToDefinition.second->var.qualifiers & Qualifiers::Extern) == Qualifiers::None) {
                                    std::size_t linkerAddress, size;
                                    const Definition* registers;
                                    getLinkerAddressAndSize(nameToDefinition.second, linkerAddress, size, registers);
                                    writeSymbolRecord(nameToDefinition.second, nameToDefinition.second->var.resolvedType, false, registers, size);
                                    commitBuffer();
                                    writeLinkerRecord(nameToDefinition.second, linkerAddress, false);
                                }
                            }

                            for (const auto& nameToDefinition : namesToDefinitions) {
                                if (nameToDefinition.second->kind == DefinitionKind::Namespace) {
                                    const auto namespaceName = nameToDefinition.second->namespace_.environment->getFullName();
                                    if (nonEmptyNamespaces.find(StringView(namespaceName)) != nonEmptyNamespaces.end()) {
                                        *this << "S:"_sv;
                                        writeLocalSymbol(nameToDefinition.second);
                                        *this << "({0}ST"_sv << NAMESPACE_ICON << namespaceName << ":S),Z,0,0"_sv;
                                        commitBuffer();
                                        writeLinkerRecord(nameToDefinition.second, NAMESPACE_OFFSET, false);
                                    }
                                }
                            }

                            definitions.clear();
                            namesToDefinitions.clear();
                        }
                    }
                }

                // Write additional local labels that have distinct addresses from the above.
                void dumpLocalLabels(const std::vector<const Definition*>& definitions) {
                    for (const auto definition : definitions) {
                        if (definition->kind == DefinitionKind::Func && definition->func.address.hasValue() && !definition->func.body) {
                            getAndDumpScopeInfo(definition->parentScope);
                            writeLinkerRecord(definition, definition->func.address->absolutePosition.get(), false);
                        }
                    }
                }

                void dumpSourceLines() {
                    const auto irNodes = context.compiler->getCodeIrNodes();
                    StringView lastLocation = StringView(nullptr, 0), path;
                    for (const auto irNode : irNodes) {
                        if (lastLocation.getData() != irNode->location.canonicalPath.getData()) {
                            path = getRelativeFilePath(lastLocation = irNode->location.canonicalPath);
                        }
                        if (path.getLength() > 0) {
                            getAndDumpScopeInfo(irNode->code.scope);
                            *this << "L:C$"_sv << path << '$' << irNode->location.line;
                            *this << '$' << irNode->code.scope->getDebugNestingLevel() << "_0$"_sv << irNode->code.scope->getDebugBlockId() << ':';
                            useHex = true;
                            *this << irNode->code.address.absolutePosition.get();
                            commitBuffer();
                        }
                    }
                }

            private:
                DebugFormatContext& context;
                Writer* writer;
                bool snes;                                                          // Caches whether we are writing to a SNES file type.
                std::string moduleName;                                             // File name without .wiz extension and with non-alphanumerics replaced.
                std::unordered_map<StringView, StringView> relativeFilePaths;       // Cache of .wiz file names relative to this .cdb.
                std::string cdbPath;                                                // Directory path of this .cdb that the above are based on.
                StringView namespaceName;                                           // Current namespace including function names.
                const Definition* currentStackFrame = nullptr;                      // Current function we are inside of.
                char* buffer = nullptr;                                             // Line buffer.
                std::size_t bufferLen = 0;                                          // Size of line buffer.
                std::size_t lineLen = 0;                                            // Used chars of line buffer.
                bool useHex = false;                                                // Whether to encode the next integer as hex.
                bool lineHasErrors = false;                                         // Some definition couldn't be represented and the buffer should not be written.
                char convBuffer[20];                                                // Unsigned integer conversion buffer up to 64-bit.
                std::unordered_map<const SymbolTable*, const Definition*> functionScopes; // Reverse lookup from a scope to a function definition.
                std::unordered_map<const SymbolTable*, std::pair<StringView, const Definition*>> scopeInfo; // Cache for next higher function definition and namespace of a scope.
                std::vector<unsigned int> writtenBlockNestings;                     // Remembers which "N:<blockId>$<parentBlockId>" pairs have already been written.
                std::map<std::string, UniquePtr<Namespace>> namespaceTree;          // List of namespaceTree found while going through definitions for use in namespace to struct conversion.
                std::set<StringView> nonEmptyNamespaces;                            // For "namespaces as local variable" feature.

                /// <summary>Retrieve the namespace string for a definition skipping anonymous blocks.</summary>
                /// <param name="definition">Definition to return the namespace of.</param>
                /// <returns>The fully qualified namespace for the given definition.</returns>
                StringView getNamespace(const SymbolTable* scope) {
                    for (auto currentScope = scope; currentScope; currentScope = currentScope->getParent()) {
                        const auto fullName = currentScope->getFullName();
                        if (fullName.size() > 0 && fullName[0] != '%') {
                            return context.stringPool->intern(fullName);
                        }
                    }
                    return ""_sv;
                }

                void reserveBuffer(std::size_t size) {
                    auto total = lineLen + size + text::OsNewLine.getLength();
                    if (bufferLen < total) {
                        total += 10;
                        char* bufferNew = reinterpret_cast<char*>(realloc(buffer, total));
                        if (bufferNew == nullptr) {
                            context.report->error("out of memory", SourceLocation(), ReportErrorFlags::Fatal);
                            std::abort();
                        }
                        buffer = bufferNew;
                        bufferLen = total;
                    }
                }

                void appendToBuffer(const char* src, const std::size_t len) {
                    reserveBuffer(len);
                    memcpy(&buffer[lineLen], src, len);
                    lineLen += len;
                }

                CdbWriter& operator <<(const StringView sv) {
                    appendToBuffer(sv.getData(), sv.getLength());
                    return *this;
                }

                CdbWriter& operator <<(const std::string& text) {
                    appendToBuffer(text.data(), text.length());
                    return *this;
                }

                CdbWriter& operator <<(const char c) {
                    reserveBuffer(1);
                    buffer[lineLen++] = c;
                    return *this;
                }

                template <typename T>
                CdbWriter& operator <<(T v) {
                    return *this << static_cast<std::size_t>(v);
                }

                CdbWriter& operator <<(std::size_t v) {
                    if (!v) {
                        *this << '0';
                    } else {
                        auto ptr = reinterpret_cast<char*>(&convBuffer + 1), end = ptr;
                        if (!useHex) {
                            do {
                                *--ptr = v % 10 + '0';
                                v /= 10;
                            } while (v);
                        } else {
                            do {
                                *--ptr = (v % 16 < 10) ? v % 16 + '0' : v % 16 + ('A' - 10);
                                v /= 16;
                            } while (v);
                            useHex = false;
                        }
                        appendToBuffer(ptr, end - ptr);
                    }
                    return *this;
                }

                void commitBuffer(bool clear = true) {
                    if (!lineHasErrors) {
                        memcpy(&buffer[lineLen], text::OsNewLine.getData(), text::OsNewLine.getLength());
                        writer->write(StringView(buffer, lineLen + text::OsNewLine.getLength()));
                    }
                    if (clear) {
                        lineLen = 0;
                        lineHasErrors = false;
                    }
                }

                void writeNamespacePrefix() {
                    if (namespaceName.getLength() > 0) {
                        *this << namespaceName << '.';
                    }
                }

                void writeNameLevelAndBlock(const Definition* definition, bool writeSubLevel) {
                    if (definition->name.getLength() >= 1 && definition->name[0] == '$') {
                        // Turn this into a nested label for the previously defined function.
                        writeLocalLabelPrefix();
                        *this << definition->name.sub(1);
                    } else {
                        *this << definition->name;
                    }
                    *this << '$' << (definition->parentScope ? definition->parentScope->getDebugNestingLevel() : 0);
                    if (writeSubLevel) {
                        *this << "_0"_sv;
                    }
                    *this << '$' << (definition->parentScope ? definition->parentScope->getDebugBlockId() : 0);
                }

                void writeLocalSymbol(const Definition* definition) {
                    *this << 'L' << moduleName << '.' << namespaceName << '$';
                    writeNameLevelAndBlock(definition, true);
                }

                void writeTypeChain(const TypeExpression* typeExpression) {
                    switch (typeExpression->kind) {
                        case TypeExpressionKind::Array: {
                            *this << "DA"_sv << typeExpression->array.size->integerLiteral.value.toString() << "d,"_sv;
                            writeTypeChain(typeExpression->array.elementType.get());
                            break;
                        }
                        case TypeExpressionKind::DesignatedStorage: {
                            writeTypeChain(typeExpression->designatedStorage.elementType.get());
                            break;
                        }
                        case TypeExpressionKind::Function: {
                            *this << "DF,"_sv;
                            writeTypeChain(typeExpression->function.returnType.get());
                            break;
                        }
                        case TypeExpressionKind::Pointer: {
                            /* Pointer types in SDCC:
                             *     | Constant   | C++                        | Description
                             *  DG | GPOINTER   | n/a                        | generic
                             *  DD | POINTER    | __data / __near  (default) | internal ram / near data
                             *  DX | FPOINTER   | __xdata / __far            | external ram / far data
                             *  DI | IPOINTER   | __idata                    | upper 128 bytes
                             *  DP | PPOINTER   | __pdata                    | paged area
                             *  DC | CPOINTER   | __code                     | code space
                             *  DA | EEPPOINTER | n/a                        | EEPROM
                             */
                            bool isFar = (typeExpression->pointer.qualifiers & Qualifiers::Far) != Qualifiers::None;
                            *this << (isFar ? "DX,"_sv : "DG,"_sv);
                            writeTypeChain(typeExpression->pointer.elementType.get());
                            break;
                        }
                        case TypeExpressionKind::ResolvedIdentifier: {
                            const auto identifierDefinition = typeExpression->resolvedIdentifier.definition;
                            switch (identifierDefinition->kind) {
                                case DefinitionKind::BuiltinBoolType: {
                                    *this << "SC:U"_sv;
                                    break;
                                }
                                case DefinitionKind::BuiltinIntegerType: {
                                    auto size = identifierDefinition->builtinIntegerType.size;

                                    if (size <= 4) {
                                        *this << (size <= 1 ? "SC:"_sv : size <= 2 ? "SS:"_sv : "SL:"_sv);
                                        *this << (identifierDefinition->builtinIntegerType.min.isNegative() ? 'S' : 'U');
                                    } else {
                                        context.report->error("cdb: cannot represent integer of size " + std::to_string(size) + " (max is 32-bit)", typeExpression->location);
                                        lineHasErrors = true;
                                    }
                                    break;
                                }
                                case DefinitionKind::Enum: {
                                    writeTypeChain(identifierDefinition->enum_.resolvedUnderlyingType.get());
                                    break;
                                }
                                case DefinitionKind::Struct: {
                                    const auto oldNamespace = namespaceName;
                                    const auto onExit = makeScopeGuard([&]() {
                                        namespaceName = oldNamespace;
                                    });
                                    namespaceName = getNamespace(identifierDefinition->parentScope);

                                    *this << "ST"_sv;
                                    writeNamespacePrefix();
                                    *this << identifierDefinition->name << ":S"_sv;
                                    break;
                                }
                                default: std::abort();
                            }
                            break;
                        }
                        case TypeExpressionKind::Tuple: {
                            if (typeExpression->tuple.elementTypes.size() == 0) { // void
                                *this << "SV:S"_sv;
                            } else {
                                context.report->error("cdb: tuples are not supported", typeExpression->location);
                                lineHasErrors = true;
                            }
                            break;
                        }
                        default: std::abort();
                    }
                }

                // Used to write type information for var and func definitions as well as struct members.
                void writeSymbolRecord(const Definition* definition, const TypeExpression* typeExpression, const bool isStruct, const bool isInRegisters, const std::size_t size) {
                    auto address = definition->getAddress();
                    auto qualifiers = Qualifiers::None;
                    
                    if (definition->kind == DefinitionKind::Var) {
                        if (definition->var.resolvedType->kind == TypeExpressionKind::DesignatedStorage) {
                            address = definition->var.resolvedType->designatedStorage.holder->resolvedIdentifier.definition->getAddress();
                        }
                        qualifiers = definition->var.qualifiers;
                    }

                    *this << "S:"_sv;
                    if (isStruct) {
                        *this << "S$"_sv;
                        writeNameLevelAndBlock(definition, true);
                    } else if (currentStackFrame == nullptr) {
                        *this << "G$"_sv;
                        writeNamespacePrefix();
                        writeNameLevelAndBlock(definition, true);
                    } else {
                        writeLocalSymbol(definition);
                    }
                    
                    *this << "({"_sv << size << '}';
                    writeTypeChain(typeExpression);
                    *this << ')';

                    if (isStruct) {
                        *this << ",Z"_sv; // Unspecified
                    } else if (isInRegisters) {
                        *this << ",R"_sv; // Register storage
                    } else if (address.hasValue()) {
                        if (address->bank != nullptr) {
                            switch (address->bank->getKind()) {
                                case BankKind::UninitializedRam:
                                case BankKind::InitializedRam:
                                    *this << ",F"_sv;
                                    break;
                                case BankKind::ProgramRom:
                                    *this << ",C"_sv;
                                    break;
                                case BankKind::CharacterRom:
                                case BankKind::DataRom:
                                    *this << ",D"_sv;
                                    break;
                                default: std::abort();
                            }
                        } else if ((qualifiers & Qualifiers::Extern) != Qualifiers::None) {
                            *this << ",I"_sv; // Memory Mapped I/O Register
                        } else {
                            *this << ",Z"_sv; // Absolute memory address with no bank
                        }
                    } else std::abort();
                    *this << ",0,0"_sv;
                }

                void writeLocalLabelPrefix() {
                    *this << (LABEL_DIALECT == LabelDialect::RGBDS ? '.' : '@');
                }

                void writeLinkerRecord(const Definition* definition, const std::size_t linkerAddress, bool isEndRecord = false) {
                    // We only write local labels if they don't coincide with a function start address to avoid confusion in disassemblys.
                    if (definition->kind != DefinitionKind::Func || definition->func.body || context.addressOwnership.find(linkerAddress) == context.addressOwnership.end())
                    {
                        if (!isEndRecord) {
                            context.addressOwnership[linkerAddress] = definition;
                        }

                        *this << "L:"_sv;
                        if (currentStackFrame == nullptr || definition->kind == DefinitionKind::Func) {
                            *this << (isEndRecord ? "XG$"_sv : "G$"_sv);
                            if (currentStackFrame) {
                                writeLocalLabelPrefix();
                            } else {
                                writeNamespacePrefix();
                            }
                            writeNameLevelAndBlock(definition, false);
                        } else {
                            *this << (isEndRecord ? "X"_sv : ""_sv);
                            writeLocalSymbol(definition);
                        }
                        useHex = true;
                        *this << ':' << linkerAddress;
                        commitBuffer();
                    }
                }

                const StringView getRelativeFilePath(const StringView canonicalPath) {
                    const auto result = relativeFilePaths.find(canonicalPath);
                    if (result != relativeFilePaths.end()) {
                        return result->second;
                    } else {
                        auto path = path::toRelative(canonicalPath, StringView(cdbPath));
                        if (path != "") {
                            for (const char& c : path) {
                                if (c == '$') {
                                    context.report->error("cdb: no source level debugging for relative file path containing dollar sign(s): `" + path + "`", SourceLocation(canonicalPath));
                                    path = "";
                                    break;
                                }
                            }
                        } else {
                            // The paths have no common root.
                            context.report->error("cdb: no source level debugging for source files on a different drive", SourceLocation(canonicalPath));
                        }
                        return relativeFilePaths[canonicalPath] = context.stringPool->intern(path);
                    }
                }

                void getAndDumpScopeInfo(const SymbolTable* scope) {
                    const auto findings = scopeInfo.find(scope);
                    if (findings != scopeInfo.end()) {
                        namespaceName = findings->second.first;
                        currentStackFrame = findings->second.second;
                    } else {
                        namespaceName = ""_sv;
                        currentStackFrame = nullptr;
                        for (auto currentScope = scope; currentScope != nullptr; currentScope = currentScope->getParent()) {
                            // As an extension to the .cdb format, we write block nesting information so local variables show up in the right scopes.
                            if (writtenBlockNestings.size() <= currentScope->getDebugBlockId()) {
                                writtenBlockNestings.resize(currentScope->getDebugBlockId() + 1);
                            }
                            if (!writtenBlockNestings[currentScope->getDebugBlockId()]) {
                                writtenBlockNestings[currentScope->getDebugBlockId()] = true;
                                if (currentScope->getDebugBlockId()) {
                                    *this << "N:"_sv << currentScope->getDebugBlockId() << '$' << currentScope->getParent()->getDebugBlockId();
                                    commitBuffer();
                                }
                            }

                            // Retrieve or establish in which stack frame as seen by a debugger this definition is relevant.
                            auto scopeAndFunction = functionScopes.find(currentScope);
                            if (scopeAndFunction != functionScopes.end()) {
                                if (scopeAndFunction->second->func.stackFrame) {
                                    // In this case we are dealing with an inlined function and the stack frame is that of the host function.
                                    currentStackFrame = scopeAndFunction->second->func.stackFrame;
                                } else {
                                    currentStackFrame = scopeAndFunction->second;
                                }
                                namespaceName = getNamespace(currentStackFrame->parentScope);
                                if (namespaceName.getLength() > 0) {
                                    namespaceName = context.stringPool->intern(namespaceName.toString() + '.' + currentStackFrame->name.toString());
                                } else {
                                    namespaceName = currentStackFrame->name;
                                }
                            }
                        }
                        if (currentStackFrame == nullptr && scope != nullptr) {
                            namespaceName = getNamespace(scope);
                        }
                        scopeInfo.insert(std::pair(scope, std::pair(namespaceName, currentStackFrame)));
                    }
                }

                std::size_t getSizeForType(const TypeExpression* typeExpression) {
                    switch (typeExpression->kind) {
                        case TypeExpressionKind::Array: {
                            // Array sizes are always compile time integer literals.
                            return static_cast<std::size_t>(typeExpression->array.size->integerLiteral.value) * getSizeForType(typeExpression->array.elementType.get());
                        }
                        case TypeExpressionKind::DesignatedStorage: {
                            return getSizeForType(typeExpression->designatedStorage.elementType.get());
                        }
                        case TypeExpressionKind::Function: {
                            return typeExpression->function.far ? 3 : 2;
                        }
                        case TypeExpressionKind::Pointer: {
                            return ((typeExpression->pointer.qualifiers & Qualifiers::Far) != Qualifiers::None) ? 3 : 2;
                        }
                        case TypeExpressionKind::ResolvedIdentifier: {
                            const auto definition = typeExpression->resolvedIdentifier.definition;
                            switch (definition->kind) {
                                case DefinitionKind::BuiltinBoolType: return 1;
                                case DefinitionKind::BuiltinIntegerType: return definition->builtinIntegerType.size;
                                case DefinitionKind::Enum: return getSizeForType(definition->enum_.resolvedUnderlyingType.get());
                                case DefinitionKind::Func: return definition->func.far ? 3 : 2;
                                case DefinitionKind::Struct: return definition->struct_.size.get();
                                default: std::abort();
                            }
                        }
                        default: std::abort();
                    }
                }

                bool getLinkerAddressAndSize(const Definition* definition, std::size_t& linkerAddress, std::size_t& size, const Definition*& registers, Optional<Address> address = Optional<Address>()) {
                    const auto& var = definition->var;

                    switch (var.resolvedType->kind) {
                        case TypeExpressionKind::Array:
                        case TypeExpressionKind::Function:
                        case TypeExpressionKind::Pointer:
                        case TypeExpressionKind::ResolvedIdentifier: {
                            if (!address.hasValue()) {
                                address = var.address;
                            }
                            registers = nullptr;
                            break;
                        }
                        case TypeExpressionKind::DesignatedStorage: {
                            assert(!var.address.hasValue());
                            const auto holder = var.resolvedType->designatedStorage.holder->resolvedIdentifier.definition;
                            switch (holder->kind) {
                                case DefinitionKind::Var: {
                                    return getLinkerAddressAndSize(holder, linkerAddress, size, registers, address);
                                }
                                case DefinitionKind::BuiltinRegister: {
                                    registers = holder;
                                    break;
                                }
                                default: std::abort(); 
                            }
                            break;
                        }
                        default: std::abort();
                    }

                    size = getSizeForType(var.resolvedType);

                    if (registers) {
                        linkerAddress = 0;
                    } else if (!address->absolutePosition.hasValue() || !address->relativePosition.hasValue() || (definition->var.qualifiers & Qualifiers::Extern) != Qualifiers::None) {
                        // Ignore hardware registers / 'extern'.
                        // If these are mapper-related, definitions for different mappers might alias each other.
                        // Also, mapper-related registers might alias code/data in the ROM area of address space.
                        return false;
                    } else if (!snes && isDebugLabelOutputRelative(definition, address.get())) {
                        const auto offset = context.outputContext->getOutputOffset(address.get());
                        if (offset.hasValue()) {
                            linkerAddress = std::max<std::size_t>(offset.get() - context.outputContext->fileHeaderPrefixSize, 0);
                        } else std::abort();
                    } else {
                        linkerAddress = address->absolutePosition.get();
                    }
                    return true;
                }

                void dumpNamespace(const Namespace* namespace_, StringView namespaceName) {
                    *this << "T:F"_sv << moduleName << '$' << NAMESPACE_ICON << namespaceName << '[';

                    for (std::size_t i = 0; i < namespace_->memberVars.size(); i++) {
                        const auto member = namespace_->memberVars[i];
                        std::size_t linkerAddress, size;
                        const Definition* registers;
                        if (getLinkerAddressAndSize(member, linkerAddress, size, registers)) {
                            const auto offset = NAMESPACE_OFFSET - linkerAddress;
                            *this << "({-"_sv << offset << '}';
                            writeSymbolRecord(member, member->var.resolvedType, true, false, size);
                            *this << ')';
                        }
                    }

                    for (const auto& subNamespace : namespace_->namespaces) {
                        *this << "({0}S:S$"_sv << subNamespace.first << "$0_0$0({0}ST"_sv << NAMESPACE_ICON << namespaceName << '.' << subNamespace.first << ":S),Z,0,0)"_sv;
                    }

                    *this << ']';
                    commitBuffer();

                    for (const auto& subNamespace : namespace_->namespaces) {
                        dumpNamespace(subNamespace.second.get(), StringView(namespaceName.toString() + '.' + subNamespace.first));
                    }
                }
        };
    }

    CdbSymDebugFormat::CdbSymDebugFormat() {}
    CdbSymDebugFormat::~CdbSymDebugFormat() {}

    bool CdbSymDebugFormat::generate(DebugFormatContext& context) {
        const auto debugName = path::stripExtension(context.outputName).toString() + ".cdb";

        if (auto writer = context.resourceManager->openWriter(StringView(debugName))) {
            CdbWriter cdbWriter(context, writer.get(), StringView(debugName));
                const auto definitions = context.compiler->getRegisteredDefinitions();
                cdbWriter.dumpVersion();
                cdbWriter.dumpAndSetModuleName(context.outputName);
                cdbWriter.dumpDefinitions(definitions);
                cdbWriter.dumpNamespaces();
                cdbWriter.dumpLocalLabels(definitions);
                cdbWriter.dumpSourceLines();
        }

        return true;
    }
}