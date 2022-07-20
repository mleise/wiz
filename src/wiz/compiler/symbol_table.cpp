#include <cstdio>
#include <limits>
#include <algorithm>
#include <wiz/ast/statement.h>
#include <wiz/utility/report.h>
#include <wiz/compiler/definition.h>
#include <wiz/compiler/symbol_table.h>

namespace wiz {
    std::string SymbolTable::generateBlockName() {
        static unsigned int blockIndex = 0;
        char buffer[std::numeric_limits<unsigned int>::digits10 + 5] = {0};
        std::sprintf(buffer, "%%blk%u", blockIndex++);
        return std::string(buffer);
    }

    SymbolTable::SymbolTable()
    : parent(nullptr) {}

    SymbolTable::SymbolTable(
        SymbolTable* parent,
        StringView namespaceName)
    : parent(parent),
    namespaceName(namespaceName) {}

    SymbolTable::~SymbolTable() {}

    SymbolTable* SymbolTable::getParent() const {
        return parent;
    }

    std::string SymbolTable::getFullName() const {
        if (!parent) {
            return namespaceName.toString();
        } else if (namespaceName.getLength() > 0) {
            if (namespaceName[0] == '%') {
                return namespaceName.toString();
            } else {
                std::string parentName = parent->getFullName();
                return (parentName.length() ? parentName + "." : "") + namespaceName.toString();
            }
        } else {
            return "";
        }
    }

    std::uint16_t SymbolTable::getDebugNestingLevel() const {
        return debugNestingLevel;
    }

    void SymbolTable::setDebugNestingLevel(const std::uint16_t level) {
        debugNestingLevel = level;
    }

    unsigned int SymbolTable::getDebugBlockId() const {
        return debugBlockId;
    }

    void SymbolTable::setDebugBlockId(unsigned int id) {
        debugBlockId = id;
    }

    void SymbolTable::printKeys(Report* report) const {
        for (const auto& item : namesToDefinitions) {
            const auto& decl = item.second->declaration;
            report->log(item.first.toString() + ": " + decl->getDescription().toString() + " (declared: " + decl->location.toString() + ")");
        }
    }

    void SymbolTable::getDefinitions(std::vector<Definition*>& results) const {
        results.reserve(results.size() + namesToDefinitions.size());
        for (const auto& it : namesToDefinitions) {
            results.push_back(it.second.get());
        }
    }

    void SymbolTable::getDefinitions(std::vector<const Definition*>& results) const {
        results.reserve(results.size() + namesToDefinitions.size());
        for (const auto& it : namesToDefinitions) {
            results.push_back(it.second.get());
        }
    }

    Definition* SymbolTable::addDefinition(Report* report, FwdUniquePtr<Definition> def) {
        const auto match = findLocalMemberDefinition(def->name);
        if (match != nullptr) {
            if (report) {
                report->error("redefinition of symbol `" + def->name.toString() + "`", def->declaration->location, ReportErrorFlags::Continued);
                report->error("`" + def->name.toString() + "` was previously defined here, by " + match->declaration->getDescription().toString(), match->declaration->location);
            }
            return nullptr;
        } else {
            def->parentScope = this;

            auto result = def.get();
            namesToDefinitions[def->name] = std::move(def);
            return result;
        }
    }

    bool SymbolTable::addImport(SymbolTable* import) {
        if (import == this) {
            return false;
        }
        if (std::find(imports.begin(), imports.end(), import) == imports.end()) {
            imports.push_back(import);
            return true;
        }
        return false;
    }

    bool SymbolTable::addRecursiveImport(SymbolTable* import) {
        if (addImport(import)) {
            for (const auto& it : namesToDefinitions) {
                const auto name = it.first;
                const auto& def = it.second;
                if (auto ns = def->tryGet<Definition::Namespace>()) {
                    if (const auto importedDef = import->findLocalMemberDefinition(name)) {
                        if (const auto importedNS = importedDef->tryGet<Definition::Namespace>()) {
                            ns->environment->addRecursiveImport(importedNS->environment);
                        }
                    }
                }
            }

            return true;
        }
        return false;
    }

    Definition* SymbolTable::findLocalMemberDefinition(StringView name) const {
        const auto match = namesToDefinitions.find(name);
        if (match != namesToDefinitions.end()) {
            return match->second.get();
        }
        return nullptr;
    }

    void SymbolTable::findImportedMemberDefinitions(StringView name, std::set<Definition*>& results) const {
        for (const auto import : imports) {
            if (const auto result = import->findLocalMemberDefinition(name)) {
                if (std::find(results.begin(), results.end(), result) == results.end()) {
                    results.insert(result);
                }
            }
        }
    }

    void SymbolTable::findMemberDefinitions(StringView name, std::set<Definition*>& results) const {
        findImportedMemberDefinitions(name, results);
        if (const auto result = findLocalMemberDefinition(name)) {
            if (std::find(results.begin(), results.end(), result) == results.end()) {
                results.insert(results.begin(), result);
            }
        }
    }

    void SymbolTable::findUnqualifiedDefinitions(StringView name, std::set<Definition*>& results) const {
        findMemberDefinitions(name, results);
        if (results.size() == 0 && parent != nullptr) {
            parent->findUnqualifiedDefinitions(name, results);
        }
    }
}

