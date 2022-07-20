#ifndef WIZ_FORMAT_DEBUG_DEBUG_FORMAT_H
#define WIZ_FORMAT_DEBUG_DEBUG_FORMAT_H

#include <memory>
#include <vector>
#include <unordered_map>

#include <wiz/utility/string_view.h>

namespace wiz {
    class Bank;
    class Config;
    class Report;
    class StringPool;
    class ResourceManager;
    class Compiler;
    struct Definition;
    struct OutputFormatContext;

    struct DebugFormatContext {
        DebugFormatContext(
            ResourceManager* resourceManager,
            Report* report,
            StringPool* stringPool,
            const Config* config,
            StringView formatName,
            StringView outputName,
            const OutputFormatContext* outputContext,
            const Compiler* compiler)
        : resourceManager(resourceManager),
        report(report),
        stringPool(stringPool),
        config(config),
        formatName(formatName),
        outputName(outputName),
        outputContext(outputContext),
        compiler(compiler) {}

        ResourceManager* resourceManager;
        Report* report;
        StringPool* stringPool;
        const Config* config;
        StringView formatName;
        StringView outputName;
        const OutputFormatContext* outputContext;
        const Compiler* compiler;

        std::unordered_map<std::size_t, const Definition*> addressOwnership;
    };    

    class DebugFormat {
        public:
            virtual ~DebugFormat() {}

            virtual bool generate(DebugFormatContext& context) = 0;
    };

    class DebugFormatCollection {
        public:
            DebugFormatCollection();
            ~DebugFormatCollection();

            std::size_t getFormatNameCount() const;
            StringView getFormatName(std::size_t index) const;

            void add(StringView name, std::unique_ptr<DebugFormat> format);
            DebugFormat* find(StringView name) const;

        private:
            std::vector<std::unique_ptr<DebugFormat>> formats;
            std::vector<StringView> formatNames;
            std::unordered_map<StringView, DebugFormat*> formatsByName;
    };

    // TODO: msl files (mesen-s smybol files)
    // TODO: sym files (bsnes-plus)
    // TODO: dbg files (mesen source mapping)
    // TODO: nl files (FCEUX)
    // TODO: investigate Mednafen, no$sns, no$gmb, MEKA, OpenMSX, and others for their formats.
}


#endif
