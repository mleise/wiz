#ifndef WIZ_FORMAT_DEBUG_CDB_SYM_DEBUG_FORMAT_H
#define WIZ_FORMAT_DEBUG_CDB_SYM_DEBUG_FORMAT_H

#include <wiz/format/debug/debug_format.h>

namespace wiz {
    class CdbSymDebugFormat : public DebugFormat {
        public:
            CdbSymDebugFormat();
            ~CdbSymDebugFormat() override;

            bool generate(DebugFormatContext& context) override;
    };
}

#endif
