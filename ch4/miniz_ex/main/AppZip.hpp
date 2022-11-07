#pragma once

#include <cstring>

#include "esp_log.h"
#include "esp_heap_caps.h"
#include "mbedtls/base64.h"

#include "rom/miniz.h"

namespace app
{
    class AppZip
    {
    private:
        constexpr static const size_t DATASIZE{1024 * 64};
        char *m_data_buffer;
        char *m_compressed_buffer;
        char *m_decompressed_buffer;
        tdefl_compressor m_comp;
        tinfl_decompressor m_decomp;

    public:
        char *zip(const char *data, size_t *len)
        {
            tdefl_init(&m_comp, NULL, NULL, TDEFL_WRITE_ZLIB_HEADER | 1500);
            memset(m_data_buffer, 0, DATASIZE);
            memcpy(m_data_buffer, data, *len);

            size_t inbytes = 0, outbytes = 0, inpos = 0, outpos = 0;
            while (inbytes != DATASIZE)
            {
                outbytes = DATASIZE - outpos;
                inbytes = DATASIZE - inpos;
                tdefl_compress(&m_comp, &m_data_buffer[inpos], &inbytes, &m_compressed_buffer[outpos], &outbytes, TDEFL_FINISH);
                inpos += inbytes;
                outpos += outbytes;
            }
            *len = outpos;
            return m_compressed_buffer;
        }

        char *unzip(const char *data, size_t len)
        {
            tinfl_init(&m_decomp);
            if (data != m_compressed_buffer)
            {
                memset(m_compressed_buffer, 0, DATASIZE);
                memcpy(m_compressed_buffer, data, len);
            }
            size_t inbytes = 0, outbytes = 0, inpos = 0, outpos = 0;
            inpos = 0;
            outpos = 0;
            while (inbytes != len)
            {
                outbytes = DATASIZE - outpos;
                inbytes = len - inpos;
                tinfl_decompress(&m_decomp, (const mz_uint8 *)&m_compressed_buffer[inpos], &inbytes, (uint8_t *)m_decompressed_buffer, (mz_uint8 *)&m_decompressed_buffer[outpos], &outbytes, TINFL_FLAG_PARSE_ZLIB_HEADER);
                inpos += inbytes;
                outpos += outbytes;
                if (outbytes == 0)
                {
                    break;
                }
            }

            return m_decompressed_buffer;
        }

        void init(void)
        {
            m_data_buffer = (char *)heap_caps_malloc(DATASIZE, MALLOC_CAP_SPIRAM | MALLOC_CAP_8BIT);
            m_compressed_buffer = (char *)heap_caps_malloc(DATASIZE, MALLOC_CAP_SPIRAM | MALLOC_CAP_8BIT);
            m_decompressed_buffer = (char *)heap_caps_malloc(DATASIZE, MALLOC_CAP_SPIRAM | MALLOC_CAP_8BIT);
        }
    };
}