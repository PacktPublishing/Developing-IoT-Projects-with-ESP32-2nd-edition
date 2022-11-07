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

        tdefl_compressor m_deflator;
        tinfl_decompressor m_inflator;

        const mz_uint s_tdefl_num_probes[11]{0, 1, 6, 32, 16, 32, 128, 256, 512, 768, 1500};

        const char *s_pStr = "Good morning Dr. Chandra. This is Hal. I am ready for my first lesson."
                             "Good morning Dr. Chandra. This is Hal. I am ready for my first lesson."
                             "Good morning Dr. Chandra. This is Hal. I am ready for my first lesson."
                             "Good morning Dr. Chandra. This is Hal. I am ready for my first lesson."
                             "Good morning Dr. Chandra. This is Hal. I am ready for my first lesson."
                             "Good morning Dr. Chandra. This is Hal. I am ready for my first lesson."
                             "Good morning Dr. Chandra. This is Hal. I am ready for my first lesson.";

    public:
        char *zip(const char *data, size_t *len)
        {
            tdefl_status status = tdefl_init(&m_deflator, NULL, NULL, TDEFL_WRITE_ZLIB_HEADER | 1500);
            assert(status == TDEFL_STATUS_OKAY);
            memset(m_data_buffer, 0, DATASIZE);
            memcpy(m_data_buffer, data, *len);

            size_t inbytes = 0, outbytes = 0, inpos = 0, outpos = 0;
            while (inbytes != DATASIZE)
            {
                outbytes = DATASIZE - outpos;
                inbytes = DATASIZE - inpos;
                tdefl_compress(&m_deflator, &m_data_buffer[inpos], &inbytes, &m_compressed_buffer[outpos], &outbytes, TDEFL_FINISH);
                printf("...Compressed %d into %d bytes\n", inbytes, outbytes);
                inpos += inbytes;
                outpos += outbytes;
            }
            *len = outpos;
            return m_compressed_buffer;
        }

        char *unzip(const char *data, size_t len)
        {
            tinfl_init(&m_inflator);
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
                tinfl_decompress(&m_inflator, (const mz_uint8 *)&m_compressed_buffer[inpos], &inbytes, (uint8_t *)m_decompressed_buffer, (mz_uint8 *)&m_decompressed_buffer[outpos], &outbytes, TINFL_FLAG_PARSE_ZLIB_HEADER);
                printf("...Decompressed %d into %d bytes\n", inbytes, outbytes);
                inpos += inbytes;
                outpos += outbytes;
                if (outbytes == 0)
                {
                    break;
                }
            }

            return m_decompressed_buffer;
        }

        void test(const char *data, size_t len)
        {
            int x;
            char b;
            char *inbuf, *outbuf;
            tdefl_compressor *comp;
            tinfl_decompressor *decomp;
            tdefl_status status;
            size_t inbytes = 0, outbytes = 0, inpos = 0, outpos = 0, compsz;
            printf("Allocating data buffer and filling it with semi-random data\n");
            inbuf = (char *)heap_caps_malloc(DATASIZE, MALLOC_CAP_SPIRAM | MALLOC_CAP_8BIT);
            assert(inbuf != NULL);
            // srand(0);
            // for (x = 0; x < DATASIZE; x++)
            // {
            //     inbuf[x] = (x & 1) ? rand() & 0xff : 0;
            // }
            sprintf(inbuf, "%s", s_pStr);
            printf("Allocating compressor & outbuf (%d bytes)\n", sizeof(tdefl_compressor));
            comp = (tdefl_compressor *)malloc(sizeof(tdefl_compressor));
            assert(comp != NULL);
            outbuf = (char *)heap_caps_malloc(DATASIZE, MALLOC_CAP_SPIRAM | MALLOC_CAP_8BIT);
            assert(outbuf != NULL);
            printf("Compressing...\n");
            status = tdefl_init(comp, NULL, NULL, TDEFL_WRITE_ZLIB_HEADER | 1500);
            assert(status == TDEFL_STATUS_OKAY);
            while (inbytes != DATASIZE)
            {
                outbytes = DATASIZE - outpos;
                inbytes = DATASIZE - inpos;
                tdefl_compress(comp, &inbuf[inpos], &inbytes, &outbuf[outpos], &outbytes, TDEFL_FINISH);
                printf("...Compressed %d into %d bytes\n", inbytes, outbytes);
                inpos += inbytes;
                outpos += outbytes;
            }
            compsz = outpos;
            free(comp);
            // Kill inbuffer
            for (x = 0; x < DATASIZE; x++)
            {
                inbuf[x] = 0;
            }
            free(inbuf);

            inbuf = outbuf;
            outbuf = (char *)heap_caps_malloc(DATASIZE, MALLOC_CAP_SPIRAM | MALLOC_CAP_8BIT);
            assert(outbuf != NULL);
            printf("Reinflating...\n");
            decomp = (tinfl_decompressor *)malloc(sizeof(tinfl_decompressor));
            assert(decomp != NULL);
            tinfl_init(decomp);
            inpos = 0;
            outpos = 0;
            while (inbytes != compsz)
            {
                outbytes = DATASIZE - outpos;
                inbytes = compsz - inpos;
                tinfl_decompress(decomp, (const mz_uint8 *)&inbuf[inpos], &inbytes, (uint8_t *)outbuf, (mz_uint8 *)&outbuf[outpos], &outbytes, TINFL_FLAG_PARSE_ZLIB_HEADER);
                printf("...Decompressed %d into %d bytes\n", inbytes, outbytes);
                inpos += inbytes;
                outpos += outbytes;
            }
            // printf("Checking if same...\n");
            // srand(0);
            // for (x = 0; x < DATASIZE; x++)
            // {
            //     b = (x & 1) ? rand() & 0xff : 0;
            //     if (outbuf[x] != b)
            //     {
            //         printf("Pos %x: %hhx!=%hhx\n", x, outbuf[x], b);
            //     }
            // }
            // printf("Great Success!\n");

            ESP_LOGI(__func__, "%.*s", strlen(s_pStr), outbuf);
            free(inbuf);
            free(outbuf);
            free(decomp);
        }

        void init(void)
        {
            // m_buffer = (char *)heap_caps_malloc(512 * 1024, MALLOC_CAP_SPIRAM | MALLOC_CAP_8BIT);
            // m_base64_buff = (char *)heap_caps_malloc(512 * 1024, MALLOC_CAP_SPIRAM | MALLOC_CAP_8BIT);
            // assert(m_buffer != nullptr);
            // g_deflator = (tdefl_compressor *)heap_caps_malloc(sizeof(tdefl_compressor), MALLOC_CAP_SPIRAM);
            // assert(g_deflator != nullptr);

            m_data_buffer = (char *)heap_caps_malloc(DATASIZE, MALLOC_CAP_SPIRAM | MALLOC_CAP_8BIT);
            m_compressed_buffer = (char *)heap_caps_malloc(DATASIZE, MALLOC_CAP_SPIRAM | MALLOC_CAP_8BIT);
            m_decompressed_buffer = (char *)heap_caps_malloc(DATASIZE, MALLOC_CAP_SPIRAM | MALLOC_CAP_8BIT);
        }
    };
}