#include "AppButton.hpp"
#include "AppZip.hpp"
#include <cstring>
#include "esp_log.h"

// unsigned char * base64_encode(const unsigned char *src, size_t len, size_t *out_len);

// int mbedtls_base64_encode( unsigned char *dst, size_t dlen, size_t *olen, const unsigned char *src, size_t slen )

// $ echo AQIDBAUGBwgJCgsM | base64 -d | od -t x8 -An --endian=big

// $ echo AQIDBAUGBwgJCgsM | base64 -d > 1.l
// $ xxd 1.l

namespace
{
    const char *s_pStr = "Good morning Dr. Chandra. This is Hal. I am ready for my first lesson."
                         "Good morning Dr. Chandra. This is Hal. I am ready for my first lesson."
                         "Good morning Dr. Chandra. This is Hal. I am ready for my first lesson."
                         "Good morning Dr. Chandra. This is Hal. I am ready for my first lesson."
                         "Good morning Dr. Chandra. This is Hal. I am ready for my first lesson."
                         "Good morning Dr. Chandra. This is Hal. I am ready for my first lesson."
                         "Good morning Dr. Chandra. This is Hal. I am ready for my first lesson.";

    app::AppButton m_btn;
    app::AppZip m_zip;
    size_t m_data_len;
    char *m_compressed_data;
    char *m_decompressed_data;

    void leftBtnForZip(void *btn_ptr)
    {
        m_data_len = strlen(s_pStr);
        m_compressed_data = m_zip.zip(s_pStr, &m_data_len);
        ESP_LOGI(__func__, "compressed to %u", m_data_len);
    }

    void middleBtnForUnzip(void *btn_ptr)
    {
        // m_zip.test(sample_zip, sizeof(sample_zip));
        ESP_LOGI(__func__, "decompressing data (len=%u)", m_data_len);
        m_decompressed_data = m_zip.unzip(m_compressed_data, m_data_len);
        ESP_LOGI(__func__, "%.*s", strlen(s_pStr), m_decompressed_data);
    }
}

extern "C" void app_main(void)
{
    m_zip.init();
    m_btn.init(leftBtnForZip, middleBtnForUnzip);
}
