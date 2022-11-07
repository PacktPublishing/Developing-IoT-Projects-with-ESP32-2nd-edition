#include "AppButton.hpp"
#include "AppZip.hpp"
#include <cstring>
#include "esp_log.h"

namespace
{
    const char *m_test_str = "this is a repeating text to be compressed. you can try anything\n"
                             "this is a repeating text to be compressed. you can try anything\n"
                             "this is a repeating text to be compressed. you can try anything\n"
                             "this is a repeating text to be compressed. you can try anything";

    app::AppButton m_btn;
    app::AppZip m_zip;
    size_t m_data_len;
    char *m_compressed_data;
    char *m_decompressed_data;

    void leftBtnForZip(void *btn_ptr)
    {
        m_data_len = strlen(m_test_str);
        m_compressed_data = m_zip.zip(m_test_str, m_data_len);
        ESP_LOGI(__func__, "compressed to %u from %u", m_data_len, strlen(m_test_str));
        ESP_LOG_BUFFER_HEX(__func__, m_compressed_data, m_data_len);
    }

    void middleBtnForUnzip(void *btn_ptr)
    {
        m_decompressed_data = m_zip.unzip(m_compressed_data, m_data_len);
        ESP_LOGI(__func__, "%.*s", m_data_len, m_decompressed_data);
    }
}

extern "C" void app_main(void)
{
    m_zip.init();
    m_btn.init(leftBtnForZip, middleBtnForUnzip);
}
