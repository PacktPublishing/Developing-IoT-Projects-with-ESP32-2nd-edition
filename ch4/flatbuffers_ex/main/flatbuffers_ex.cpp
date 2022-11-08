#include <cinttypes>
#include "esp_log.h"
#include "esp_heap_caps.h"
#include "AppButton.hpp"
#include "AppLdrLogger.hpp"

namespace
{
    constexpr const size_t BUFFERSIZE{16u * 1024};
    uint8_t *m_buffer;

    app::AppButton m_btn;
    app::AppLdrLogger m_logger;

    void binarySerialize(void *btn_ptr)
    {
        size_t len = m_logger.getBinary(m_buffer);
        ESP_LOG_BUFFER_HEX(__func__, m_buffer, len);
    }

    void jsonSerialize(void *btn_ptr)
    {
        std::string json = m_logger.getJson(m_buffer);
        ESP_LOGI(__func__, "%s", json.c_str());
    }
}

extern "C" void app_main(void)
{
    m_buffer = reinterpret_cast<uint8_t *>(heap_caps_malloc(BUFFERSIZE, MALLOC_CAP_SPIRAM));

    m_btn.init(binarySerialize, jsonSerialize);
    m_logger.init();
}
