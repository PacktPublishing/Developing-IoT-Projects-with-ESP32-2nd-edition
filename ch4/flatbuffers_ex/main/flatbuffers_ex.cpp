#include <cinttypes>
#include "esp_log.h"
#include "esp_heap_caps.h"
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"

#include "AppButton.hpp"
#include "AppLdrLogger.hpp"
#include "AppLdrClient.hpp"

namespace
{
    constexpr const char *TAG{"app"};
    constexpr const size_t BUFFERSIZE{16u * 1024};
    uint8_t *m_buffer;

    app::AppButton m_btn;
    app::AppLdrLogger m_logger;
    app::AppLdrClient m_client;

    void loggerTask(void *param)
    {
        m_logger.run();
    }
}

extern "C" void app_main(void)
{
    m_buffer = reinterpret_cast<uint8_t *>(heap_caps_malloc(BUFFERSIZE, MALLOC_CAP_SPIRAM));

    auto serialize = [](void *)
    {
        ESP_LOGI(TAG, "serializing..");
        size_t len = m_logger.serialize(m_buffer);
        ESP_LOG_BUFFER_HEX(TAG, m_buffer, len);
    };

    auto deserialize = [](void *)
    {
        ESP_LOGI(TAG, "deserializing..");
        m_client.consume(m_buffer);
    };

    m_btn.init(serialize, deserialize);
    m_logger.init();

    xTaskCreate(loggerTask, "logger", 3072, nullptr, 5, nullptr);
}
