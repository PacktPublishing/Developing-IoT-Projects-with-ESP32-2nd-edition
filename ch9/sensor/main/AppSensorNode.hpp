// https://rainmaker.espressif.com/docs/standard-types.html

#pragma once

#include <cstring>
#include <cstdint>
#include <functional>

#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "sdkconfig.h"

#include "tsl2561.h"
#include "bmp280.h"
#include "AppNode.hpp"
#include "AppCommon.hpp"

#define LIGHT_INTENSITY(x) (uint8_t)((x) > 2048 ? 100 : (int)((x)*100 / 2048))

namespace app
{
    using SensorReadingCb_f = std::function<void(const SensorReading_t &)>;

    class AppSensorNode : public AppNode
    {
    private:
        SensorReadingCb_f m_reading_cb;
        tsl2561_t m_light_sensor;
        bmp280_t m_temp_sensor;

        esp_rmaker_param_t *m_light_rmaker_param;
        esp_rmaker_param_t *m_temp_rmaker_param;

        static void defineSensor(esp_rmaker_device_t *device, void *arg);
        static void readSensor(void *arg);

    public:
        AppSensorNode() : AppNode({"Sensor Node", "esp.node.sensor", "Sensor", "esp.device.sensor", defineSensor, this}), m_reading_cb(nullptr)
        {
        }

        void init() override
        {
            static bmp280_params_t bme280_sensor_params;
            memset(&m_light_sensor, 0, sizeof(tsl2561_t));

            ESP_ERROR_CHECK(i2cdev_init());
            
            ESP_ERROR_CHECK(tsl2561_init_desc(&m_light_sensor, TSL2561_I2C_ADDR_FLOAT, I2C_NUM_0, gpio_num_t::GPIO_NUM_41, gpio_num_t::GPIO_NUM_40));
            ESP_ERROR_CHECK(tsl2561_init(&m_light_sensor));

            ESP_ERROR_CHECK(bmp280_init_default_params(&bme280_sensor_params));
            ESP_ERROR_CHECK(bmp280_init_desc(&m_temp_sensor, BMP280_I2C_ADDRESS_0, I2C_NUM_0, gpio_num_t::GPIO_NUM_41, gpio_num_t::GPIO_NUM_40));
            ESP_ERROR_CHECK(bmp280_init(&m_temp_sensor, &bme280_sensor_params));

            AppNode::init();
        }

        void start() override
        {
            AppNode::start();
            xTaskCreate(readSensor, "sensor", 4096, this, 5, nullptr);
        }

        void setReadingCb(SensorReadingCb_f cb)
        {
            m_reading_cb = cb;
        }
    };

    void AppSensorNode::defineSensor(esp_rmaker_device_t *device, void *arg)
    {
        AppSensorNode *obj = reinterpret_cast<AppSensorNode *>(arg);

        obj->m_light_rmaker_param = esp_rmaker_intensity_param_create("light-intensity", 0);
        esp_rmaker_device_add_param(device, obj->m_light_rmaker_param);
        esp_rmaker_device_assign_primary_param(device, obj->m_light_rmaker_param);

        obj->m_temp_rmaker_param = esp_rmaker_temperature_param_create("temperature", 0);
        esp_rmaker_device_add_param(device, obj->m_temp_rmaker_param);
    }

    void AppSensorNode::readSensor(void *arg)
    {
        AppSensorNode *obj = reinterpret_cast<AppSensorNode *>(arg);
        float pressure;
        float temperature;
        float humidity;
        uint32_t lux;

        while (true)
        {
            vTaskDelay(pdMS_TO_TICKS(10000));

            bmp280_read_float(&obj->m_temp_sensor, &temperature, &pressure, &humidity);
            tsl2561_read_lux(&obj->m_light_sensor, &lux);
            SensorReading_t reading{LIGHT_INTENSITY(lux), temperature};
            if (obj->m_connected)
            {
                esp_rmaker_param_update_and_report(obj->m_temp_rmaker_param, esp_rmaker_float(reading.temperature));
                esp_rmaker_param_update_and_report(obj->m_light_rmaker_param, esp_rmaker_int(reading.light_intensity));
            }
            if (obj->m_reading_cb != nullptr)
            {
                obj->m_reading_cb(reading);
            }
        }
    }
}
