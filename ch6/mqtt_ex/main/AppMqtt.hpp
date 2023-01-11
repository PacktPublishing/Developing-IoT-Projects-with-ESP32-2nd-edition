#pragma once

#include <functional>
#include <string>

#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "mqtt_client.h"
#include "sdkconfig.h"
#include "AppSensor.hpp"

namespace app
{
    typedef struct
    {
        esp_mqtt_event_id_t id;
        void *data;
    } MqttEventData_t;

    using MqttEventCb_f = std::function<void(MqttEventData_t)>;

    class AppMqtt
    {
    private:
        AppSensor *m_sensor;
        esp_mqtt_client_handle_t m_client = nullptr;
        std::string m_sensor_topic;
        TaskHandle_t m_publish_handle = nullptr;
        MqttEventCb_f m_event_cb;

        void handleMqttData(esp_mqtt_event_handle_t event);

        static void mqttEventHandler(void *arg,
                                     esp_event_base_t base,
                                     int32_t event_id,
                                     void *event_data);

        static void publishSensorState(void *param);

    public:
        AppMqtt(AppSensor *sensor) : m_sensor(sensor), m_sensor_topic(sensor->getName() + "/state")
        {
        }

        void init(MqttEventCb_f cb)
        {
            m_event_cb = cb;
            esp_mqtt_client_config_t mqtt_cfg = {
                .host = CONFIG_MQTT_BROKER_IP,
                .port = CONFIG_MQTT_PORT,
                .client_id = m_sensor->getName().c_str(),
                .username = MQTT_USER,
                .password = MQTT_PWD};
            m_client = esp_mqtt_client_init(&mqtt_cfg);
            esp_mqtt_client_register_event(m_client, MQTT_EVENT_ANY, mqttEventHandler, this);
            xTaskCreate(publishSensorState, "publish", 4096, this, 5, &m_publish_handle);
            vTaskSuspend(m_publish_handle);
        }

        void start(void)
        {
            esp_mqtt_client_start(m_client);
        }
    };

    void AppMqtt::mqttEventHandler(void *arg,
                                   esp_event_base_t base,
                                   int32_t event_id,
                                   void *event_data)
    {
        AppMqtt *obj = reinterpret_cast<AppMqtt *>(arg);

        switch (static_cast<esp_mqtt_event_id_t>(event_id))
        {
        case MQTT_EVENT_CONNECTED:
            esp_mqtt_client_subscribe(obj->m_client, obj->m_sensor_topic.c_str(), 1);
            vTaskResume(obj->m_publish_handle);
            break;
        case MQTT_EVENT_DATA:
            obj->handleMqttData(reinterpret_cast<esp_mqtt_event_handle_t>(event_data));
            break;
        case MQTT_EVENT_DISCONNECTED:
            vTaskSuspend(obj->m_publish_handle);
            break;
        default:
            break;
        }
        obj->m_event_cb({static_cast<esp_mqtt_event_id_t>(event_id), event_data});
    }

    void AppMqtt::handleMqttData(esp_mqtt_event_handle_t event)
    {
        std::string data{event->data, (size_t)event->data_len};
        m_sensor->setState(data);
    }

    void AppMqtt::publishSensorState(void *param)
    {
        AppMqtt *obj = reinterpret_cast<AppMqtt *>(param);

        while (true)
        {
            vTaskDelay(pdMS_TO_TICKS(3000));
            if (obj->m_sensor->isEnabled())
            {
                std::string state_text = obj->m_sensor->getState();
                esp_mqtt_client_publish(obj->m_client, obj->m_sensor_topic.c_str(), state_text.c_str(), state_text.length(), 1, 0);
            }
        }
    }
}