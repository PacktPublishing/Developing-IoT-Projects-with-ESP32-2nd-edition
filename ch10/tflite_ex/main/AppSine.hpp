#pragma once

#include <cstdint>
#include <limits>
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "esp_log.h"
#include "bootloader_random.h"
#include "esp_random.h"

#include "tensorflow/lite/micro/micro_mutable_op_resolver.h"
#include "tensorflow/lite/micro/micro_interpreter.h"
#include "tensorflow/lite/micro/system_setup.h"
#include "tensorflow/lite/schema/schema_generated.h"

#include "model.h"
#include "AppUi.hpp"

namespace app
{
    class AppSine
    {
    private:
        const tflite::Model *m_model{nullptr};
        tflite::MicroInterpreter *m_interpreter{nullptr};

        uint8_t m_tensor_arena[2000];
        static constexpr float INPUT_RANGE = 2.f * 3.14159265359f;

        AppUi *m_ui;

    public:
        void init(AppUi *ui)
        {
            m_ui = ui;

            m_model = tflite::GetModel(g_model);
            static tflite::MicroMutableOpResolver<1> resolver;
            resolver.AddFullyConnected();

            static tflite::MicroInterpreter static_interpreter(m_model, resolver, m_tensor_arena, sizeof(m_tensor_arena));
            m_interpreter = &static_interpreter;
            m_interpreter->AllocateTensors();
        }

        void run(void)
        {
            TfLiteTensor *input_tensor{m_interpreter->input(0)};
            TfLiteTensor *output_tensor{m_interpreter->output(0)};

            bootloader_random_enable();
            while (1)
            {
                vTaskDelay(pdMS_TO_TICKS(500));

                float random_val = static_cast<float>(esp_random()) /
                                   static_cast<float>(std::numeric_limits<uint32_t>::max());
                float x = random_val * INPUT_RANGE;

                int8_t x_quantized = x / input_tensor->params.scale + input_tensor->params.zero_point;
                input_tensor->data.int8[0] = x_quantized;

                m_interpreter->Invoke();

                int8_t y_quantized = output_tensor->data.int8[0];
                float y = (y_quantized - output_tensor->params.zero_point) * output_tensor->params.scale;
                m_ui->drawSinePoint(x, y);
            }
        }
    };
}