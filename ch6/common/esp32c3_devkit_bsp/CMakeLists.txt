set(srcs "ws2812_led.c" "led_strip_rmt_ws2812.c" "button.c" "button_obj.cpp")

idf_component_register(SRCS ${srcs}
                    INCLUDE_DIRS include
                    REQUIRES "driver")
