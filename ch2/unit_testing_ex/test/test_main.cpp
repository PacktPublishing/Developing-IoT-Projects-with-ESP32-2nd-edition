#include "gtest/gtest.h"
#include "AppLight.hpp"
#include "driver/gpio.h"

namespace app
{
    class LightTest : public ::testing::Test
    {
    protected:
        static AppLight light;
        LightTest()
        {
            light.initialize();
        }
    };
    AppLight LightTest::light;

    TEST_F(LightTest, turns_on_light)
    {
        light.on();
        ASSERT_GT(gpio_get_level(GPIO_NUM_4), 0);
    }

    TEST_F(LightTest, turns_off_light)
    {
        light.off();
        ASSERT_EQ(gpio_get_level(GPIO_NUM_4), 0);
    }
} // namespace app

extern "C" void app_main()
{
    ::testing::InitGoogleTest();
    RUN_ALL_TESTS();
}