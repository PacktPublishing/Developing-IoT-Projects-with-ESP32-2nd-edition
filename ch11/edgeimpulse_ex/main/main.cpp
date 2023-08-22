
#include "AppLed.hpp"
#include "AppSpeech.hpp"

namespace
{
    app::AppLed app_led;
    app::AppSpeech app_speech;

}

extern "C" void app_main()
{
    app_speech.init({[]()
                     { app_led.setColor(app::eColor::Blue); },
                     []()
                     { app_led.setColor(app::eColor::Red); },
                     []()
                     { app_led.setColor(app::eColor::Green); }});
    app_led.init();

    app_speech.start();
}
