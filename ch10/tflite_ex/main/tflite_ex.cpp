
#include "AppSine.hpp"
#include "AppUi.hpp"

namespace
{
    app::AppSine app_sine;
    app::AppUi app_ui;
}

extern "C" void app_main(void)
{
    app_ui.init();
    app_sine.init(&app_ui);

    app_sine.run();
}