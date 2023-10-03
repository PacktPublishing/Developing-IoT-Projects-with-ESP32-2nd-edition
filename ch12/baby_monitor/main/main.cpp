
#include "AppAudio.hpp"
#include "AppDriver.hpp"
#include "AppRmaker.hpp"
#include "AppMem.hpp"

namespace
{
    app::AppAudio app_audio;
    app::AppDriver app_driver;
    app::AppRmaker app_rmaker;
    app::AppMem app_mem;
}

extern "C" void app_main()
{
    app_mem.print();
    app_driver.init();
    app_rmaker.init();
    app_audio.init([](bool crying)
                    { app_rmaker.update(crying); });

    app_mem.print();
    app_rmaker.start();
    app_driver.start();
    app_audio.start();

    app_mem.monitor();
}
