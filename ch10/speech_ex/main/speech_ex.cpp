#include "AppSpeech.hpp"

namespace
{
    app::AppSpeech m_app_sp;
}

extern "C" void app_main()
{
    m_app_sp.start();
}
