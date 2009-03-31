///
/// @file libyasm/plugin.cpp
/// @brief YASM plugin loader implementation for Windows and Unix.
///
/// @license
///  Copyright (C) 2008  Peter Johnson
///
/// Redistribution and use in source and binary forms, with or without
/// modification, are permitted provided that the following conditions
/// are met:
///  - Redistributions of source code must retain the above copyright
///    notice, this list of conditions and the following disclaimer.
///  - Redistributions in binary form must reproduce the above copyright
///    notice, this list of conditions and the following disclaimer in the
///    documentation and/or other materials provided with the distribution.
///
/// THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND OTHER CONTRIBUTORS ``AS IS''
/// AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
/// IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
/// ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR OTHER CONTRIBUTORS BE
/// LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
/// CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
/// SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
/// INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
/// CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
/// ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
/// POSSIBILITY OF SUCH DAMAGE.
/// @endlicense
///
#include "System/plugin.h"

#include <iostream>
#include <vector>

#if defined(_MSC_VER)
#include <windows.h>
#elif defined(__MACH__) || defined(__APPLE__) || defined(__GNUC__)
#include <dlfcn.h>
#endif

#include "config.h"

static std::vector<void*> loaded_plugins;

static void*
load_dll(const std::string& name)
{
#if defined(_MSC_VER)
    return LoadLibrary(name.c_str());
#elif defined(__MACH__) || defined(__APPLE__) || defined(__GNUC__)
    return dlopen(name.c_str(), RTLD_NOW);
#else
    return 0;
#endif
}

namespace yasm
{

bool
load_plugin(const std::string& name)
{
    // Load library
    void* lib = 0;

    // First attempt: FOO.so
    std::string path = name;
#if defined(_MSC_VER)
    if (path.compare(path.length()-4, 4, ".dll") != 0)
        path += ".dll";
#elif defined(__MACH__) || defined(__APPLE__)
    if (path.compare(path.length()-3, 3, ".dylib") != 0)
        path += ".dylib";
#elif defined(__GNUC__)
    if (path.compare(path.length()-3, 3, ".so") != 0)
        path += ".so";
#endif
    lib = load_dll(path);

    // Second attempt: PLUGIN_INSTALL_DIR/FOO.so
    if (!lib && name.find_first_of("\\/") == std::string::npos)
    {
#if defined(_MSC_VER)
        path.insert(0, PLUGIN_INSTALL_DIR "\\");
#elif defined(__GNUC__)
        path.insert(0, PLUGIN_INSTALL_DIR "/");
#endif
        lib = load_dll(path);
    }

    // Last attempt: FOO
    if (!lib)
        lib = load_dll(name);

    if (!lib)
        return false;   // Didn't load successfully

    // Add to vector of loaded plugins
    loaded_plugins.push_back(lib);

    // Get yasm_init_plugin() function and run it

    void (*init_plugin) (void) = 0;
#if defined(_MSC_VER)
    init_plugin = reinterpret_cast<void (*)(void)>
        (GetProcAddress((HINSTANCE)lib, "yasm_init_plugin"));
#elif defined(__MACH__) || defined(__APPLE__) || defined(__GNUC__)
    init_plugin = reinterpret_cast<void (*)(void)>
        (reinterpret_cast<uintptr_t>(dlsym(lib, "yasm_init_plugin")));
#endif

    if (!init_plugin)
        return false;   // Didn't load successfully

    init_plugin();
    return true;
}

void
unload_plugins(void)
{
    while (!loaded_plugins.empty()) {
        void* plugin = loaded_plugins.back();
        loaded_plugins.pop_back();
#if defined(_MSC_VER)
        FreeLibrary(reinterpret_cast<HINSTANCE>(plugin));
#elif defined(__MACH__) || defined(__APPLE__) || defined(__GNUC__)
        dlclose(plugin);
#endif
    }
}

} // namespace yasm
