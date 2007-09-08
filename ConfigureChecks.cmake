INCLUDE(CheckCXXSourceCompiles)
INCLUDE(TestCXXAcceptsFlag)
INCLUDE(CMakeBackwardCompatibilityCXX)
INCLUDE(CheckFunctionExists)
INCLUDE(CheckIncludeFile)
INCLUDE(CheckSymbolExists)

FIND_PACKAGE(Boost REQUIRED)
INCLUDE_DIRECTORIES(${Boost_INCLUDE_DIRS})
LINK_DIRECTORIES(${Boost_LIBRARY_DIRS})

#FIND_PROGRAM(XMLTO NAMES xmlto)
#IF (XMLTO)
#    SET(BUILD_MAN ON)
#ENDIF (XMLTO)

# ISO C99 include files
CHECK_INCLUDE_FILE(stdint.h HAVE_STDINT_H)

# Platform-specific include files (POSIX, Win32)
CHECK_INCLUDE_FILE(inttypes.h HAVE_INTTYPES_H)
CHECK_INCLUDE_FILE(locale.h HAVE_LOCALE_H)
CHECK_INCLUDE_FILE(libgen.h HAVE_LIBGEN_H)
CHECK_INCLUDE_FILE(unistd.h HAVE_UNISTD_H)
CHECK_INCLUDE_FILE(direct.h HAVE_DIRECT_H)
CHECK_INCLUDE_FILE(strings.h HAVE_STRINGS_H)

CHECK_SYMBOL_EXISTS(abort "stdlib.h" HAVE_ABORT)
CHECK_SYMBOL_EXISTS(toascii "ctype.h" HAVE_TOASCII)
CHECK_SYMBOL_EXISTS(vsnprintf "stdio.h" HAVE_VSNPRINTF)

CHECK_FUNCTION_EXISTS(getcwd HAVE_GETCWD)
CHECK_FUNCTION_EXISTS(strcasecmp HAVE_STRCASECMP)
CHECK_FUNCTION_EXISTS(strncasecmp HAVE_STRNCASECMP)
CHECK_FUNCTION_EXISTS(stricmp HAVE_STRICMP)
CHECK_FUNCTION_EXISTS(strcmpi HAVE_STRCMPI)
CHECK_FUNCTION_EXISTS(_stricmp HAVE__STRICMP)
CHECK_FUNCTION_EXISTS(_strcmpi HAVE__STRCMPI)

CONFIGURE_FILE(config.h.cmake ${CMAKE_CURRENT_BINARY_DIR}/config.h)

ADD_DEFINITIONS(-DHAVE_CONFIG_H)
#INCLUDE(FindPythonInterp)
#INCLUDE(FindPythonLibs)

#IF (PYTHONINTERP_FOUND)
#    EXEC_PROGRAM("${PYTHON_EXECUTABLE}"
#                 ARGS "${yasm_SOURCE_DIR}/CMake/have_pyrex.py"
#                 RETURN_VALUE HAVE_PYREX)
#ENDIF (PYTHONINTERP_FOUND)

IF (CMAKE_COMPILER_IS_GNUCXX)
    CHECK_CXX_ACCEPTS_FLAG(-pipe CXX_ACCEPTS_PIPE)
    CHECK_CXX_ACCEPTS_FLAG(-ansi CXX_ACCEPTS_ANSI)
    CHECK_CXX_ACCEPTS_FLAG(-pedantic CXX_ACCEPTS_PEDANTIC)
    CHECK_CXX_ACCEPTS_FLAG(-Wall CXX_ACCEPTS_WALL)
    CHECK_CXX_ACCEPTS_FLAG(-Wextra CXX_ACCEPTS_WEXTRA)
    CHECK_CXX_ACCEPTS_FLAG(-Wno-unused-parameter CXX_ACCEPTS_WNOUNUSEDPARAM)

    IF (CXX_ACCEPTS_PIPE)
        ADD_DEFINITIONS(-pipe)
    ENDIF (CXX_ACCEPTS_PIPE)

    IF (CXX_ACCEPTS_ANSI)
        ADD_DEFINITIONS(-ansi)
    ENDIF (CXX_ACCEPTS_ANSI)

    IF (CXX_ACCEPTS_PEDANTIC)
        ADD_DEFINITIONS(-pedantic)
    ENDIF (CXX_ACCEPTS_PEDANTIC)

    IF (CXX_ACCEPTS_WALL)
        ADD_DEFINITIONS(-Wall)
    ENDIF (CXX_ACCEPTS_WALL)

    IF (CXX_ACCEPTS_WEXTRA)
        ADD_DEFINITIONS(-Wextra)
    ENDIF (CXX_ACCEPTS_WEXTRA)

    IF (CXX_ACCEPTS_WNOUNUSEDPARAM)
        ADD_DEFINITIONS(-Wno-unused-parameter)
    ENDIF (CXX_ACCEPTS_WNOUNUSEDPARAM)
ENDIF (CMAKE_COMPILER_IS_GNUCXX)

