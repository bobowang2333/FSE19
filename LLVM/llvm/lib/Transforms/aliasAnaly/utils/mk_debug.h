/*
 * Author: Markus Kusano
 *
 * Debugging output macros
 */
#pragma once


#ifdef MK_DEBUG
#define DEBUG_MSG(str) do { errs() << str; } while( false )
#else
#define DEBUG_MSG(str) do { } while (false)
#endif

#ifdef MK_DEBUG
#define DEBUG_MSG_RED(str) \
do { \
    if (errs().has_colors()) {  \
      errs().changeColor(raw_ostream::RED); \
    } \
    errs() << str;  \
    errs().resetColor(); } while (false)
#else
#define DEBUG_MSG_RED(str) do { } while (false)
#endif
