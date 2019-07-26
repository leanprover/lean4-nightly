// Lean compiler output
// Module: init.system.filepath
// Imports: init.system.platform init.data.char.basic
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
uint32 l_System_FilePath_pathSeparator___closed__1;
obj* l_System_FilePath_pathSeparators___closed__3;
extern uint8 l_System_Platform_isWindows;
obj* l_System_FilePath_pathSeparators___closed__2;
uint32 l_System_FilePath_searchPathSeparator;
obj* l_System_FilePath_pathSeparators;
obj* l_System_FilePath_pathSeparators___closed__1;
uint32 l_System_FilePath_searchPathSeparator___closed__1;
uint32 l_System_FilePath_extSeparator;
uint32 l_System_FilePath_pathSeparator;
uint32 _init_l_System_FilePath_pathSeparator___closed__1() {
_start:
{
uint8 x_1; 
x_1 = l_System_Platform_isWindows;
if (x_1 == 0)
{
uint32 x_2; 
x_2 = 47;
return x_2;
}
else
{
uint32 x_3; 
x_3 = 92;
return x_3;
}
}
}
uint32 _init_l_System_FilePath_pathSeparator() {
_start:
{
uint32 x_1; 
x_1 = l_System_FilePath_pathSeparator___closed__1;
return x_1;
}
}
obj* _init_l_System_FilePath_pathSeparators___closed__1() {
_start:
{
uint32 x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = 47;
x_2 = lean::box(0);
x_3 = lean::box_uint32(x_1);
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
return x_4;
}
}
obj* _init_l_System_FilePath_pathSeparators___closed__2() {
_start:
{
uint32 x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = 92;
x_2 = l_System_FilePath_pathSeparators___closed__1;
x_3 = lean::box_uint32(x_1);
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
return x_4;
}
}
obj* _init_l_System_FilePath_pathSeparators___closed__3() {
_start:
{
uint8 x_1; 
x_1 = l_System_Platform_isWindows;
if (x_1 == 0)
{
obj* x_2; 
x_2 = l_System_FilePath_pathSeparators___closed__1;
return x_2;
}
else
{
obj* x_3; 
x_3 = l_System_FilePath_pathSeparators___closed__2;
return x_3;
}
}
}
obj* _init_l_System_FilePath_pathSeparators() {
_start:
{
obj* x_1; 
x_1 = l_System_FilePath_pathSeparators___closed__3;
return x_1;
}
}
uint32 _init_l_System_FilePath_searchPathSeparator___closed__1() {
_start:
{
uint8 x_1; 
x_1 = l_System_Platform_isWindows;
if (x_1 == 0)
{
uint32 x_2; 
x_2 = 58;
return x_2;
}
else
{
uint32 x_3; 
x_3 = 59;
return x_3;
}
}
}
uint32 _init_l_System_FilePath_searchPathSeparator() {
_start:
{
uint32 x_1; 
x_1 = l_System_FilePath_searchPathSeparator___closed__1;
return x_1;
}
}
uint32 _init_l_System_FilePath_extSeparator() {
_start:
{
uint32 x_1; 
x_1 = 46;
return x_1;
}
}
obj* initialize_init_system_platform(obj*);
obj* initialize_init_data_char_basic(obj*);
static bool _G_initialized = false;
obj* initialize_init_system_filepath(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_system_platform(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_char_basic(w);
if (io_result_is_error(w)) return w;
l_System_FilePath_pathSeparator___closed__1 = _init_l_System_FilePath_pathSeparator___closed__1();
l_System_FilePath_pathSeparator = _init_l_System_FilePath_pathSeparator();
l_System_FilePath_pathSeparators___closed__1 = _init_l_System_FilePath_pathSeparators___closed__1();
lean::mark_persistent(l_System_FilePath_pathSeparators___closed__1);
l_System_FilePath_pathSeparators___closed__2 = _init_l_System_FilePath_pathSeparators___closed__2();
lean::mark_persistent(l_System_FilePath_pathSeparators___closed__2);
l_System_FilePath_pathSeparators___closed__3 = _init_l_System_FilePath_pathSeparators___closed__3();
lean::mark_persistent(l_System_FilePath_pathSeparators___closed__3);
l_System_FilePath_pathSeparators = _init_l_System_FilePath_pathSeparators();
lean::mark_persistent(l_System_FilePath_pathSeparators);
l_System_FilePath_searchPathSeparator___closed__1 = _init_l_System_FilePath_searchPathSeparator___closed__1();
l_System_FilePath_searchPathSeparator = _init_l_System_FilePath_searchPathSeparator();
l_System_FilePath_extSeparator = _init_l_System_FilePath_extSeparator();
return w;
}
