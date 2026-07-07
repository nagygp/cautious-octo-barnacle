// Lean compiler output
// Module: RequestProject.KasamiFourier
// Imports: public import Init public import Mathlib public import RequestProject.KasamiDefs public import RequestProject.KasamiCharacters
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
static lean_object* lp_RequestProject_deltaIndicator___redArg___closed__1;
lean_object* lp_mathlib_Complex_ofReal(lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
uint8_t lp_mathlib_Multiset_decidableMem___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* lp_RequestProject_deltaIndicator___redArg___closed__0;
lean_object* lp_RequestProject_kasamiDelta___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_deltaIndicator___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_deltaIndicator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_RequestProject_deltaIndicator___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_2 = lp_mathlib_Complex_ofReal(x_1);
return x_2;
}
}
static lean_object* _init_lp_RequestProject_deltaIndicator___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
x_2 = lp_mathlib_Complex_ofReal(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_deltaIndicator___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
lean_inc_ref(x_3);
x_6 = lp_RequestProject_kasamiDelta___redArg(x_1, x_2, x_3, x_4);
x_7 = lp_mathlib_Multiset_decidableMem___redArg(x_3, x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lp_RequestProject_deltaIndicator___redArg___closed__0;
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lp_RequestProject_deltaIndicator___redArg___closed__1;
return x_9;
}
}
}
LEAN_EXPORT lean_object* lp_RequestProject_deltaIndicator(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_RequestProject_deltaIndicator___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_KasamiDefs(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_KasamiCharacters(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_RequestProject_KasamiFourier(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_KasamiDefs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_KasamiCharacters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_RequestProject_deltaIndicator___redArg___closed__0 = _init_lp_RequestProject_deltaIndicator___redArg___closed__0();
lean_mark_persistent(lp_RequestProject_deltaIndicator___redArg___closed__0);
lp_RequestProject_deltaIndicator___redArg___closed__1 = _init_lp_RequestProject_deltaIndicator___redArg___closed__1();
lean_mark_persistent(lp_RequestProject_deltaIndicator___redArg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
