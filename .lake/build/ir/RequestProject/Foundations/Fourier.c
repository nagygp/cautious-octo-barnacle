// Lean compiler output
// Module: RequestProject.Foundations.Fourier
// Imports: public import Init public import RequestProject.Foundations.AddCharCount
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
LEAN_EXPORT lean_object* lp_RequestProject_Vanish_Foundations_fourierTransform___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_Vanish_Foundations_fourierTransform(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_Vanish_Foundations_fourierTransform___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_Vanish_Foundations_crossCorr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_CommRing_toNonUnitalCommRing___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_Vanish_Foundations_crossCorr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_Vanish_Foundations_crossCorr___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_Vanish_Foundations_fourierTransform___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_6);
x_7 = lean_apply_2(x_1, x_2, x_6);
x_8 = lean_apply_1(x_3, x_7);
x_9 = lean_apply_1(x_4, x_6);
x_10 = lean_apply_2(x_5, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_Vanish_Foundations_fourierTransform___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_7 = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(x_3);
x_8 = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
x_10 = lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(x_1);
x_13 = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(x_12);
x_14 = lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_alloc_closure((void*)(lp_RequestProject_Vanish_Foundations_fourierTransform___redArg___lam__0), 6, 5);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_6);
lean_closure_set(x_16, 2, x_4);
lean_closure_set(x_16, 3, x_5);
lean_closure_set(x_16, 4, x_11);
x_17 = lp_mathlib_Finset_sum___redArg(x_9, x_2, x_16);
lean_dec_ref(x_9);
return x_17;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_Vanish_Foundations_fourierTransform(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lp_RequestProject_Vanish_Foundations_fourierTransform___redArg(x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_Vanish_Foundations_crossCorr___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_6);
x_7 = lean_apply_2(x_1, x_6, x_2);
x_8 = lean_apply_1(x_3, x_7);
x_9 = lean_apply_1(x_4, x_6);
x_10 = lean_apply_2(x_5, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_Vanish_Foundations_crossCorr___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_7 = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(x_3);
x_8 = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
x_10 = lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(x_1);
x_13 = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(x_12);
x_14 = lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_alloc_closure((void*)(lp_RequestProject_Vanish_Foundations_crossCorr___redArg___lam__0), 6, 5);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_6);
lean_closure_set(x_16, 2, x_4);
lean_closure_set(x_16, 3, x_5);
lean_closure_set(x_16, 4, x_11);
x_17 = lp_mathlib_Finset_sum___redArg(x_9, x_2, x_16);
lean_dec_ref(x_9);
return x_17;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_Vanish_Foundations_crossCorr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lp_RequestProject_Vanish_Foundations_crossCorr___redArg(x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_Foundations_AddCharCount(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_RequestProject_Foundations_Fourier(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_Foundations_AddCharCount(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
