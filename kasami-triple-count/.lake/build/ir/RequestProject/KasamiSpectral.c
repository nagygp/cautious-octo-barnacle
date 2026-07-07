// Lean compiler output
// Module: RequestProject.KasamiSpectral
// Imports: public import Init public import Mathlib public import RequestProject.KasamiDefs public import RequestProject.KasamiCharacters public import RequestProject.KasamiFourier
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
lean_object* lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
LEAN_EXPORT uint8_t lp_RequestProject_kasamiDiffCount___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_CommRing_toNonUnitalCommRing___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_kasamiDiffCount___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_kasamiDiffCount(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_kasamiDiffCount___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_RequestProject_kasamiFun___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toEuclideanDomain___redArg(lean_object*);
LEAN_EXPORT uint8_t lp_RequestProject_kasamiDiffCount___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_inc(x_1);
lean_inc(x_7);
x_8 = lean_apply_2(x_1, x_7, x_2);
x_9 = lp_RequestProject_kasamiFun___redArg(x_3, x_4, x_8);
x_10 = lp_RequestProject_kasamiFun___redArg(x_3, x_4, x_7);
x_11 = lean_apply_2(x_1, x_9, x_10);
x_12 = lean_apply_2(x_5, x_11, x_6);
x_13 = lean_unbox(x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_kasamiDiffCount___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lp_RequestProject_kasamiDiffCount___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_kasamiDiffCount___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc_ref(x_1);
x_7 = lp_mathlib_Field_toEuclideanDomain___redArg(x_1);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_7);
x_9 = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(x_8);
x_10 = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(x_9);
x_11 = lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_alloc_closure((void*)(lp_RequestProject_kasamiDiffCount___redArg___lam__0___boxed), 7, 6);
lean_closure_set(x_13, 0, x_12);
lean_closure_set(x_13, 1, x_5);
lean_closure_set(x_13, 2, x_1);
lean_closure_set(x_13, 3, x_4);
lean_closure_set(x_13, 4, x_3);
lean_closure_set(x_13, 5, x_6);
x_14 = lp_mathlib_Multiset_filter___redArg(x_13, x_2);
x_15 = l_List_lengthTR___redArg(x_14);
lean_dec(x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_kasamiDiffCount(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lp_RequestProject_kasamiDiffCount___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_KasamiDefs(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_KasamiCharacters(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_KasamiFourier(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_RequestProject_KasamiSpectral(uint8_t builtin) {
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
res = initialize_RequestProject_RequestProject_KasamiFourier(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
