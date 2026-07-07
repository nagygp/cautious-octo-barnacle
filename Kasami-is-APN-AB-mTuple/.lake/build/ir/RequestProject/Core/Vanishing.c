// Lean compiler output
// Module: RequestProject.Core.Vanishing
// Imports: public import Init public import Mathlib public import RequestProject.Core.Character
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
extern lean_object* lp_mathlib_Int_instCommMonoid;
lean_object* lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_MTupleCount_TupleSet___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_MTupleCount_P___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_MTupleCount_TupleSet___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_RequestProject_MTupleCount_TupleSet___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_MTupleCount_TupleSet___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_MTupleCount_TupleSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_prod___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_CommRing_toNonUnitalCommRing___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_MTupleCount_TupleSet___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(lean_object*);
lean_object* lp_RequestProject_MTupleCount_S___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_MTupleCount_00_u03ba___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_MTupleCount_P(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_MTupleCount_00_u03ba(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_MTupleCount_TupleSet___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_MTupleCount_P___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Fintype_piFinset___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Field_toEuclideanDomain___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_MTupleCount_P___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_MTupleCount_TupleSet___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_MTupleCount_TupleSet___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_RequestProject_MTupleCount_TupleSet___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_MTupleCount_TupleSet___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_4);
x_5 = lean_apply_1(x_1, x_4);
x_6 = lean_apply_1(x_2, x_4);
x_7 = lean_apply_2(x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t lp_RequestProject_MTupleCount_TupleSet___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_alloc_closure((void*)(lp_RequestProject_MTupleCount_TupleSet___redArg___lam__1), 4, 3);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
lean_closure_set(x_8, 2, x_2);
x_9 = l_List_finRange(x_3);
x_10 = lp_mathlib_Finset_sum___redArg(x_4, x_9, x_8);
x_11 = lean_apply_2(x_5, x_10, x_6);
x_12 = lean_unbox(x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_MTupleCount_TupleSet___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lp_RequestProject_MTupleCount_TupleSet___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_MTupleCount_TupleSet___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_6 = lp_mathlib_Field_toEuclideanDomain___redArg(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec_ref(x_6);
x_8 = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(x_7);
x_9 = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
x_11 = lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lp_mathlib_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(x_9);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_alloc_closure((void*)(lp_RequestProject_MTupleCount_TupleSet___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_15, 0, x_4);
lean_inc(x_3);
x_16 = l_List_finRange(x_3);
lean_inc(x_3);
x_17 = lean_alloc_closure((void*)(lp_RequestProject_MTupleCount_TupleSet___redArg___lam__2___boxed), 7, 6);
lean_closure_set(x_17, 0, x_5);
lean_closure_set(x_17, 1, x_12);
lean_closure_set(x_17, 2, x_3);
lean_closure_set(x_17, 3, x_10);
lean_closure_set(x_17, 4, x_2);
lean_closure_set(x_17, 5, x_14);
x_18 = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(x_18, 0, x_3);
x_19 = lp_mathlib_Fintype_piFinset___redArg(x_18, x_16, x_15);
x_20 = lp_mathlib_Multiset_filter___redArg(x_17, x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_MTupleCount_TupleSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_RequestProject_MTupleCount_TupleSet___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_MTupleCount_00_u03ba___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lp_RequestProject_MTupleCount_TupleSet___redArg(x_1, x_2, x_3, x_4, x_5);
x_7 = l_List_lengthTR___redArg(x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_MTupleCount_00_u03ba(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_RequestProject_MTupleCount_00_u03ba___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_MTupleCount_P___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_apply_1(x_1, x_7);
x_9 = lean_apply_2(x_2, x_3, x_8);
x_10 = lp_RequestProject_MTupleCount_S___redArg(x_4, x_5, x_9, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_MTupleCount_P___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = lp_mathlib_Int_instCommMonoid;
lean_inc_ref(x_1);
x_8 = lp_mathlib_Field_toEuclideanDomain___redArg(x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
lean_dec_ref(x_8);
x_10 = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(x_9);
x_11 = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(x_10);
x_12 = lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = l_List_finRange(x_3);
x_15 = lean_alloc_closure((void*)(lp_RequestProject_MTupleCount_P___redArg___lam__0), 7, 6);
lean_closure_set(x_15, 0, x_4);
lean_closure_set(x_15, 1, x_13);
lean_closure_set(x_15, 2, x_6);
lean_closure_set(x_15, 3, x_1);
lean_closure_set(x_15, 4, x_2);
lean_closure_set(x_15, 5, x_5);
x_16 = lp_mathlib_Finset_prod___redArg(x_7, x_14, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_MTupleCount_P(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lp_RequestProject_MTupleCount_P___redArg(x_2, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_MTupleCount_P___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lp_RequestProject_MTupleCount_P(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_Core_Character(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_RequestProject_Core_Vanishing(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_Core_Character(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
