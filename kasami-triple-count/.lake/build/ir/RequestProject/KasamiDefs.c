// Lean compiler output
// Module: RequestProject.KasamiDefs
// Imports: public import Init public import Mathlib
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
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_kasamiDelta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_tripleSet___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_kasamiDelta___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_CommRing_toNonUnitalCommRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_tripleSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_kasamiFun___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_kasamiExp___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_RequestProject_tripleSet___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_kasamiDelta___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_kasamiFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_product___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_kasamiFun(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_tripleSet___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_kasamiExp(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_kasamiDelta___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_kasamiFun___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_image___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toEuclideanDomain___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_kasamiExp(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_nat_pow(x_2, x_1);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_pow(x_4, x_1);
x_6 = lean_nat_sub(x_3, x_5);
lean_dec(x_5);
lean_dec(x_3);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_kasamiExp___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_RequestProject_kasamiExp(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_kasamiFun___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lp_mathlib_Field_toSemifield___redArg(x_1);
x_5 = lp_mathlib_Semifield_toDivisionSemiring___redArg(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec_ref(x_5);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lp_RequestProject_kasamiExp(x_2);
x_9 = lean_apply_2(x_7, x_8, x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_kasamiFun___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_RequestProject_kasamiFun___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_kasamiFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_RequestProject_kasamiFun___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_kasamiFun___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_RequestProject_kasamiFun(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_kasamiDelta___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_5);
x_6 = lp_RequestProject_kasamiFun___redArg(x_1, x_2, x_5);
lean_inc(x_3);
lean_inc(x_4);
x_7 = lean_apply_2(x_3, x_5, x_4);
x_8 = lp_RequestProject_kasamiFun___redArg(x_1, x_2, x_7);
lean_inc(x_3);
x_9 = lean_apply_2(x_3, x_6, x_8);
x_10 = lean_apply_2(x_3, x_9, x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_kasamiDelta___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_RequestProject_kasamiDelta___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_kasamiDelta___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_inc_ref(x_1);
x_5 = lp_mathlib_Field_toEuclideanDomain___redArg(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec_ref(x_5);
x_7 = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(x_6);
x_8 = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(x_7);
x_9 = lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec_ref(x_9);
lean_inc_ref(x_1);
x_11 = lp_mathlib_Field_toDivisionRing___redArg(x_1);
x_12 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_12);
lean_dec_ref(x_11);
x_13 = lp_mathlib_Ring_toAddGroupWithOne___redArg(x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_14);
lean_dec_ref(x_13);
x_15 = lean_ctor_get(x_14, 2);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_alloc_closure((void*)(lp_RequestProject_kasamiDelta___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_4);
lean_closure_set(x_16, 2, x_10);
lean_closure_set(x_16, 3, x_15);
x_17 = lp_mathlib_Finset_image___redArg(x_3, x_16, x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_kasamiDelta(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_RequestProject_kasamiDelta___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t lp_RequestProject_tripleSet___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
lean_inc(x_1);
lean_inc(x_2);
x_12 = lean_apply_2(x_1, x_2, x_9);
lean_inc(x_1);
lean_inc(x_3);
x_13 = lean_apply_2(x_1, x_3, x_10);
lean_inc(x_4);
x_14 = lean_apply_2(x_4, x_12, x_13);
lean_inc(x_4);
x_15 = lean_apply_2(x_4, x_2, x_3);
x_16 = lean_apply_2(x_1, x_15, x_11);
x_17 = lean_apply_2(x_4, x_14, x_16);
x_18 = lean_apply_2(x_5, x_17, x_6);
x_19 = lean_unbox(x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_tripleSet___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lp_RequestProject_tripleSet___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_tripleSet___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_inc_ref(x_1);
x_7 = lp_mathlib_Field_toEuclideanDomain___redArg(x_1);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_7);
x_9 = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(x_8);
x_10 = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(x_9);
lean_inc_ref(x_10);
x_11 = lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lp_mathlib_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(x_10);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec_ref(x_14);
lean_inc_ref(x_3);
x_16 = lean_alloc_closure((void*)(lp_RequestProject_tripleSet___redArg___lam__0___boxed), 7, 6);
lean_closure_set(x_16, 0, x_12);
lean_closure_set(x_16, 1, x_5);
lean_closure_set(x_16, 2, x_6);
lean_closure_set(x_16, 3, x_13);
lean_closure_set(x_16, 4, x_3);
lean_closure_set(x_16, 5, x_15);
x_17 = lp_RequestProject_kasamiDelta___redArg(x_1, x_2, x_3, x_4);
lean_inc_n(x_17, 2);
x_18 = lp_mathlib_Multiset_product___redArg(x_17, x_17);
x_19 = lp_mathlib_Multiset_product___redArg(x_17, x_18);
x_20 = lp_mathlib_Multiset_filter___redArg(x_16, x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_tripleSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lp_RequestProject_tripleSet___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_RequestProject_KasamiDefs(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
