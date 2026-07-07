// Lean compiler output
// Module: RequestProject.Core.KasamiAPN
// Imports: public import Init public import Mathlib public import RequestProject.FiniteField.Thm32 public import RequestProject.FiniteField.ExpArith public import RequestProject.FiniteField.FrobAlg
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
LEAN_EXPORT lean_object* lp_RequestProject___private_RequestProject_Core_KasamiAPN_0__Int_neg_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* lp_RequestProject___private_RequestProject_Core_KasamiAPN_0__Int_neg_match__1_splitter___redArg___closed__0;
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_KasamiAPN_kasamiExp___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject___private_RequestProject_Core_KasamiAPN_0__Int_neg_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject___private_RequestProject_Core_KasamiAPN_0__Int_neg_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject___private_RequestProject_Core_KasamiAPN_0__Int_neg_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_KasamiAPN_kasamiExp(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_KasamiAPN_kasamiExp(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_mul(x_2, x_1);
x_4 = lean_nat_pow(x_2, x_3);
lean_dec(x_3);
x_5 = lean_nat_pow(x_2, x_1);
x_6 = lean_nat_sub(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_KasamiAPN_kasamiExp___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_RequestProject_KasamiAPN_kasamiExp(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_lp_RequestProject___private_RequestProject_Core_KasamiAPN_0__Int_neg_match__1_splitter___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_RequestProject___private_RequestProject_Core_KasamiAPN_0__Int_neg_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lp_RequestProject___private_RequestProject_Core_KasamiAPN_0__Int_neg_match__1_splitter___redArg___closed__0;
x_5 = lean_int_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_nat_abs(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_8 = lean_nat_abs(x_1);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_8, x_9);
lean_dec(x_8);
x_11 = lean_apply_1(x_3, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* lp_RequestProject___private_RequestProject_Core_KasamiAPN_0__Int_neg_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_RequestProject___private_RequestProject_Core_KasamiAPN_0__Int_neg_match__1_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_RequestProject___private_RequestProject_Core_KasamiAPN_0__Int_neg_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_RequestProject___private_RequestProject_Core_KasamiAPN_0__Int_neg_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_RequestProject___private_RequestProject_Core_KasamiAPN_0__Int_neg_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_RequestProject___private_RequestProject_Core_KasamiAPN_0__Int_neg_match__1_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_FiniteField_Thm32(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_FiniteField_ExpArith(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_FiniteField_FrobAlg(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_RequestProject_Core_KasamiAPN(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_FiniteField_Thm32(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_FiniteField_ExpArith(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_FiniteField_FrobAlg(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_RequestProject___private_RequestProject_Core_KasamiAPN_0__Int_neg_match__1_splitter___redArg___closed__0 = _init_lp_RequestProject___private_RequestProject_Core_KasamiAPN_0__Int_neg_match__1_splitter___redArg___closed__0();
lean_mark_persistent(lp_RequestProject___private_RequestProject_Core_KasamiAPN_0__Int_neg_match__1_splitter___redArg___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
