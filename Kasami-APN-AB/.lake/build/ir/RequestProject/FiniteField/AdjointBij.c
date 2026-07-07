// Lean compiler output
// Module: RequestProject.FiniteField.AdjointBij
// Imports: public import Init public import Mathlib public import RequestProject.FiniteField.TraceNorm public import RequestProject.FiniteField.ExpArith public import RequestProject.FiniteField.FrobAlg public import RequestProject.FiniteField.Lemma31 public import RequestProject.FiniteField.BareLemma31Skeleton
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
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_FiniteField_TraceNorm(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_FiniteField_ExpArith(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_FiniteField_FrobAlg(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_FiniteField_Lemma31(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_FiniteField_BareLemma31Skeleton(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_RequestProject_FiniteField_AdjointBij(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_FiniteField_TraceNorm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_FiniteField_ExpArith(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_FiniteField_FrobAlg(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_FiniteField_Lemma31(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_FiniteField_BareLemma31Skeleton(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
