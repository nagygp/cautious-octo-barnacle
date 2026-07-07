// Lean compiler output
// Module: RequestProject.DempwolffMueller.AdjointBij
// Imports: public import Init public import Mathlib public import RequestProject.DempwolffMueller.TraceNorm public import RequestProject.Core.ExpArith public import RequestProject.DempwolffMueller.ExpArith public import RequestProject.DempwolffMueller.FrobAlg public import RequestProject.DempwolffMueller.Lemma31 public import RequestProject.DempwolffMueller.BareLemma31
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
lean_object* initialize_RequestProject_RequestProject_DempwolffMueller_TraceNorm(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_Core_ExpArith(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_DempwolffMueller_ExpArith(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_DempwolffMueller_FrobAlg(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_DempwolffMueller_Lemma31(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_DempwolffMueller_BareLemma31(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_RequestProject_DempwolffMueller_AdjointBij(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_DempwolffMueller_TraceNorm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_Core_ExpArith(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_DempwolffMueller_ExpArith(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_DempwolffMueller_FrobAlg(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_DempwolffMueller_Lemma31(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_DempwolffMueller_BareLemma31(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
