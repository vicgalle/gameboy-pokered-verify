// Lean compiler output
// Module: SM83
// Imports: public import Init public import SM83.Basic public import SM83.State public import SM83.Flags public import SM83.Memory public import SM83.Arithmetic public import SM83.Logic public import SM83.Load public import SM83.Control public import SM83.Properties
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
lean_object* initialize_autoresearch_x2dworkspace_SM83_Basic(uint8_t builtin);
lean_object* initialize_autoresearch_x2dworkspace_SM83_State(uint8_t builtin);
lean_object* initialize_autoresearch_x2dworkspace_SM83_Flags(uint8_t builtin);
lean_object* initialize_autoresearch_x2dworkspace_SM83_Memory(uint8_t builtin);
lean_object* initialize_autoresearch_x2dworkspace_SM83_Arithmetic(uint8_t builtin);
lean_object* initialize_autoresearch_x2dworkspace_SM83_Logic(uint8_t builtin);
lean_object* initialize_autoresearch_x2dworkspace_SM83_Load(uint8_t builtin);
lean_object* initialize_autoresearch_x2dworkspace_SM83_Control(uint8_t builtin);
lean_object* initialize_autoresearch_x2dworkspace_SM83_Properties(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_autoresearch_x2dworkspace_SM83(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_autoresearch_x2dworkspace_SM83_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_autoresearch_x2dworkspace_SM83_State(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_autoresearch_x2dworkspace_SM83_Flags(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_autoresearch_x2dworkspace_SM83_Memory(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_autoresearch_x2dworkspace_SM83_Arithmetic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_autoresearch_x2dworkspace_SM83_Logic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_autoresearch_x2dworkspace_SM83_Load(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_autoresearch_x2dworkspace_SM83_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_autoresearch_x2dworkspace_SM83_Properties(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
