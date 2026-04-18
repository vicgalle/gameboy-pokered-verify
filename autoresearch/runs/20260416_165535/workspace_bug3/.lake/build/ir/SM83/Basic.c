// Lean compiler output
// Module: SM83.Basic
// Imports: public import Init
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
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_swapNibbles___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_resBit8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_signExtend8to16(lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_resBit8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_lo___boxed(lean_object*);
lean_object* l_BitVec_extractLsb_x27___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_append___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_shiftLeft(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_cast___at___00UInt8_modn_spec__0(lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_swapNibbles(lean_object*);
lean_object* l_BitVec_not(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_testBit8___boxed(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_setBit8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_mk16(lean_object*, lean_object*);
uint8_t l_Nat_testBit(lean_object*, lean_object*);
lean_object* l_BitVec_signExtend(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_hi___boxed(lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_autoresearch_x2dworkspace_SM83_testBit8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_lo(lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_hi(lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_setBit8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_mk16___boxed(lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_hi(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(8u);
x_3 = l_BitVec_extractLsb_x27___redArg(x_2, x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_hi___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_autoresearch_x2dworkspace_SM83_hi(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_lo(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_unsigned_to_nat(8u);
x_4 = l_BitVec_extractLsb_x27___redArg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_lo___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_autoresearch_x2dworkspace_SM83_lo(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_mk16(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(8u);
x_4 = l_BitVec_append___redArg(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_mk16___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_autoresearch_x2dworkspace_SM83_mk16(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_signExtend8to16(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_unsigned_to_nat(16u);
x_4 = l_BitVec_signExtend(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t lp_autoresearch_x2dworkspace_SM83_testBit8(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Nat_testBit(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_testBit8___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lp_autoresearch_x2dworkspace_SM83_testBit8(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_setBit8(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_shiftl(x_3, x_2);
x_5 = l_Nat_cast___at___00UInt8_modn_spec__0(x_4);
lean_dec(x_4);
x_6 = lean_nat_lor(x_1, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_setBit8___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_autoresearch_x2dworkspace_SM83_setBit8(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_resBit8(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_unsigned_to_nat(8u);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_shiftl(x_4, x_2);
x_6 = l_Nat_cast___at___00UInt8_modn_spec__0(x_5);
lean_dec(x_5);
x_7 = l_BitVec_not(x_3, x_6);
lean_dec(x_6);
x_8 = lean_nat_land(x_1, x_7);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_resBit8___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_autoresearch_x2dworkspace_SM83_resBit8(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_swapNibbles(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_unsigned_to_nat(4u);
x_4 = lean_nat_shiftr(x_1, x_3);
x_5 = l_BitVec_shiftLeft(x_2, x_1, x_3);
x_6 = lean_nat_lor(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_swapNibbles___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_autoresearch_x2dworkspace_SM83_swapNibbles(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_autoresearch_x2dworkspace_SM83_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
