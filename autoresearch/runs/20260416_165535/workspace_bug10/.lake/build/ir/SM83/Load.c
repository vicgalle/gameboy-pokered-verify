// Lean compiler output
// Module: SM83.Load
// Imports: public import Init public import SM83.Flags public import SM83.Memory
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
lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_hl(lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_ldBCnn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_ldADE(lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_ldSPnn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_popDE(lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_popAF(lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_pushBC(lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_ldABC(lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_lddAHL(lean_object*);
lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_bc(lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_ldiAHL(lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_pushDE(lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_ldDEA(lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_ldiHLA(lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_ldnnA(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_ldHLA(lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_pushHL(lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_ldAnn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_ldBCnn___boxed(lean_object*, lean_object*);
lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_pushStack(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_popHL(lean_object*);
lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_writeMem(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_ldDEnn___boxed(lean_object*, lean_object*);
lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_setBC(lean_object*, lean_object*);
lean_object* l_BitVec_add(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_ldDEnn(lean_object*, lean_object*);
static lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_ldiHLA___closed__0;
lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_popStack(lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_pushAF(lean_object*);
lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_setDE(lean_object*, lean_object*);
static lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_popAF___closed__0;
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_popBC(lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_ldHLnn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_ldHLnn(lean_object*, lean_object*);
lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_de(lean_object*);
lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_setHL(lean_object*, lean_object*);
lean_object* lp_autoresearch_x2dworkspace_SM83_lo(lean_object*);
lean_object* lp_autoresearch_x2dworkspace_SM83_hi(lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_ldHLr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_ldBCA(lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_ldAHL(lean_object*);
lean_object* l_BitVec_sub(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_lddHLA(lean_object*);
lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_af(lean_object*);
lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_readMem(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_ldAHL(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 4);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 5);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 6);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 7);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 8);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 9);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 10);
lean_inc_ref(x_11);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*11);
x_13 = lp_autoresearch_x2dworkspace_SM83_CPUState_hl(x_1);
x_14 = lp_autoresearch_x2dworkspace_SM83_CPUState_readMem(x_1, x_13);
x_15 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_15, 2, x_3);
lean_ctor_set(x_15, 3, x_4);
lean_ctor_set(x_15, 4, x_5);
lean_ctor_set(x_15, 5, x_6);
lean_ctor_set(x_15, 6, x_7);
lean_ctor_set(x_15, 7, x_8);
lean_ctor_set(x_15, 8, x_9);
lean_ctor_set(x_15, 9, x_10);
lean_ctor_set(x_15, 10, x_11);
lean_ctor_set_uint8(x_15, sizeof(void*)*11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_ldHLA(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lp_autoresearch_x2dworkspace_SM83_CPUState_hl(x_1);
x_4 = lp_autoresearch_x2dworkspace_SM83_CPUState_writeMem(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_ldHLr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lp_autoresearch_x2dworkspace_SM83_CPUState_hl(x_1);
x_4 = lp_autoresearch_x2dworkspace_SM83_CPUState_writeMem(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_ldAnn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 4);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 5);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 6);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 7);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 8);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 9);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 10);
lean_inc_ref(x_12);
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*11);
x_14 = lp_autoresearch_x2dworkspace_SM83_CPUState_readMem(x_1, x_2);
x_15 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set(x_15, 2, x_4);
lean_ctor_set(x_15, 3, x_5);
lean_ctor_set(x_15, 4, x_6);
lean_ctor_set(x_15, 5, x_7);
lean_ctor_set(x_15, 6, x_8);
lean_ctor_set(x_15, 7, x_9);
lean_ctor_set(x_15, 8, x_10);
lean_ctor_set(x_15, 9, x_11);
lean_ctor_set(x_15, 10, x_12);
lean_ctor_set_uint8(x_15, sizeof(void*)*11, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_ldnnA(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lp_autoresearch_x2dworkspace_SM83_CPUState_writeMem(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_ldABC(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 4);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 5);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 6);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 7);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 8);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 9);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 10);
lean_inc_ref(x_11);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*11);
x_13 = lp_autoresearch_x2dworkspace_SM83_CPUState_bc(x_1);
x_14 = lp_autoresearch_x2dworkspace_SM83_CPUState_readMem(x_1, x_13);
x_15 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_15, 2, x_3);
lean_ctor_set(x_15, 3, x_4);
lean_ctor_set(x_15, 4, x_5);
lean_ctor_set(x_15, 5, x_6);
lean_ctor_set(x_15, 6, x_7);
lean_ctor_set(x_15, 7, x_8);
lean_ctor_set(x_15, 8, x_9);
lean_ctor_set(x_15, 9, x_10);
lean_ctor_set(x_15, 10, x_11);
lean_ctor_set_uint8(x_15, sizeof(void*)*11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_ldADE(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 4);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 5);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 6);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 7);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 8);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 9);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 10);
lean_inc_ref(x_11);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*11);
x_13 = lp_autoresearch_x2dworkspace_SM83_CPUState_de(x_1);
x_14 = lp_autoresearch_x2dworkspace_SM83_CPUState_readMem(x_1, x_13);
x_15 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_15, 2, x_3);
lean_ctor_set(x_15, 3, x_4);
lean_ctor_set(x_15, 4, x_5);
lean_ctor_set(x_15, 5, x_6);
lean_ctor_set(x_15, 6, x_7);
lean_ctor_set(x_15, 7, x_8);
lean_ctor_set(x_15, 8, x_9);
lean_ctor_set(x_15, 9, x_10);
lean_ctor_set(x_15, 10, x_11);
lean_ctor_set_uint8(x_15, sizeof(void*)*11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_ldBCA(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lp_autoresearch_x2dworkspace_SM83_CPUState_bc(x_1);
x_4 = lp_autoresearch_x2dworkspace_SM83_CPUState_writeMem(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_ldDEA(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lp_autoresearch_x2dworkspace_SM83_CPUState_de(x_1);
x_4 = lp_autoresearch_x2dworkspace_SM83_CPUState_writeMem(x_1, x_3, x_2);
return x_4;
}
}
static lean_object* _init_lp_autoresearch_x2dworkspace_SM83_CPUState_ldiHLA___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_unsigned_to_nat(16u);
x_3 = l_BitVec_ofNat(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_ldiHLA(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lp_autoresearch_x2dworkspace_SM83_CPUState_hl(x_1);
x_4 = lp_autoresearch_x2dworkspace_SM83_CPUState_writeMem(x_1, x_3, x_2);
x_5 = lean_unsigned_to_nat(16u);
x_6 = lp_autoresearch_x2dworkspace_SM83_CPUState_hl(x_4);
x_7 = lp_autoresearch_x2dworkspace_SM83_CPUState_ldiHLA___closed__0;
x_8 = l_BitVec_add(x_5, x_6, x_7);
lean_dec(x_6);
x_9 = lp_autoresearch_x2dworkspace_SM83_CPUState_setHL(x_4, x_8);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_lddHLA(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lp_autoresearch_x2dworkspace_SM83_CPUState_hl(x_1);
x_4 = lp_autoresearch_x2dworkspace_SM83_CPUState_writeMem(x_1, x_3, x_2);
x_5 = lean_unsigned_to_nat(16u);
x_6 = lp_autoresearch_x2dworkspace_SM83_CPUState_hl(x_4);
x_7 = lp_autoresearch_x2dworkspace_SM83_CPUState_ldiHLA___closed__0;
x_8 = l_BitVec_sub(x_5, x_6, x_7);
lean_dec(x_6);
x_9 = lp_autoresearch_x2dworkspace_SM83_CPUState_setHL(x_4, x_8);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_ldiAHL(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 4);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 5);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 6);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 7);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 8);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 9);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 10);
lean_inc_ref(x_11);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*11);
x_13 = lp_autoresearch_x2dworkspace_SM83_CPUState_hl(x_1);
x_14 = lp_autoresearch_x2dworkspace_SM83_CPUState_readMem(x_1, x_13);
x_15 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_15, 2, x_3);
lean_ctor_set(x_15, 3, x_4);
lean_ctor_set(x_15, 4, x_5);
lean_ctor_set(x_15, 5, x_6);
lean_ctor_set(x_15, 6, x_7);
lean_ctor_set(x_15, 7, x_8);
lean_ctor_set(x_15, 8, x_9);
lean_ctor_set(x_15, 9, x_10);
lean_ctor_set(x_15, 10, x_11);
lean_ctor_set_uint8(x_15, sizeof(void*)*11, x_12);
x_16 = lean_unsigned_to_nat(16u);
x_17 = lp_autoresearch_x2dworkspace_SM83_CPUState_hl(x_15);
x_18 = lp_autoresearch_x2dworkspace_SM83_CPUState_ldiHLA___closed__0;
x_19 = l_BitVec_add(x_16, x_17, x_18);
lean_dec(x_17);
x_20 = lp_autoresearch_x2dworkspace_SM83_CPUState_setHL(x_15, x_19);
lean_dec(x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_lddAHL(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 4);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 5);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 6);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 7);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 8);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 9);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 10);
lean_inc_ref(x_11);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*11);
x_13 = lp_autoresearch_x2dworkspace_SM83_CPUState_hl(x_1);
x_14 = lp_autoresearch_x2dworkspace_SM83_CPUState_readMem(x_1, x_13);
x_15 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_15, 2, x_3);
lean_ctor_set(x_15, 3, x_4);
lean_ctor_set(x_15, 4, x_5);
lean_ctor_set(x_15, 5, x_6);
lean_ctor_set(x_15, 6, x_7);
lean_ctor_set(x_15, 7, x_8);
lean_ctor_set(x_15, 8, x_9);
lean_ctor_set(x_15, 9, x_10);
lean_ctor_set(x_15, 10, x_11);
lean_ctor_set_uint8(x_15, sizeof(void*)*11, x_12);
x_16 = lean_unsigned_to_nat(16u);
x_17 = lp_autoresearch_x2dworkspace_SM83_CPUState_hl(x_15);
x_18 = lp_autoresearch_x2dworkspace_SM83_CPUState_ldiHLA___closed__0;
x_19 = l_BitVec_sub(x_16, x_17, x_18);
lean_dec(x_17);
x_20 = lp_autoresearch_x2dworkspace_SM83_CPUState_setHL(x_15, x_19);
lean_dec(x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_ldBCnn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_autoresearch_x2dworkspace_SM83_CPUState_setBC(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_ldBCnn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_autoresearch_x2dworkspace_SM83_CPUState_ldBCnn(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_ldDEnn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_autoresearch_x2dworkspace_SM83_CPUState_setDE(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_ldDEnn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_autoresearch_x2dworkspace_SM83_CPUState_ldDEnn(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_ldHLnn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_autoresearch_x2dworkspace_SM83_CPUState_setHL(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_ldHLnn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_autoresearch_x2dworkspace_SM83_CPUState_ldHLnn(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_ldSPnn(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 8);
lean_dec(x_4);
lean_ctor_set(x_1, 8, x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_ctor_get(x_1, 3);
x_9 = lean_ctor_get(x_1, 4);
x_10 = lean_ctor_get(x_1, 5);
x_11 = lean_ctor_get(x_1, 6);
x_12 = lean_ctor_get(x_1, 7);
x_13 = lean_ctor_get(x_1, 9);
x_14 = lean_ctor_get(x_1, 10);
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*11);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_6);
lean_ctor_set(x_16, 2, x_7);
lean_ctor_set(x_16, 3, x_8);
lean_ctor_set(x_16, 4, x_9);
lean_ctor_set(x_16, 5, x_10);
lean_ctor_set(x_16, 6, x_11);
lean_ctor_set(x_16, 7, x_12);
lean_ctor_set(x_16, 8, x_2);
lean_ctor_set(x_16, 9, x_13);
lean_ctor_set(x_16, 10, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*11, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_pushBC(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lp_autoresearch_x2dworkspace_SM83_CPUState_bc(x_1);
x_3 = lp_autoresearch_x2dworkspace_SM83_CPUState_pushStack(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_pushDE(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lp_autoresearch_x2dworkspace_SM83_CPUState_de(x_1);
x_3 = lp_autoresearch_x2dworkspace_SM83_CPUState_pushStack(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_pushHL(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lp_autoresearch_x2dworkspace_SM83_CPUState_hl(x_1);
x_3 = lp_autoresearch_x2dworkspace_SM83_CPUState_pushStack(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_pushAF(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lp_autoresearch_x2dworkspace_SM83_CPUState_af(x_1);
x_3 = lp_autoresearch_x2dworkspace_SM83_CPUState_pushStack(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_popBC(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lp_autoresearch_x2dworkspace_SM83_CPUState_popStack(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lp_autoresearch_x2dworkspace_SM83_CPUState_setBC(x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_popDE(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lp_autoresearch_x2dworkspace_SM83_CPUState_popStack(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lp_autoresearch_x2dworkspace_SM83_CPUState_setDE(x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_popHL(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lp_autoresearch_x2dworkspace_SM83_CPUState_popStack(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lp_autoresearch_x2dworkspace_SM83_CPUState_setHL(x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
static lean_object* _init_lp_autoresearch_x2dworkspace_SM83_CPUState_popAF___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(240u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = l_BitVec_ofNat(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_popAF(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lp_autoresearch_x2dworkspace_SM83_CPUState_popStack(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_3, 1);
lean_dec(x_6);
x_7 = lean_ctor_get(x_3, 0);
lean_dec(x_7);
x_8 = lp_autoresearch_x2dworkspace_SM83_hi(x_4);
x_9 = lp_autoresearch_x2dworkspace_SM83_lo(x_4);
lean_dec(x_4);
x_10 = lp_autoresearch_x2dworkspace_SM83_CPUState_popAF___closed__0;
x_11 = lean_nat_land(x_9, x_10);
lean_dec(x_9);
lean_ctor_set(x_3, 1, x_11);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_12 = lean_ctor_get(x_3, 2);
x_13 = lean_ctor_get(x_3, 3);
x_14 = lean_ctor_get(x_3, 4);
x_15 = lean_ctor_get(x_3, 5);
x_16 = lean_ctor_get(x_3, 6);
x_17 = lean_ctor_get(x_3, 7);
x_18 = lean_ctor_get(x_3, 8);
x_19 = lean_ctor_get(x_3, 9);
x_20 = lean_ctor_get(x_3, 10);
x_21 = lean_ctor_get_uint8(x_3, sizeof(void*)*11);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_22 = lp_autoresearch_x2dworkspace_SM83_hi(x_4);
x_23 = lp_autoresearch_x2dworkspace_SM83_lo(x_4);
lean_dec(x_4);
x_24 = lp_autoresearch_x2dworkspace_SM83_CPUState_popAF___closed__0;
x_25 = lean_nat_land(x_23, x_24);
lean_dec(x_23);
x_26 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_12);
lean_ctor_set(x_26, 3, x_13);
lean_ctor_set(x_26, 4, x_14);
lean_ctor_set(x_26, 5, x_15);
lean_ctor_set(x_26, 6, x_16);
lean_ctor_set(x_26, 7, x_17);
lean_ctor_set(x_26, 8, x_18);
lean_ctor_set(x_26, 9, x_19);
lean_ctor_set(x_26, 10, x_20);
lean_ctor_set_uint8(x_26, sizeof(void*)*11, x_21);
return x_26;
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_autoresearch_x2dworkspace_SM83_Flags(uint8_t builtin);
lean_object* initialize_autoresearch_x2dworkspace_SM83_Memory(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_autoresearch_x2dworkspace_SM83_Load(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_autoresearch_x2dworkspace_SM83_Flags(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_autoresearch_x2dworkspace_SM83_Memory(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_autoresearch_x2dworkspace_SM83_CPUState_ldiHLA___closed__0 = _init_lp_autoresearch_x2dworkspace_SM83_CPUState_ldiHLA___closed__0();
lean_mark_persistent(lp_autoresearch_x2dworkspace_SM83_CPUState_ldiHLA___closed__0);
lp_autoresearch_x2dworkspace_SM83_CPUState_popAF___closed__0 = _init_lp_autoresearch_x2dworkspace_SM83_CPUState_popAF___closed__0();
lean_mark_persistent(lp_autoresearch_x2dworkspace_SM83_CPUState_popAF___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
