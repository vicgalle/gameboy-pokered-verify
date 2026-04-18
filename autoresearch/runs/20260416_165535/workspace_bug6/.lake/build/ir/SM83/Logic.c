// Lean compiler output
// Module: SM83.Logic
// Imports: public import Init public import SM83.Flags public import SM83.Basic
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
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execAnd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execRlca(lean_object*);
static lean_object* lp_autoresearch_x2dworkspace_SM83_execAnd___closed__0;
lean_object* lp_autoresearch_x2dworkspace_SM83_resBit8(lean_object*, lean_object*);
uint8_t lp_autoresearch_x2dworkspace_SM83_CPUState_cFlag(lean_object*);
static lean_object* lp_autoresearch_x2dworkspace_SM83_execSra___closed__0;
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execSwap(lean_object*);
uint8_t lp_autoresearch_x2dworkspace_SM83_CPUState_zFlag(lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execCcf(lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execRla(lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execRes___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execScf(lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execBit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execRrca(lean_object*);
lean_object* lp_autoresearch_x2dworkspace_SM83_mkFlags(uint8_t, uint8_t, uint8_t, uint8_t);
lean_object* l_BitVec_shiftLeft(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execRra(lean_object*);
lean_object* lp_autoresearch_x2dworkspace_SM83_swapNibbles(lean_object*);
lean_object* l_BitVec_not(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execSrl___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execSet(lean_object*, lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execOr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execXor___boxed(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execSra___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execXor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execSwap___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execSla___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execSrl(lean_object*);
static lean_object* lp_autoresearch_x2dworkspace_SM83_execRlca___closed__0;
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execRes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execCcf___boxed(lean_object*);
lean_object* lean_nat_lxor(lean_object*, lean_object*);
uint8_t l_Nat_testBit(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execSra(lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execCpl(lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execBit___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execSet___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execAnd___boxed(lean_object*, lean_object*);
lean_object* lp_autoresearch_x2dworkspace_SM83_setBit8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execOr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execSla(lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
static lean_object* _init_lp_autoresearch_x2dworkspace_SM83_execAnd___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = l_BitVec_ofNat(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execAnd(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
lean_dec(x_5);
x_6 = lean_nat_land(x_4, x_2);
lean_dec(x_4);
x_7 = lp_autoresearch_x2dworkspace_SM83_execAnd___closed__0;
x_8 = lean_nat_dec_eq(x_6, x_7);
x_9 = 0;
x_10 = 1;
x_11 = lp_autoresearch_x2dworkspace_SM83_mkFlags(x_8, x_9, x_10, x_9);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 2);
x_14 = lean_ctor_get(x_1, 3);
x_15 = lean_ctor_get(x_1, 4);
x_16 = lean_ctor_get(x_1, 5);
x_17 = lean_ctor_get(x_1, 6);
x_18 = lean_ctor_get(x_1, 7);
x_19 = lean_ctor_get(x_1, 8);
x_20 = lean_ctor_get(x_1, 9);
x_21 = lean_ctor_get(x_1, 10);
x_22 = lean_ctor_get_uint8(x_1, sizeof(void*)*11);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_23 = lean_nat_land(x_12, x_2);
lean_dec(x_12);
x_24 = lp_autoresearch_x2dworkspace_SM83_execAnd___closed__0;
x_25 = lean_nat_dec_eq(x_23, x_24);
x_26 = 0;
x_27 = 1;
x_28 = lp_autoresearch_x2dworkspace_SM83_mkFlags(x_25, x_26, x_27, x_26);
x_29 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_13);
lean_ctor_set(x_29, 3, x_14);
lean_ctor_set(x_29, 4, x_15);
lean_ctor_set(x_29, 5, x_16);
lean_ctor_set(x_29, 6, x_17);
lean_ctor_set(x_29, 7, x_18);
lean_ctor_set(x_29, 8, x_19);
lean_ctor_set(x_29, 9, x_20);
lean_ctor_set(x_29, 10, x_21);
lean_ctor_set_uint8(x_29, sizeof(void*)*11, x_22);
return x_29;
}
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execAnd___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_autoresearch_x2dworkspace_SM83_execAnd(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execOr(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
lean_dec(x_5);
x_6 = lean_nat_lor(x_4, x_2);
lean_dec(x_4);
x_7 = lp_autoresearch_x2dworkspace_SM83_execAnd___closed__0;
x_8 = lean_nat_dec_eq(x_6, x_7);
x_9 = 0;
x_10 = lp_autoresearch_x2dworkspace_SM83_mkFlags(x_8, x_9, x_9, x_9);
lean_ctor_set(x_1, 1, x_10);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 2);
x_13 = lean_ctor_get(x_1, 3);
x_14 = lean_ctor_get(x_1, 4);
x_15 = lean_ctor_get(x_1, 5);
x_16 = lean_ctor_get(x_1, 6);
x_17 = lean_ctor_get(x_1, 7);
x_18 = lean_ctor_get(x_1, 8);
x_19 = lean_ctor_get(x_1, 9);
x_20 = lean_ctor_get(x_1, 10);
x_21 = lean_ctor_get_uint8(x_1, sizeof(void*)*11);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_1);
x_22 = lean_nat_lor(x_11, x_2);
lean_dec(x_11);
x_23 = lp_autoresearch_x2dworkspace_SM83_execAnd___closed__0;
x_24 = lean_nat_dec_eq(x_22, x_23);
x_25 = 0;
x_26 = lp_autoresearch_x2dworkspace_SM83_mkFlags(x_24, x_25, x_25, x_25);
x_27 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_12);
lean_ctor_set(x_27, 3, x_13);
lean_ctor_set(x_27, 4, x_14);
lean_ctor_set(x_27, 5, x_15);
lean_ctor_set(x_27, 6, x_16);
lean_ctor_set(x_27, 7, x_17);
lean_ctor_set(x_27, 8, x_18);
lean_ctor_set(x_27, 9, x_19);
lean_ctor_set(x_27, 10, x_20);
lean_ctor_set_uint8(x_27, sizeof(void*)*11, x_21);
return x_27;
}
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execOr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_autoresearch_x2dworkspace_SM83_execOr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execXor(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
lean_dec(x_5);
x_6 = lean_nat_lxor(x_4, x_2);
lean_dec(x_4);
x_7 = lp_autoresearch_x2dworkspace_SM83_execAnd___closed__0;
x_8 = lean_nat_dec_eq(x_6, x_7);
x_9 = 0;
x_10 = lp_autoresearch_x2dworkspace_SM83_mkFlags(x_8, x_9, x_9, x_9);
lean_ctor_set(x_1, 1, x_10);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 2);
x_13 = lean_ctor_get(x_1, 3);
x_14 = lean_ctor_get(x_1, 4);
x_15 = lean_ctor_get(x_1, 5);
x_16 = lean_ctor_get(x_1, 6);
x_17 = lean_ctor_get(x_1, 7);
x_18 = lean_ctor_get(x_1, 8);
x_19 = lean_ctor_get(x_1, 9);
x_20 = lean_ctor_get(x_1, 10);
x_21 = lean_ctor_get_uint8(x_1, sizeof(void*)*11);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_1);
x_22 = lean_nat_lxor(x_11, x_2);
lean_dec(x_11);
x_23 = lp_autoresearch_x2dworkspace_SM83_execAnd___closed__0;
x_24 = lean_nat_dec_eq(x_22, x_23);
x_25 = 0;
x_26 = lp_autoresearch_x2dworkspace_SM83_mkFlags(x_24, x_25, x_25, x_25);
x_27 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_12);
lean_ctor_set(x_27, 3, x_13);
lean_ctor_set(x_27, 4, x_14);
lean_ctor_set(x_27, 5, x_15);
lean_ctor_set(x_27, 6, x_16);
lean_ctor_set(x_27, 7, x_17);
lean_ctor_set(x_27, 8, x_18);
lean_ctor_set(x_27, 9, x_19);
lean_ctor_set(x_27, 10, x_20);
lean_ctor_set_uint8(x_27, sizeof(void*)*11, x_21);
return x_27;
}
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execXor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_autoresearch_x2dworkspace_SM83_execXor(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execCpl(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; 
x_2 = lean_ctor_get(x_1, 0);
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
x_13 = lp_autoresearch_x2dworkspace_SM83_CPUState_cFlag(x_1);
x_14 = lp_autoresearch_x2dworkspace_SM83_CPUState_zFlag(x_1);
x_15 = !lean_is_exclusive(x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_16 = lean_ctor_get(x_1, 10);
lean_dec(x_16);
x_17 = lean_ctor_get(x_1, 9);
lean_dec(x_17);
x_18 = lean_ctor_get(x_1, 8);
lean_dec(x_18);
x_19 = lean_ctor_get(x_1, 7);
lean_dec(x_19);
x_20 = lean_ctor_get(x_1, 6);
lean_dec(x_20);
x_21 = lean_ctor_get(x_1, 5);
lean_dec(x_21);
x_22 = lean_ctor_get(x_1, 4);
lean_dec(x_22);
x_23 = lean_ctor_get(x_1, 3);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 2);
lean_dec(x_24);
x_25 = lean_ctor_get(x_1, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_1, 0);
lean_dec(x_26);
x_27 = lean_unsigned_to_nat(8u);
x_28 = l_BitVec_not(x_27, x_2);
lean_dec(x_2);
x_29 = 1;
x_30 = lp_autoresearch_x2dworkspace_SM83_mkFlags(x_14, x_29, x_29, x_13);
lean_ctor_set(x_1, 1, x_30);
lean_ctor_set(x_1, 0, x_28);
return x_1;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_1);
x_31 = lean_unsigned_to_nat(8u);
x_32 = l_BitVec_not(x_31, x_2);
lean_dec(x_2);
x_33 = 1;
x_34 = lp_autoresearch_x2dworkspace_SM83_mkFlags(x_14, x_33, x_33, x_13);
x_35 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_3);
lean_ctor_set(x_35, 3, x_4);
lean_ctor_set(x_35, 4, x_5);
lean_ctor_set(x_35, 5, x_6);
lean_ctor_set(x_35, 6, x_7);
lean_ctor_set(x_35, 7, x_8);
lean_ctor_set(x_35, 8, x_9);
lean_ctor_set(x_35, 9, x_10);
lean_ctor_set(x_35, 10, x_11);
lean_ctor_set_uint8(x_35, sizeof(void*)*11, x_12);
return x_35;
}
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execSrl(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Nat_testBit(x_1, x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_shiftr(x_1, x_4);
x_6 = lp_autoresearch_x2dworkspace_SM83_execAnd___closed__0;
x_7 = lean_nat_dec_eq(x_5, x_6);
x_8 = 0;
x_9 = lp_autoresearch_x2dworkspace_SM83_mkFlags(x_7, x_8, x_8, x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execSrl___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_autoresearch_x2dworkspace_SM83_execSrl(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execSla(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_unsigned_to_nat(7u);
x_4 = l_Nat_testBit(x_1, x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_BitVec_shiftLeft(x_2, x_1, x_5);
x_7 = lp_autoresearch_x2dworkspace_SM83_execAnd___closed__0;
x_8 = lean_nat_dec_eq(x_6, x_7);
x_9 = 0;
x_10 = lp_autoresearch_x2dworkspace_SM83_mkFlags(x_8, x_9, x_9, x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execSla___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_autoresearch_x2dworkspace_SM83_execSla(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_lp_autoresearch_x2dworkspace_SM83_execSra___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(128u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = l_BitVec_ofNat(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execSra(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Nat_testBit(x_1, x_2);
x_4 = lp_autoresearch_x2dworkspace_SM83_execSra___closed__0;
x_5 = lean_nat_land(x_1, x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_shiftr(x_1, x_6);
x_8 = lean_nat_lor(x_7, x_5);
lean_dec(x_5);
lean_dec(x_7);
x_9 = lp_autoresearch_x2dworkspace_SM83_execAnd___closed__0;
x_10 = lean_nat_dec_eq(x_8, x_9);
x_11 = 0;
x_12 = lp_autoresearch_x2dworkspace_SM83_mkFlags(x_10, x_11, x_11, x_3);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execSra___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_autoresearch_x2dworkspace_SM83_execSra(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execSwap(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lp_autoresearch_x2dworkspace_SM83_swapNibbles(x_1);
x_3 = lp_autoresearch_x2dworkspace_SM83_execAnd___closed__0;
x_4 = lean_nat_dec_eq(x_2, x_3);
x_5 = 0;
x_6 = lp_autoresearch_x2dworkspace_SM83_mkFlags(x_4, x_5, x_5, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execSwap___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_autoresearch_x2dworkspace_SM83_execSwap(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_lp_autoresearch_x2dworkspace_SM83_execRlca___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = l_BitVec_ofNat(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execRlca(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_2 = lean_ctor_get(x_1, 0);
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
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 lean_ctor_release(x_1, 7);
 lean_ctor_release(x_1, 8);
 lean_ctor_release(x_1, 9);
 lean_ctor_release(x_1, 10);
 x_13 = x_1;
} else {
 lean_dec_ref(x_1);
 x_13 = lean_box(0);
}
x_14 = lean_unsigned_to_nat(8u);
x_15 = lean_unsigned_to_nat(7u);
x_16 = l_Nat_testBit(x_2, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_BitVec_shiftLeft(x_14, x_2, x_17);
lean_dec(x_2);
if (x_16 == 0)
{
lean_object* x_25; 
x_25 = lp_autoresearch_x2dworkspace_SM83_execAnd___closed__0;
x_19 = x_25;
goto block_24;
}
else
{
lean_object* x_26; 
x_26 = lp_autoresearch_x2dworkspace_SM83_execRlca___closed__0;
x_19 = x_26;
goto block_24;
}
block_24:
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_nat_lor(x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
x_21 = 0;
x_22 = lp_autoresearch_x2dworkspace_SM83_mkFlags(x_21, x_21, x_21, x_16);
if (lean_is_scalar(x_13)) {
 x_23 = lean_alloc_ctor(0, 11, 1);
} else {
 x_23 = x_13;
}
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_3);
lean_ctor_set(x_23, 3, x_4);
lean_ctor_set(x_23, 4, x_5);
lean_ctor_set(x_23, 5, x_6);
lean_ctor_set(x_23, 6, x_7);
lean_ctor_set(x_23, 7, x_8);
lean_ctor_set(x_23, 8, x_9);
lean_ctor_set(x_23, 9, x_10);
lean_ctor_set(x_23, 10, x_11);
lean_ctor_set_uint8(x_23, sizeof(void*)*11, x_12);
return x_23;
}
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execRrca(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_2 = lean_ctor_get(x_1, 0);
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
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 lean_ctor_release(x_1, 7);
 lean_ctor_release(x_1, 8);
 lean_ctor_release(x_1, 9);
 lean_ctor_release(x_1, 10);
 x_13 = x_1;
} else {
 lean_dec_ref(x_1);
 x_13 = lean_box(0);
}
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Nat_testBit(x_2, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_shiftr(x_2, x_16);
lean_dec(x_2);
if (x_15 == 0)
{
lean_object* x_24; 
x_24 = lp_autoresearch_x2dworkspace_SM83_execAnd___closed__0;
x_18 = x_24;
goto block_23;
}
else
{
lean_object* x_25; 
x_25 = lp_autoresearch_x2dworkspace_SM83_execSra___closed__0;
x_18 = x_25;
goto block_23;
}
block_23:
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_nat_lor(x_17, x_18);
lean_dec(x_18);
lean_dec(x_17);
x_20 = 0;
x_21 = lp_autoresearch_x2dworkspace_SM83_mkFlags(x_20, x_20, x_20, x_15);
if (lean_is_scalar(x_13)) {
 x_22 = lean_alloc_ctor(0, 11, 1);
} else {
 x_22 = x_13;
}
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_3);
lean_ctor_set(x_22, 3, x_4);
lean_ctor_set(x_22, 4, x_5);
lean_ctor_set(x_22, 5, x_6);
lean_ctor_set(x_22, 6, x_7);
lean_ctor_set(x_22, 7, x_8);
lean_ctor_set(x_22, 8, x_9);
lean_ctor_set(x_22, 9, x_10);
lean_ctor_set(x_22, 10, x_11);
lean_ctor_set_uint8(x_22, sizeof(void*)*11, x_12);
return x_22;
}
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execRla(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_ctor_get(x_1, 0);
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
x_13 = lp_autoresearch_x2dworkspace_SM83_CPUState_cFlag(x_1);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 lean_ctor_release(x_1, 7);
 lean_ctor_release(x_1, 8);
 lean_ctor_release(x_1, 9);
 lean_ctor_release(x_1, 10);
 x_14 = x_1;
} else {
 lean_dec_ref(x_1);
 x_14 = lean_box(0);
}
x_15 = lean_unsigned_to_nat(8u);
x_16 = lean_unsigned_to_nat(7u);
x_17 = l_Nat_testBit(x_2, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_BitVec_shiftLeft(x_15, x_2, x_18);
lean_dec(x_2);
if (x_13 == 0)
{
lean_object* x_26; 
x_26 = lp_autoresearch_x2dworkspace_SM83_execAnd___closed__0;
x_20 = x_26;
goto block_25;
}
else
{
lean_object* x_27; 
x_27 = lp_autoresearch_x2dworkspace_SM83_execRlca___closed__0;
x_20 = x_27;
goto block_25;
}
block_25:
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_nat_lor(x_19, x_20);
lean_dec(x_20);
lean_dec(x_19);
x_22 = 0;
x_23 = lp_autoresearch_x2dworkspace_SM83_mkFlags(x_22, x_22, x_22, x_17);
if (lean_is_scalar(x_14)) {
 x_24 = lean_alloc_ctor(0, 11, 1);
} else {
 x_24 = x_14;
}
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_3);
lean_ctor_set(x_24, 3, x_4);
lean_ctor_set(x_24, 4, x_5);
lean_ctor_set(x_24, 5, x_6);
lean_ctor_set(x_24, 6, x_7);
lean_ctor_set(x_24, 7, x_8);
lean_ctor_set(x_24, 8, x_9);
lean_ctor_set(x_24, 9, x_10);
lean_ctor_set(x_24, 10, x_11);
lean_ctor_set_uint8(x_24, sizeof(void*)*11, x_12);
return x_24;
}
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execRra(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_2 = lean_ctor_get(x_1, 0);
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
x_13 = lp_autoresearch_x2dworkspace_SM83_CPUState_cFlag(x_1);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 lean_ctor_release(x_1, 7);
 lean_ctor_release(x_1, 8);
 lean_ctor_release(x_1, 9);
 lean_ctor_release(x_1, 10);
 x_14 = x_1;
} else {
 lean_dec_ref(x_1);
 x_14 = lean_box(0);
}
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Nat_testBit(x_2, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_shiftr(x_2, x_17);
lean_dec(x_2);
if (x_13 == 0)
{
lean_object* x_25; 
x_25 = lp_autoresearch_x2dworkspace_SM83_execAnd___closed__0;
x_19 = x_25;
goto block_24;
}
else
{
lean_object* x_26; 
x_26 = lp_autoresearch_x2dworkspace_SM83_execSra___closed__0;
x_19 = x_26;
goto block_24;
}
block_24:
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_nat_lor(x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
x_21 = 0;
x_22 = lp_autoresearch_x2dworkspace_SM83_mkFlags(x_21, x_21, x_21, x_16);
if (lean_is_scalar(x_14)) {
 x_23 = lean_alloc_ctor(0, 11, 1);
} else {
 x_23 = x_14;
}
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_3);
lean_ctor_set(x_23, 3, x_4);
lean_ctor_set(x_23, 4, x_5);
lean_ctor_set(x_23, 5, x_6);
lean_ctor_set(x_23, 6, x_7);
lean_ctor_set(x_23, 7, x_8);
lean_ctor_set(x_23, 8, x_9);
lean_ctor_set(x_23, 9, x_10);
lean_ctor_set(x_23, 10, x_11);
lean_ctor_set_uint8(x_23, sizeof(void*)*11, x_12);
return x_23;
}
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execBit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_11; 
x_11 = l_Nat_testBit(x_2, x_1);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = 1;
x_4 = x_12;
goto block_10;
}
else
{
uint8_t x_13; 
x_13 = 0;
x_4 = x_13;
goto block_10;
}
block_10:
{
lean_object* x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_unsigned_to_nat(4u);
x_6 = l_Nat_testBit(x_3, x_5);
x_7 = 0;
x_8 = 1;
x_9 = lp_autoresearch_x2dworkspace_SM83_mkFlags(x_4, x_7, x_8, x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execBit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_autoresearch_x2dworkspace_SM83_execBit(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execSet(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_autoresearch_x2dworkspace_SM83_setBit8(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execSet___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_autoresearch_x2dworkspace_SM83_execSet(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execRes(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_autoresearch_x2dworkspace_SM83_resBit8(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execRes___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_autoresearch_x2dworkspace_SM83_execRes(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execScf(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; 
x_2 = lean_ctor_get(x_1, 0);
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
x_13 = lp_autoresearch_x2dworkspace_SM83_CPUState_zFlag(x_1);
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; 
x_15 = lean_ctor_get(x_1, 10);
lean_dec(x_15);
x_16 = lean_ctor_get(x_1, 9);
lean_dec(x_16);
x_17 = lean_ctor_get(x_1, 8);
lean_dec(x_17);
x_18 = lean_ctor_get(x_1, 7);
lean_dec(x_18);
x_19 = lean_ctor_get(x_1, 6);
lean_dec(x_19);
x_20 = lean_ctor_get(x_1, 5);
lean_dec(x_20);
x_21 = lean_ctor_get(x_1, 4);
lean_dec(x_21);
x_22 = lean_ctor_get(x_1, 3);
lean_dec(x_22);
x_23 = lean_ctor_get(x_1, 2);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 1);
lean_dec(x_24);
x_25 = lean_ctor_get(x_1, 0);
lean_dec(x_25);
x_26 = 0;
x_27 = 1;
x_28 = lp_autoresearch_x2dworkspace_SM83_mkFlags(x_13, x_26, x_26, x_27);
lean_ctor_set(x_1, 1, x_28);
return x_1;
}
else
{
uint8_t x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_1);
x_29 = 0;
x_30 = 1;
x_31 = lp_autoresearch_x2dworkspace_SM83_mkFlags(x_13, x_29, x_29, x_30);
x_32 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_3);
lean_ctor_set(x_32, 3, x_4);
lean_ctor_set(x_32, 4, x_5);
lean_ctor_set(x_32, 5, x_6);
lean_ctor_set(x_32, 6, x_7);
lean_ctor_set(x_32, 7, x_8);
lean_ctor_set(x_32, 8, x_9);
lean_ctor_set(x_32, 9, x_10);
lean_ctor_set(x_32, 10, x_11);
lean_ctor_set_uint8(x_32, sizeof(void*)*11, x_12);
return x_32;
}
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execCcf(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_19; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_ctor_get(x_1, 3);
x_5 = lean_ctor_get(x_1, 4);
x_6 = lean_ctor_get(x_1, 5);
x_7 = lean_ctor_get(x_1, 6);
x_8 = lean_ctor_get(x_1, 7);
x_9 = lean_ctor_get(x_1, 8);
x_10 = lean_ctor_get(x_1, 9);
x_11 = lean_ctor_get(x_1, 10);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*11);
x_13 = lp_autoresearch_x2dworkspace_SM83_CPUState_zFlag(x_1);
x_14 = 0;
x_19 = lp_autoresearch_x2dworkspace_SM83_CPUState_cFlag(x_1);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = 1;
x_15 = x_20;
goto block_18;
}
else
{
x_15 = x_14;
goto block_18;
}
block_18:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lp_autoresearch_x2dworkspace_SM83_mkFlags(x_13, x_14, x_14, x_15);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_17 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_3);
lean_ctor_set(x_17, 3, x_4);
lean_ctor_set(x_17, 4, x_5);
lean_ctor_set(x_17, 5, x_6);
lean_ctor_set(x_17, 6, x_7);
lean_ctor_set(x_17, 7, x_8);
lean_ctor_set(x_17, 8, x_9);
lean_ctor_set(x_17, 9, x_10);
lean_ctor_set(x_17, 10, x_11);
lean_ctor_set_uint8(x_17, sizeof(void*)*11, x_12);
return x_17;
}
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_execCcf___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_autoresearch_x2dworkspace_SM83_execCcf(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_autoresearch_x2dworkspace_SM83_Flags(uint8_t builtin);
lean_object* initialize_autoresearch_x2dworkspace_SM83_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_autoresearch_x2dworkspace_SM83_Logic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_autoresearch_x2dworkspace_SM83_Flags(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_autoresearch_x2dworkspace_SM83_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_autoresearch_x2dworkspace_SM83_execAnd___closed__0 = _init_lp_autoresearch_x2dworkspace_SM83_execAnd___closed__0();
lean_mark_persistent(lp_autoresearch_x2dworkspace_SM83_execAnd___closed__0);
lp_autoresearch_x2dworkspace_SM83_execSra___closed__0 = _init_lp_autoresearch_x2dworkspace_SM83_execSra___closed__0();
lean_mark_persistent(lp_autoresearch_x2dworkspace_SM83_execSra___closed__0);
lp_autoresearch_x2dworkspace_SM83_execRlca___closed__0 = _init_lp_autoresearch_x2dworkspace_SM83_execRlca___closed__0();
lean_mark_persistent(lp_autoresearch_x2dworkspace_SM83_execRlca___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
