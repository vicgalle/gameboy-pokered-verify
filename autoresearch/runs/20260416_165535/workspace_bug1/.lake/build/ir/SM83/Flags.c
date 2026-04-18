// Lean compiler output
// Module: SM83.Flags
// Imports: public import Init public import SM83.State
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
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_setZFlag(lean_object*, uint8_t);
static lean_object* lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__6;
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_zBit;
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_hFlag___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_autoresearch_x2dworkspace_SM83_CPUState_cFlag(lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_setFlags___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_autoresearch_x2dworkspace_SM83_CPUState_zFlag(lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_cBit;
static lean_object* lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__4;
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_mkFlags(uint8_t, uint8_t, uint8_t, uint8_t);
lean_object* l_Nat_cast___at___00UInt8_modn_spec__0(lean_object*);
LEAN_EXPORT uint8_t lp_autoresearch_x2dworkspace_SM83_CPUState_nFlag(lean_object*);
static lean_object* lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__8;
static lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_setZFlag___closed__0;
lean_object* l_BitVec_not(lean_object*, lean_object*);
static lean_object* lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__7;
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_setCFlag(lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_setFlags(lean_object*, uint8_t, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_cFlag___boxed(lean_object*);
static lean_object* lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__0;
lean_object* lean_nat_land(lean_object*, lean_object*);
static lean_object* lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__2;
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_hBit;
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_nFlag___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_setCFlag___boxed(lean_object*, lean_object*);
static lean_object* lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__5;
uint8_t l_Nat_testBit(lean_object*, lean_object*);
static lean_object* lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__3;
static lean_object* lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__1;
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_zFlag___boxed(lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_setZFlag___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_autoresearch_x2dworkspace_SM83_CPUState_hFlag(lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_mkFlags___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_setCFlag___closed__0;
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_nBit;
lean_object* lean_nat_lor(lean_object*, lean_object*);
static lean_object* _init_lp_autoresearch_x2dworkspace_SM83_zBit() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(7u);
return x_1;
}
}
static lean_object* _init_lp_autoresearch_x2dworkspace_SM83_nBit() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(6u);
return x_1;
}
}
static lean_object* _init_lp_autoresearch_x2dworkspace_SM83_hBit() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(5u);
return x_1;
}
}
static lean_object* _init_lp_autoresearch_x2dworkspace_SM83_cBit() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(4u);
return x_1;
}
}
LEAN_EXPORT uint8_t lp_autoresearch_x2dworkspace_SM83_CPUState_zFlag(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_unsigned_to_nat(7u);
x_4 = l_Nat_testBit(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_zFlag___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lp_autoresearch_x2dworkspace_SM83_CPUState_zFlag(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t lp_autoresearch_x2dworkspace_SM83_CPUState_nFlag(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_unsigned_to_nat(6u);
x_4 = l_Nat_testBit(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_nFlag___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lp_autoresearch_x2dworkspace_SM83_CPUState_nFlag(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t lp_autoresearch_x2dworkspace_SM83_CPUState_hFlag(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_unsigned_to_nat(5u);
x_4 = l_Nat_testBit(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_hFlag___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lp_autoresearch_x2dworkspace_SM83_CPUState_hFlag(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t lp_autoresearch_x2dworkspace_SM83_CPUState_cFlag(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_unsigned_to_nat(4u);
x_4 = l_Nat_testBit(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_cFlag___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lp_autoresearch_x2dworkspace_SM83_CPUState_cFlag(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = l_BitVec_ofNat(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_shiftl(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__1;
x_2 = l_Nat_cast___at___00UInt8_modn_spec__0(x_1);
return x_2;
}
}
static lean_object* _init_lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_shiftl(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__3;
x_2 = l_Nat_cast___at___00UInt8_modn_spec__0(x_1);
return x_2;
}
}
static lean_object* _init_lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(6u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_shiftl(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__5;
x_2 = l_Nat_cast___at___00UInt8_modn_spec__0(x_1);
return x_2;
}
}
static lean_object* _init_lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_shiftl(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__7;
x_2 = l_Nat_cast___at___00UInt8_modn_spec__0(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_mkFlags(uint8_t x_1, uint8_t x_2, uint8_t x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_19; lean_object* x_20; lean_object* x_24; 
if (x_1 == 0)
{
lean_object* x_28; 
x_28 = lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__0;
x_24 = x_28;
goto block_27;
}
else
{
lean_object* x_29; 
x_29 = lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__8;
x_24 = x_29;
goto block_27;
}
block_12:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_nat_lor(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
x_10 = lean_nat_lor(x_9, x_5);
lean_dec(x_5);
lean_dec(x_9);
x_11 = lean_nat_lor(x_10, x_8);
lean_dec(x_8);
lean_dec(x_10);
return x_11;
}
block_18:
{
if (x_4 == 0)
{
lean_object* x_16; 
x_16 = lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__0;
x_5 = x_15;
x_6 = x_13;
x_7 = x_14;
x_8 = x_16;
goto block_12;
}
else
{
lean_object* x_17; 
x_17 = lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__2;
x_5 = x_15;
x_6 = x_13;
x_7 = x_14;
x_8 = x_17;
goto block_12;
}
}
block_23:
{
if (x_3 == 0)
{
lean_object* x_21; 
x_21 = lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__0;
x_13 = x_19;
x_14 = x_20;
x_15 = x_21;
goto block_18;
}
else
{
lean_object* x_22; 
x_22 = lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__4;
x_13 = x_19;
x_14 = x_20;
x_15 = x_22;
goto block_18;
}
}
block_27:
{
if (x_2 == 0)
{
lean_object* x_25; 
x_25 = lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__0;
x_19 = x_24;
x_20 = x_25;
goto block_23;
}
else
{
lean_object* x_26; 
x_26 = lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__6;
x_19 = x_24;
x_20 = x_26;
goto block_23;
}
}
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_mkFlags___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_unbox(x_1);
x_6 = lean_unbox(x_2);
x_7 = lean_unbox(x_3);
x_8 = lean_unbox(x_4);
x_9 = lp_autoresearch_x2dworkspace_SM83_mkFlags(x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_setFlags(lean_object* x_1, uint8_t x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 1);
lean_dec(x_7);
x_8 = lp_autoresearch_x2dworkspace_SM83_mkFlags(x_2, x_3, x_4, x_5);
lean_ctor_set(x_1, 1, x_8);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 3);
x_12 = lean_ctor_get(x_1, 4);
x_13 = lean_ctor_get(x_1, 5);
x_14 = lean_ctor_get(x_1, 6);
x_15 = lean_ctor_get(x_1, 7);
x_16 = lean_ctor_get(x_1, 8);
x_17 = lean_ctor_get(x_1, 9);
x_18 = lean_ctor_get(x_1, 10);
x_19 = lean_ctor_get_uint8(x_1, sizeof(void*)*11);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_20 = lp_autoresearch_x2dworkspace_SM83_mkFlags(x_2, x_3, x_4, x_5);
x_21 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_21, 0, x_9);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_10);
lean_ctor_set(x_21, 3, x_11);
lean_ctor_set(x_21, 4, x_12);
lean_ctor_set(x_21, 5, x_13);
lean_ctor_set(x_21, 6, x_14);
lean_ctor_set(x_21, 7, x_15);
lean_ctor_set(x_21, 8, x_16);
lean_ctor_set(x_21, 9, x_17);
lean_ctor_set(x_21, 10, x_18);
lean_ctor_set_uint8(x_21, sizeof(void*)*11, x_19);
return x_21;
}
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_setFlags___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_6 = lean_unbox(x_2);
x_7 = lean_unbox(x_3);
x_8 = lean_unbox(x_4);
x_9 = lean_unbox(x_5);
x_10 = lp_autoresearch_x2dworkspace_SM83_CPUState_setFlags(x_1, x_6, x_7, x_8, x_9);
return x_10;
}
}
static lean_object* _init_lp_autoresearch_x2dworkspace_SM83_CPUState_setZFlag___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__8;
x_2 = lean_unsigned_to_nat(8u);
x_3 = l_BitVec_not(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_setZFlag(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__8;
x_4 = lp_autoresearch_x2dworkspace_SM83_CPUState_setZFlag___closed__0;
if (x_2 == 0)
{
lean_object* x_26; 
x_26 = lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__0;
x_5 = x_26;
goto block_25;
}
else
{
x_5 = x_3;
goto block_25;
}
block_25:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_nat_land(x_7, x_4);
lean_dec(x_7);
x_9 = lean_nat_lor(x_8, x_5);
lean_dec(x_5);
lean_dec(x_8);
lean_ctor_set(x_1, 1, x_9);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
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
lean_inc(x_10);
lean_dec(x_1);
x_22 = lean_nat_land(x_11, x_4);
lean_dec(x_11);
x_23 = lean_nat_lor(x_22, x_5);
lean_dec(x_5);
lean_dec(x_22);
x_24 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_24, 0, x_10);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_12);
lean_ctor_set(x_24, 3, x_13);
lean_ctor_set(x_24, 4, x_14);
lean_ctor_set(x_24, 5, x_15);
lean_ctor_set(x_24, 6, x_16);
lean_ctor_set(x_24, 7, x_17);
lean_ctor_set(x_24, 8, x_18);
lean_ctor_set(x_24, 9, x_19);
lean_ctor_set(x_24, 10, x_20);
lean_ctor_set_uint8(x_24, sizeof(void*)*11, x_21);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_setZFlag___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
x_4 = lp_autoresearch_x2dworkspace_SM83_CPUState_setZFlag(x_1, x_3);
return x_4;
}
}
static lean_object* _init_lp_autoresearch_x2dworkspace_SM83_CPUState_setCFlag___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__2;
x_2 = lean_unsigned_to_nat(8u);
x_3 = l_BitVec_not(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_setCFlag(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__2;
x_4 = lp_autoresearch_x2dworkspace_SM83_CPUState_setCFlag___closed__0;
if (x_2 == 0)
{
lean_object* x_26; 
x_26 = lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__0;
x_5 = x_26;
goto block_25;
}
else
{
x_5 = x_3;
goto block_25;
}
block_25:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_nat_land(x_7, x_4);
lean_dec(x_7);
x_9 = lean_nat_lor(x_8, x_5);
lean_dec(x_5);
lean_dec(x_8);
lean_ctor_set(x_1, 1, x_9);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
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
lean_inc(x_10);
lean_dec(x_1);
x_22 = lean_nat_land(x_11, x_4);
lean_dec(x_11);
x_23 = lean_nat_lor(x_22, x_5);
lean_dec(x_5);
lean_dec(x_22);
x_24 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_24, 0, x_10);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_12);
lean_ctor_set(x_24, 3, x_13);
lean_ctor_set(x_24, 4, x_14);
lean_ctor_set(x_24, 5, x_15);
lean_ctor_set(x_24, 6, x_16);
lean_ctor_set(x_24, 7, x_17);
lean_ctor_set(x_24, 8, x_18);
lean_ctor_set(x_24, 9, x_19);
lean_ctor_set(x_24, 10, x_20);
lean_ctor_set_uint8(x_24, sizeof(void*)*11, x_21);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_setCFlag___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
x_4 = lp_autoresearch_x2dworkspace_SM83_CPUState_setCFlag(x_1, x_3);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_autoresearch_x2dworkspace_SM83_State(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_autoresearch_x2dworkspace_SM83_Flags(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_autoresearch_x2dworkspace_SM83_State(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_autoresearch_x2dworkspace_SM83_zBit = _init_lp_autoresearch_x2dworkspace_SM83_zBit();
lean_mark_persistent(lp_autoresearch_x2dworkspace_SM83_zBit);
lp_autoresearch_x2dworkspace_SM83_nBit = _init_lp_autoresearch_x2dworkspace_SM83_nBit();
lean_mark_persistent(lp_autoresearch_x2dworkspace_SM83_nBit);
lp_autoresearch_x2dworkspace_SM83_hBit = _init_lp_autoresearch_x2dworkspace_SM83_hBit();
lean_mark_persistent(lp_autoresearch_x2dworkspace_SM83_hBit);
lp_autoresearch_x2dworkspace_SM83_cBit = _init_lp_autoresearch_x2dworkspace_SM83_cBit();
lean_mark_persistent(lp_autoresearch_x2dworkspace_SM83_cBit);
lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__0 = _init_lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__0();
lean_mark_persistent(lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__0);
lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__1 = _init_lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__1();
lean_mark_persistent(lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__1);
lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__2 = _init_lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__2();
lean_mark_persistent(lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__2);
lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__3 = _init_lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__3();
lean_mark_persistent(lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__3);
lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__4 = _init_lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__4();
lean_mark_persistent(lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__4);
lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__5 = _init_lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__5();
lean_mark_persistent(lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__5);
lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__6 = _init_lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__6();
lean_mark_persistent(lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__6);
lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__7 = _init_lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__7();
lean_mark_persistent(lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__7);
lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__8 = _init_lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__8();
lean_mark_persistent(lp_autoresearch_x2dworkspace_SM83_mkFlags___closed__8);
lp_autoresearch_x2dworkspace_SM83_CPUState_setZFlag___closed__0 = _init_lp_autoresearch_x2dworkspace_SM83_CPUState_setZFlag___closed__0();
lean_mark_persistent(lp_autoresearch_x2dworkspace_SM83_CPUState_setZFlag___closed__0);
lp_autoresearch_x2dworkspace_SM83_CPUState_setCFlag___closed__0 = _init_lp_autoresearch_x2dworkspace_SM83_CPUState_setCFlag___closed__0();
lean_mark_persistent(lp_autoresearch_x2dworkspace_SM83_CPUState_setCFlag___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
