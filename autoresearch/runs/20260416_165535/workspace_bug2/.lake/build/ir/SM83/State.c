// Lean compiler output
// Module: SM83.State
// Imports: public import Init public import SM83.Basic
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
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_hl(lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_writeMem16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_writeMem16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_setA(lean_object*, lean_object*);
static lean_object* lp_autoresearch_x2dworkspace_SM83_defaultState___closed__3;
lean_object* l_BitVec_append___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_setC(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_bc(lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_defaultState;
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_writeMem___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_de___boxed(lean_object*);
static lean_object* lp_autoresearch_x2dworkspace_SM83_defaultState___closed__4;
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_bc___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_readMem16(lean_object*, lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_writeMem(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_hl___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_setBC(lean_object*, lean_object*);
lean_object* l_BitVec_add(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_setHL___boxed(lean_object*, lean_object*);
static lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_readMem16___closed__0;
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_setH(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_defaultState___lam__0___boxed(lean_object*, lean_object*);
lean_object* lp_autoresearch_x2dworkspace_SM83_mk16(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_setDE(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_setL(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* lp_autoresearch_x2dworkspace_SM83_defaultState___closed__1;
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_writeMem___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_setBC___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_setE(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_setD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_de(lean_object*);
static lean_object* lp_autoresearch_x2dworkspace_SM83_defaultState___closed__0;
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_setHL(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_defaultState___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_af___boxed(lean_object*);
lean_object* lp_autoresearch_x2dworkspace_SM83_lo(lean_object*);
static lean_object* lp_autoresearch_x2dworkspace_SM83_defaultState___closed__2;
lean_object* lp_autoresearch_x2dworkspace_SM83_hi(lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_setB(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_setDE___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_af(lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_readMem(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_bc(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_1, 3);
x_4 = lean_unsigned_to_nat(8u);
x_5 = l_BitVec_append___redArg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_bc___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_autoresearch_x2dworkspace_SM83_CPUState_bc(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_de(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 4);
x_3 = lean_ctor_get(x_1, 5);
x_4 = lean_unsigned_to_nat(8u);
x_5 = l_BitVec_append___redArg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_de___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_autoresearch_x2dworkspace_SM83_CPUState_de(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_hl(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 6);
x_3 = lean_ctor_get(x_1, 7);
x_4 = lean_unsigned_to_nat(8u);
x_5 = l_BitVec_append___redArg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_hl___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_autoresearch_x2dworkspace_SM83_CPUState_hl(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_af(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_unsigned_to_nat(8u);
x_5 = l_BitVec_append___redArg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_af___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_autoresearch_x2dworkspace_SM83_CPUState_af(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_setBC(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 3);
lean_dec(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_dec(x_5);
x_6 = lp_autoresearch_x2dworkspace_SM83_hi(x_2);
x_7 = lp_autoresearch_x2dworkspace_SM83_lo(x_2);
lean_ctor_set(x_1, 3, x_7);
lean_ctor_set(x_1, 2, x_6);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 4);
x_11 = lean_ctor_get(x_1, 5);
x_12 = lean_ctor_get(x_1, 6);
x_13 = lean_ctor_get(x_1, 7);
x_14 = lean_ctor_get(x_1, 8);
x_15 = lean_ctor_get(x_1, 9);
x_16 = lean_ctor_get(x_1, 10);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*11);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_18 = lp_autoresearch_x2dworkspace_SM83_hi(x_2);
x_19 = lp_autoresearch_x2dworkspace_SM83_lo(x_2);
x_20 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_9);
lean_ctor_set(x_20, 2, x_18);
lean_ctor_set(x_20, 3, x_19);
lean_ctor_set(x_20, 4, x_10);
lean_ctor_set(x_20, 5, x_11);
lean_ctor_set(x_20, 6, x_12);
lean_ctor_set(x_20, 7, x_13);
lean_ctor_set(x_20, 8, x_14);
lean_ctor_set(x_20, 9, x_15);
lean_ctor_set(x_20, 10, x_16);
lean_ctor_set_uint8(x_20, sizeof(void*)*11, x_17);
return x_20;
}
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_setBC___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_autoresearch_x2dworkspace_SM83_CPUState_setBC(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_setDE(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 5);
lean_dec(x_4);
x_5 = lean_ctor_get(x_1, 4);
lean_dec(x_5);
x_6 = lp_autoresearch_x2dworkspace_SM83_hi(x_2);
x_7 = lp_autoresearch_x2dworkspace_SM83_lo(x_2);
lean_ctor_set(x_1, 5, x_7);
lean_ctor_set(x_1, 4, x_6);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 3);
x_12 = lean_ctor_get(x_1, 6);
x_13 = lean_ctor_get(x_1, 7);
x_14 = lean_ctor_get(x_1, 8);
x_15 = lean_ctor_get(x_1, 9);
x_16 = lean_ctor_get(x_1, 10);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*11);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_18 = lp_autoresearch_x2dworkspace_SM83_hi(x_2);
x_19 = lp_autoresearch_x2dworkspace_SM83_lo(x_2);
x_20 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_9);
lean_ctor_set(x_20, 2, x_10);
lean_ctor_set(x_20, 3, x_11);
lean_ctor_set(x_20, 4, x_18);
lean_ctor_set(x_20, 5, x_19);
lean_ctor_set(x_20, 6, x_12);
lean_ctor_set(x_20, 7, x_13);
lean_ctor_set(x_20, 8, x_14);
lean_ctor_set(x_20, 9, x_15);
lean_ctor_set(x_20, 10, x_16);
lean_ctor_set_uint8(x_20, sizeof(void*)*11, x_17);
return x_20;
}
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_setDE___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_autoresearch_x2dworkspace_SM83_CPUState_setDE(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_setHL(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 7);
lean_dec(x_4);
x_5 = lean_ctor_get(x_1, 6);
lean_dec(x_5);
x_6 = lp_autoresearch_x2dworkspace_SM83_hi(x_2);
x_7 = lp_autoresearch_x2dworkspace_SM83_lo(x_2);
lean_ctor_set(x_1, 7, x_7);
lean_ctor_set(x_1, 6, x_6);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 3);
x_12 = lean_ctor_get(x_1, 4);
x_13 = lean_ctor_get(x_1, 5);
x_14 = lean_ctor_get(x_1, 8);
x_15 = lean_ctor_get(x_1, 9);
x_16 = lean_ctor_get(x_1, 10);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*11);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_18 = lp_autoresearch_x2dworkspace_SM83_hi(x_2);
x_19 = lp_autoresearch_x2dworkspace_SM83_lo(x_2);
x_20 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_9);
lean_ctor_set(x_20, 2, x_10);
lean_ctor_set(x_20, 3, x_11);
lean_ctor_set(x_20, 4, x_12);
lean_ctor_set(x_20, 5, x_13);
lean_ctor_set(x_20, 6, x_18);
lean_ctor_set(x_20, 7, x_19);
lean_ctor_set(x_20, 8, x_14);
lean_ctor_set(x_20, 9, x_15);
lean_ctor_set(x_20, 10, x_16);
lean_ctor_set_uint8(x_20, sizeof(void*)*11, x_17);
return x_20;
}
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_setHL___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_autoresearch_x2dworkspace_SM83_CPUState_setHL(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_defaultState___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_defaultState___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_autoresearch_x2dworkspace_SM83_defaultState___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_lp_autoresearch_x2dworkspace_SM83_defaultState___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = l_BitVec_ofNat(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_autoresearch_x2dworkspace_SM83_defaultState___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lp_autoresearch_x2dworkspace_SM83_defaultState___closed__0;
x_2 = lean_alloc_closure((void*)(lp_autoresearch_x2dworkspace_SM83_defaultState___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_lp_autoresearch_x2dworkspace_SM83_defaultState___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(65534u);
x_2 = lean_unsigned_to_nat(16u);
x_3 = l_BitVec_ofNat(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_autoresearch_x2dworkspace_SM83_defaultState___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(256u);
x_2 = lean_unsigned_to_nat(16u);
x_3 = l_BitVec_ofNat(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_autoresearch_x2dworkspace_SM83_defaultState___closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 0;
x_2 = lp_autoresearch_x2dworkspace_SM83_defaultState___closed__1;
x_3 = lp_autoresearch_x2dworkspace_SM83_defaultState___closed__3;
x_4 = lp_autoresearch_x2dworkspace_SM83_defaultState___closed__2;
x_5 = lp_autoresearch_x2dworkspace_SM83_defaultState___closed__0;
x_6 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_5);
lean_ctor_set(x_6, 3, x_5);
lean_ctor_set(x_6, 4, x_5);
lean_ctor_set(x_6, 5, x_5);
lean_ctor_set(x_6, 6, x_5);
lean_ctor_set(x_6, 7, x_5);
lean_ctor_set(x_6, 8, x_4);
lean_ctor_set(x_6, 9, x_3);
lean_ctor_set(x_6, 10, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*11, x_1);
return x_6;
}
}
static lean_object* _init_lp_autoresearch_x2dworkspace_SM83_defaultState() {
_start:
{
lean_object* x_1; 
x_1 = lp_autoresearch_x2dworkspace_SM83_defaultState___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_setA(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_dec(x_4);
lean_ctor_set(x_1, 0, x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_ctor_get(x_1, 4);
x_9 = lean_ctor_get(x_1, 5);
x_10 = lean_ctor_get(x_1, 6);
x_11 = lean_ctor_get(x_1, 7);
x_12 = lean_ctor_get(x_1, 8);
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
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_5);
lean_ctor_set(x_16, 2, x_6);
lean_ctor_set(x_16, 3, x_7);
lean_ctor_set(x_16, 4, x_8);
lean_ctor_set(x_16, 5, x_9);
lean_ctor_set(x_16, 6, x_10);
lean_ctor_set(x_16, 7, x_11);
lean_ctor_set(x_16, 8, x_12);
lean_ctor_set(x_16, 9, x_13);
lean_ctor_set(x_16, 10, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*11, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_setB(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 2);
lean_dec(x_4);
lean_ctor_set(x_1, 2, x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_ctor_get(x_1, 4);
x_9 = lean_ctor_get(x_1, 5);
x_10 = lean_ctor_get(x_1, 6);
x_11 = lean_ctor_get(x_1, 7);
x_12 = lean_ctor_get(x_1, 8);
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
lean_ctor_set(x_16, 2, x_2);
lean_ctor_set(x_16, 3, x_7);
lean_ctor_set(x_16, 4, x_8);
lean_ctor_set(x_16, 5, x_9);
lean_ctor_set(x_16, 6, x_10);
lean_ctor_set(x_16, 7, x_11);
lean_ctor_set(x_16, 8, x_12);
lean_ctor_set(x_16, 9, x_13);
lean_ctor_set(x_16, 10, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*11, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_setC(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 3);
lean_dec(x_4);
lean_ctor_set(x_1, 3, x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_ctor_get(x_1, 4);
x_9 = lean_ctor_get(x_1, 5);
x_10 = lean_ctor_get(x_1, 6);
x_11 = lean_ctor_get(x_1, 7);
x_12 = lean_ctor_get(x_1, 8);
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
lean_ctor_set(x_16, 3, x_2);
lean_ctor_set(x_16, 4, x_8);
lean_ctor_set(x_16, 5, x_9);
lean_ctor_set(x_16, 6, x_10);
lean_ctor_set(x_16, 7, x_11);
lean_ctor_set(x_16, 8, x_12);
lean_ctor_set(x_16, 9, x_13);
lean_ctor_set(x_16, 10, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*11, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_setD(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 4);
lean_dec(x_4);
lean_ctor_set(x_1, 4, x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_ctor_get(x_1, 3);
x_9 = lean_ctor_get(x_1, 5);
x_10 = lean_ctor_get(x_1, 6);
x_11 = lean_ctor_get(x_1, 7);
x_12 = lean_ctor_get(x_1, 8);
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
lean_ctor_set(x_16, 4, x_2);
lean_ctor_set(x_16, 5, x_9);
lean_ctor_set(x_16, 6, x_10);
lean_ctor_set(x_16, 7, x_11);
lean_ctor_set(x_16, 8, x_12);
lean_ctor_set(x_16, 9, x_13);
lean_ctor_set(x_16, 10, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*11, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_setE(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 5);
lean_dec(x_4);
lean_ctor_set(x_1, 5, x_2);
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
x_10 = lean_ctor_get(x_1, 6);
x_11 = lean_ctor_get(x_1, 7);
x_12 = lean_ctor_get(x_1, 8);
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
lean_ctor_set(x_16, 5, x_2);
lean_ctor_set(x_16, 6, x_10);
lean_ctor_set(x_16, 7, x_11);
lean_ctor_set(x_16, 8, x_12);
lean_ctor_set(x_16, 9, x_13);
lean_ctor_set(x_16, 10, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*11, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_setH(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 6);
lean_dec(x_4);
lean_ctor_set(x_1, 6, x_2);
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
x_11 = lean_ctor_get(x_1, 7);
x_12 = lean_ctor_get(x_1, 8);
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
lean_ctor_set(x_16, 6, x_2);
lean_ctor_set(x_16, 7, x_11);
lean_ctor_set(x_16, 8, x_12);
lean_ctor_set(x_16, 9, x_13);
lean_ctor_set(x_16, 10, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*11, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_setL(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 7);
lean_dec(x_4);
lean_ctor_set(x_1, 7, x_2);
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
x_12 = lean_ctor_get(x_1, 8);
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
lean_ctor_set(x_16, 7, x_2);
lean_ctor_set(x_16, 8, x_12);
lean_ctor_set(x_16, 9, x_13);
lean_ctor_set(x_16, 10, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*11, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_readMem(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 10);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_writeMem___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_eq(x_4, x_1);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_apply_1(x_2, x_4);
return x_6;
}
else
{
lean_dec(x_4);
lean_dec_ref(x_2);
lean_inc(x_3);
return x_3;
}
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_writeMem___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_autoresearch_x2dworkspace_SM83_CPUState_writeMem___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_writeMem(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 10);
x_6 = lean_alloc_closure((void*)(lp_autoresearch_x2dworkspace_SM83_CPUState_writeMem___lam__0___boxed), 4, 3);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_5);
lean_closure_set(x_6, 2, x_3);
lean_ctor_set(x_1, 10, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 3);
x_11 = lean_ctor_get(x_1, 4);
x_12 = lean_ctor_get(x_1, 5);
x_13 = lean_ctor_get(x_1, 6);
x_14 = lean_ctor_get(x_1, 7);
x_15 = lean_ctor_get(x_1, 8);
x_16 = lean_ctor_get(x_1, 9);
x_17 = lean_ctor_get(x_1, 10);
x_18 = lean_ctor_get_uint8(x_1, sizeof(void*)*11);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_19 = lean_alloc_closure((void*)(lp_autoresearch_x2dworkspace_SM83_CPUState_writeMem___lam__0___boxed), 4, 3);
lean_closure_set(x_19, 0, x_2);
lean_closure_set(x_19, 1, x_17);
lean_closure_set(x_19, 2, x_3);
x_20 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_8);
lean_ctor_set(x_20, 2, x_9);
lean_ctor_set(x_20, 3, x_10);
lean_ctor_set(x_20, 4, x_11);
lean_ctor_set(x_20, 5, x_12);
lean_ctor_set(x_20, 6, x_13);
lean_ctor_set(x_20, 7, x_14);
lean_ctor_set(x_20, 8, x_15);
lean_ctor_set(x_20, 9, x_16);
lean_ctor_set(x_20, 10, x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*11, x_18);
return x_20;
}
}
}
static lean_object* _init_lp_autoresearch_x2dworkspace_SM83_CPUState_readMem16___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_unsigned_to_nat(16u);
x_3 = l_BitVec_ofNat(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_readMem16(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_2);
lean_inc_ref(x_1);
x_3 = lp_autoresearch_x2dworkspace_SM83_CPUState_readMem(x_1, x_2);
x_4 = lean_unsigned_to_nat(16u);
x_5 = lp_autoresearch_x2dworkspace_SM83_CPUState_readMem16___closed__0;
x_6 = l_BitVec_add(x_4, x_2, x_5);
lean_dec(x_2);
x_7 = lp_autoresearch_x2dworkspace_SM83_CPUState_readMem(x_1, x_6);
x_8 = lp_autoresearch_x2dworkspace_SM83_mk16(x_7, x_3);
lean_dec(x_3);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_writeMem16(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lp_autoresearch_x2dworkspace_SM83_lo(x_3);
lean_inc(x_2);
x_5 = lp_autoresearch_x2dworkspace_SM83_CPUState_writeMem(x_1, x_2, x_4);
x_6 = lean_unsigned_to_nat(16u);
x_7 = lp_autoresearch_x2dworkspace_SM83_CPUState_readMem16___closed__0;
x_8 = l_BitVec_add(x_6, x_2, x_7);
lean_dec(x_2);
x_9 = lp_autoresearch_x2dworkspace_SM83_hi(x_3);
x_10 = lp_autoresearch_x2dworkspace_SM83_CPUState_writeMem(x_5, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_writeMem16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_autoresearch_x2dworkspace_SM83_CPUState_writeMem16(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_autoresearch_x2dworkspace_SM83_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_autoresearch_x2dworkspace_SM83_State(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_autoresearch_x2dworkspace_SM83_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_autoresearch_x2dworkspace_SM83_defaultState___closed__0 = _init_lp_autoresearch_x2dworkspace_SM83_defaultState___closed__0();
lean_mark_persistent(lp_autoresearch_x2dworkspace_SM83_defaultState___closed__0);
lp_autoresearch_x2dworkspace_SM83_defaultState___closed__1 = _init_lp_autoresearch_x2dworkspace_SM83_defaultState___closed__1();
lean_mark_persistent(lp_autoresearch_x2dworkspace_SM83_defaultState___closed__1);
lp_autoresearch_x2dworkspace_SM83_defaultState___closed__2 = _init_lp_autoresearch_x2dworkspace_SM83_defaultState___closed__2();
lean_mark_persistent(lp_autoresearch_x2dworkspace_SM83_defaultState___closed__2);
lp_autoresearch_x2dworkspace_SM83_defaultState___closed__3 = _init_lp_autoresearch_x2dworkspace_SM83_defaultState___closed__3();
lean_mark_persistent(lp_autoresearch_x2dworkspace_SM83_defaultState___closed__3);
lp_autoresearch_x2dworkspace_SM83_defaultState___closed__4 = _init_lp_autoresearch_x2dworkspace_SM83_defaultState___closed__4();
lean_mark_persistent(lp_autoresearch_x2dworkspace_SM83_defaultState___closed__4);
lp_autoresearch_x2dworkspace_SM83_defaultState = _init_lp_autoresearch_x2dworkspace_SM83_defaultState();
lean_mark_persistent(lp_autoresearch_x2dworkspace_SM83_defaultState);
lp_autoresearch_x2dworkspace_SM83_CPUState_readMem16___closed__0 = _init_lp_autoresearch_x2dworkspace_SM83_CPUState_readMem16___closed__0();
lean_mark_persistent(lp_autoresearch_x2dworkspace_SM83_CPUState_readMem16___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
