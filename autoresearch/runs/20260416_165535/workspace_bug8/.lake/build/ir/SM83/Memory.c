// Lean compiler output
// Module: SM83.Memory
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
static lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_pushStack___closed__0;
lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_writeMem16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_hramStart;
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_oamStart;
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_vramStart;
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_romBank1Start;
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_List_foldl___at___00SM83_CPUState_writeBlock_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_sramStart;
static lean_object* lp_autoresearch_x2dworkspace_SM83_romBank0Start___closed__0;
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_writeBlock(lean_object*, lean_object*, lean_object*);
static lean_object* lp_autoresearch_x2dworkspace_SM83_oamStart___closed__0;
lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_readMem16(lean_object*, lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
static lean_object* lp_autoresearch_x2dworkspace_SM83_ioStart___closed__0;
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_pushStack(lean_object*, lean_object*);
lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_writeMem(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_add(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_popStack(lean_object*);
static lean_object* lp_autoresearch_x2dworkspace_SM83_sramStart___closed__0;
static lean_object* lp_autoresearch_x2dworkspace_List_foldl___at___00SM83_CPUState_writeBlock_spec__0___closed__0;
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_ioStart;
static lean_object* lp_autoresearch_x2dworkspace_SM83_wramStart___closed__0;
static lean_object* lp_autoresearch_x2dworkspace_SM83_vramStart___closed__0;
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_wramStart;
static lean_object* lp_autoresearch_x2dworkspace_SM83_romBank1Start___closed__0;
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_pushStack___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_romBank0Start;
lean_object* l_BitVec_sub(lean_object*, lean_object*, lean_object*);
static lean_object* lp_autoresearch_x2dworkspace_SM83_hramStart___closed__0;
static lean_object* _init_lp_autoresearch_x2dworkspace_SM83_romBank0Start___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_unsigned_to_nat(16u);
x_3 = l_BitVec_ofNat(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_autoresearch_x2dworkspace_SM83_romBank0Start() {
_start:
{
lean_object* x_1; 
x_1 = lp_autoresearch_x2dworkspace_SM83_romBank0Start___closed__0;
return x_1;
}
}
static lean_object* _init_lp_autoresearch_x2dworkspace_SM83_romBank1Start___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(16384u);
x_2 = lean_unsigned_to_nat(16u);
x_3 = l_BitVec_ofNat(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_autoresearch_x2dworkspace_SM83_romBank1Start() {
_start:
{
lean_object* x_1; 
x_1 = lp_autoresearch_x2dworkspace_SM83_romBank1Start___closed__0;
return x_1;
}
}
static lean_object* _init_lp_autoresearch_x2dworkspace_SM83_vramStart___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(32768u);
x_2 = lean_unsigned_to_nat(16u);
x_3 = l_BitVec_ofNat(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_autoresearch_x2dworkspace_SM83_vramStart() {
_start:
{
lean_object* x_1; 
x_1 = lp_autoresearch_x2dworkspace_SM83_vramStart___closed__0;
return x_1;
}
}
static lean_object* _init_lp_autoresearch_x2dworkspace_SM83_sramStart___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(40960u);
x_2 = lean_unsigned_to_nat(16u);
x_3 = l_BitVec_ofNat(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_autoresearch_x2dworkspace_SM83_sramStart() {
_start:
{
lean_object* x_1; 
x_1 = lp_autoresearch_x2dworkspace_SM83_sramStart___closed__0;
return x_1;
}
}
static lean_object* _init_lp_autoresearch_x2dworkspace_SM83_wramStart___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(49152u);
x_2 = lean_unsigned_to_nat(16u);
x_3 = l_BitVec_ofNat(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_autoresearch_x2dworkspace_SM83_wramStart() {
_start:
{
lean_object* x_1; 
x_1 = lp_autoresearch_x2dworkspace_SM83_wramStart___closed__0;
return x_1;
}
}
static lean_object* _init_lp_autoresearch_x2dworkspace_SM83_oamStart___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(65024u);
x_2 = lean_unsigned_to_nat(16u);
x_3 = l_BitVec_ofNat(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_autoresearch_x2dworkspace_SM83_oamStart() {
_start:
{
lean_object* x_1; 
x_1 = lp_autoresearch_x2dworkspace_SM83_oamStart___closed__0;
return x_1;
}
}
static lean_object* _init_lp_autoresearch_x2dworkspace_SM83_ioStart___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(65280u);
x_2 = lean_unsigned_to_nat(16u);
x_3 = l_BitVec_ofNat(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_autoresearch_x2dworkspace_SM83_ioStart() {
_start:
{
lean_object* x_1; 
x_1 = lp_autoresearch_x2dworkspace_SM83_ioStart___closed__0;
return x_1;
}
}
static lean_object* _init_lp_autoresearch_x2dworkspace_SM83_hramStart___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(65408u);
x_2 = lean_unsigned_to_nat(16u);
x_3 = l_BitVec_ofNat(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_autoresearch_x2dworkspace_SM83_hramStart() {
_start:
{
lean_object* x_1; 
x_1 = lp_autoresearch_x2dworkspace_SM83_hramStart___closed__0;
return x_1;
}
}
static lean_object* _init_lp_autoresearch_x2dworkspace_List_foldl___at___00SM83_CPUState_writeBlock_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_unsigned_to_nat(16u);
x_3 = l_BitVec_ofNat(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_List_foldl___at___00SM83_CPUState_writeBlock_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lp_autoresearch_x2dworkspace_SM83_CPUState_writeMem(x_6, x_7, x_3);
x_9 = lean_unsigned_to_nat(16u);
x_10 = lp_autoresearch_x2dworkspace_List_foldl___at___00SM83_CPUState_writeBlock_spec__0___closed__0;
x_11 = l_BitVec_add(x_9, x_7, x_10);
lean_dec(x_7);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_8);
x_2 = x_4;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
lean_inc(x_14);
x_15 = lp_autoresearch_x2dworkspace_SM83_CPUState_writeMem(x_13, x_14, x_3);
x_16 = lean_unsigned_to_nat(16u);
x_17 = lp_autoresearch_x2dworkspace_List_foldl___at___00SM83_CPUState_writeBlock_spec__0___closed__0;
x_18 = l_BitVec_add(x_16, x_14, x_17);
lean_dec(x_14);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
x_1 = x_19;
x_2 = x_4;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_writeBlock(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
x_5 = lp_autoresearch_x2dworkspace_List_foldl___at___00SM83_CPUState_writeBlock_spec__0(x_4, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
return x_6;
}
}
static lean_object* _init_lp_autoresearch_x2dworkspace_SM83_CPUState_pushStack___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_unsigned_to_nat(16u);
x_3 = l_BitVec_ofNat(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_pushStack(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 8);
x_5 = lean_unsigned_to_nat(16u);
x_6 = lp_autoresearch_x2dworkspace_SM83_CPUState_pushStack___closed__0;
x_7 = l_BitVec_sub(x_5, x_4, x_6);
lean_dec(x_4);
lean_inc(x_7);
lean_ctor_set(x_1, 8, x_7);
x_8 = lp_autoresearch_x2dworkspace_SM83_CPUState_writeMem16(x_1, x_7, x_2);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = lean_ctor_get(x_1, 4);
x_14 = lean_ctor_get(x_1, 5);
x_15 = lean_ctor_get(x_1, 6);
x_16 = lean_ctor_get(x_1, 7);
x_17 = lean_ctor_get(x_1, 8);
x_18 = lean_ctor_get(x_1, 9);
x_19 = lean_ctor_get(x_1, 10);
x_20 = lean_ctor_get_uint8(x_1, sizeof(void*)*11);
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
lean_inc(x_9);
lean_dec(x_1);
x_21 = lean_unsigned_to_nat(16u);
x_22 = lp_autoresearch_x2dworkspace_SM83_CPUState_pushStack___closed__0;
x_23 = l_BitVec_sub(x_21, x_17, x_22);
lean_dec(x_17);
lean_inc(x_23);
x_24 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_24, 0, x_9);
lean_ctor_set(x_24, 1, x_10);
lean_ctor_set(x_24, 2, x_11);
lean_ctor_set(x_24, 3, x_12);
lean_ctor_set(x_24, 4, x_13);
lean_ctor_set(x_24, 5, x_14);
lean_ctor_set(x_24, 6, x_15);
lean_ctor_set(x_24, 7, x_16);
lean_ctor_set(x_24, 8, x_23);
lean_ctor_set(x_24, 9, x_18);
lean_ctor_set(x_24, 10, x_19);
lean_ctor_set_uint8(x_24, sizeof(void*)*11, x_20);
x_25 = lp_autoresearch_x2dworkspace_SM83_CPUState_writeMem16(x_24, x_23, x_2);
return x_25;
}
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_pushStack___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_autoresearch_x2dworkspace_SM83_CPUState_pushStack(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_autoresearch_x2dworkspace_SM83_CPUState_popStack(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
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
lean_inc(x_10);
x_14 = lp_autoresearch_x2dworkspace_SM83_CPUState_readMem16(x_1, x_10);
x_15 = lean_unsigned_to_nat(16u);
x_16 = lp_autoresearch_x2dworkspace_SM83_CPUState_pushStack___closed__0;
x_17 = l_BitVec_add(x_15, x_10, x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_3);
lean_ctor_set(x_18, 2, x_4);
lean_ctor_set(x_18, 3, x_5);
lean_ctor_set(x_18, 4, x_6);
lean_ctor_set(x_18, 5, x_7);
lean_ctor_set(x_18, 6, x_8);
lean_ctor_set(x_18, 7, x_9);
lean_ctor_set(x_18, 8, x_17);
lean_ctor_set(x_18, 9, x_11);
lean_ctor_set(x_18, 10, x_12);
lean_ctor_set_uint8(x_18, sizeof(void*)*11, x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_14);
return x_19;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_autoresearch_x2dworkspace_SM83_State(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_autoresearch_x2dworkspace_SM83_Memory(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_autoresearch_x2dworkspace_SM83_State(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_autoresearch_x2dworkspace_SM83_romBank0Start___closed__0 = _init_lp_autoresearch_x2dworkspace_SM83_romBank0Start___closed__0();
lean_mark_persistent(lp_autoresearch_x2dworkspace_SM83_romBank0Start___closed__0);
lp_autoresearch_x2dworkspace_SM83_romBank0Start = _init_lp_autoresearch_x2dworkspace_SM83_romBank0Start();
lean_mark_persistent(lp_autoresearch_x2dworkspace_SM83_romBank0Start);
lp_autoresearch_x2dworkspace_SM83_romBank1Start___closed__0 = _init_lp_autoresearch_x2dworkspace_SM83_romBank1Start___closed__0();
lean_mark_persistent(lp_autoresearch_x2dworkspace_SM83_romBank1Start___closed__0);
lp_autoresearch_x2dworkspace_SM83_romBank1Start = _init_lp_autoresearch_x2dworkspace_SM83_romBank1Start();
lean_mark_persistent(lp_autoresearch_x2dworkspace_SM83_romBank1Start);
lp_autoresearch_x2dworkspace_SM83_vramStart___closed__0 = _init_lp_autoresearch_x2dworkspace_SM83_vramStart___closed__0();
lean_mark_persistent(lp_autoresearch_x2dworkspace_SM83_vramStart___closed__0);
lp_autoresearch_x2dworkspace_SM83_vramStart = _init_lp_autoresearch_x2dworkspace_SM83_vramStart();
lean_mark_persistent(lp_autoresearch_x2dworkspace_SM83_vramStart);
lp_autoresearch_x2dworkspace_SM83_sramStart___closed__0 = _init_lp_autoresearch_x2dworkspace_SM83_sramStart___closed__0();
lean_mark_persistent(lp_autoresearch_x2dworkspace_SM83_sramStart___closed__0);
lp_autoresearch_x2dworkspace_SM83_sramStart = _init_lp_autoresearch_x2dworkspace_SM83_sramStart();
lean_mark_persistent(lp_autoresearch_x2dworkspace_SM83_sramStart);
lp_autoresearch_x2dworkspace_SM83_wramStart___closed__0 = _init_lp_autoresearch_x2dworkspace_SM83_wramStart___closed__0();
lean_mark_persistent(lp_autoresearch_x2dworkspace_SM83_wramStart___closed__0);
lp_autoresearch_x2dworkspace_SM83_wramStart = _init_lp_autoresearch_x2dworkspace_SM83_wramStart();
lean_mark_persistent(lp_autoresearch_x2dworkspace_SM83_wramStart);
lp_autoresearch_x2dworkspace_SM83_oamStart___closed__0 = _init_lp_autoresearch_x2dworkspace_SM83_oamStart___closed__0();
lean_mark_persistent(lp_autoresearch_x2dworkspace_SM83_oamStart___closed__0);
lp_autoresearch_x2dworkspace_SM83_oamStart = _init_lp_autoresearch_x2dworkspace_SM83_oamStart();
lean_mark_persistent(lp_autoresearch_x2dworkspace_SM83_oamStart);
lp_autoresearch_x2dworkspace_SM83_ioStart___closed__0 = _init_lp_autoresearch_x2dworkspace_SM83_ioStart___closed__0();
lean_mark_persistent(lp_autoresearch_x2dworkspace_SM83_ioStart___closed__0);
lp_autoresearch_x2dworkspace_SM83_ioStart = _init_lp_autoresearch_x2dworkspace_SM83_ioStart();
lean_mark_persistent(lp_autoresearch_x2dworkspace_SM83_ioStart);
lp_autoresearch_x2dworkspace_SM83_hramStart___closed__0 = _init_lp_autoresearch_x2dworkspace_SM83_hramStart___closed__0();
lean_mark_persistent(lp_autoresearch_x2dworkspace_SM83_hramStart___closed__0);
lp_autoresearch_x2dworkspace_SM83_hramStart = _init_lp_autoresearch_x2dworkspace_SM83_hramStart();
lean_mark_persistent(lp_autoresearch_x2dworkspace_SM83_hramStart);
lp_autoresearch_x2dworkspace_List_foldl___at___00SM83_CPUState_writeBlock_spec__0___closed__0 = _init_lp_autoresearch_x2dworkspace_List_foldl___at___00SM83_CPUState_writeBlock_spec__0___closed__0();
lean_mark_persistent(lp_autoresearch_x2dworkspace_List_foldl___at___00SM83_CPUState_writeBlock_spec__0___closed__0);
lp_autoresearch_x2dworkspace_SM83_CPUState_pushStack___closed__0 = _init_lp_autoresearch_x2dworkspace_SM83_CPUState_pushStack___closed__0();
lean_mark_persistent(lp_autoresearch_x2dworkspace_SM83_CPUState_pushStack___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
