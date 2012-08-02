/*
 * University of Illinois/NCSA
 * Open Source License
 *
 *  Copyright (c) 2007-2011,The Board of Trustees of the University of
 *  Illinois.  All rights reserved.
 *
 *  Copyright (c) 2011 Sam King, Matthew Hicks, and Edgar Pek
 *
 *  Developed by:
 *
 *  Professor Sam King in the Department of Computer Science
 *  The University of Illinois at Urbana-Champaign
 *      http://www.cs.uiuc.edu/homes/kingst/Research.html
 *
 *       Permission is hereby granted, free of charge, to any person
 *       obtaining a copy of this software and associated
 *       documentation files (the "Software"), to deal with the
 *       Software without restriction, including without limitation
 *       the rights to use, copy, modify, merge, publish, distribute,
 *       sublicense, and/or sell copies of the Software, and to permit
 *       persons to whom the Software is furnished to do so, subject
 *       to the following conditions:
 *
 *          Redistributions of source code must retain the above
 *          copyright notice, this list of conditions and the
 *          following disclaimers.
 *
 *          Redistributions in binary form must reproduce the above
 *          copyright notice, this list of conditions and the
 *          following disclaimers in the documentation and/or other
 *          materials provided with the distribution.
 *
 *          Neither the names of Sam King, the University of Illinois,
 *          nor the names of its contributors may be used to endorse
 *          or promote products derived from this Software without
 *          specific prior written permission.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 *  EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 *  MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 *  NONINFRINGEMENT.  IN NO EVENT SHALL THE CONTRIBUTORS OR COPYRIGHT
 *  HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 *  WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 *  OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
 *  DEALINGS WITH THE SOFTWARE.
*/

#include "simulator.h"

#define NUM_OPCODE_BITS 6
#define NUM_OPCODES (1<<NUM_OPCODE_BITS)
#define OPCODE_MASK (NUM_OPCODES-1)
#define OPCODE_SHIFT (32-NUM_OPCODE_BITS)

#define GET_BITS(inst, shift, bits)  (((inst)>>shift) & ((1<<(bits))-1))

#define OPCODE(inst) GET_BITS((inst), 26, 6)
#define SF_OP(inst) GET_BITS((inst), 21, 5)
#define ALU_OP(inst) GET_BITS((inst), 0, 10)
#define ALU_SHIFT(inst) ((((inst)&0xf) == 0xc) || (((inst)&0xf) == 0x8))
#define RO_SHIFT_I_OP(inst) GET_BITS((inst), 6, 2)

#define I_HI(inst) GET_BITS((inst), 21, 5)
#define I_LOW(inst) GET_BITS((inst), 0, 11)
#define SPLIT_I(inst)  ((I_HI(inst) << 11) | I_LOW(inst))
#define SPLIT_K(inst) SPLIT_I(inst)
#define I(inst) GET_BITS((inst), 0, 16)
#define I_MAC(inst) GET_BITS((inst), 0, 11)
#define K(inst) GET_BITS((inst), 0, 16)
#define L(inst) GET_BITS((inst), 0, 6)
#define N(inst) GET_BITS((inst), 0, 26)

#define RD(inst) GET_BITS((inst), 21, 5)
#define RA(inst) GET_BITS((inst), 16, 5)
#define RB(inst) GET_BITS((inst), 11, 5)

#define ADD_ALU_OP   (           0x0)
#define ADDC_ALU_OP  (           0x1)
#define SUB_ALU_OP   (           0x2)
#define AND_ALU_OP   (           0x3)
#define OR_ALU_OP    (           0x4)
#define XOR_ALU_OP   (           0x5)
#define EXTHS_ALU_OP (           0xc)
#define EXTBS_ALU_OP ((0x1<<6) | 0xc)
#define EXTBZ_ALU_OP ((0x3<<6) | 0xc)
#define EXTHZ_ALU_OP ((0x2<<6) | 0xc)
#define EXTWS_ALU_OP ((0x0<<6) | 0xd)
#define EXTWZ_ALU_OP ((0x1<<6) | 0xd)
#define SLL_ALU_OP   ((0x0<<6) | 0x8)
#define SRL_ALU_OP   ((0x1<<6) | 0x8)
#define SRA_ALU_OP   ((0x2<<6) | 0x8)
#define DIVU_ALU_OP  ((0x3<<8) | 0xa)
#define DIV_ALU_OP   ((0x3<<8) | 0x9)
#define FF1_ALU_OP   ((0x0<<8) | 0xf)
#define FL1_ALU_OP   ((0x1<<8) | 0xf)
#define MUL_ALU_OP   ((0x3<<8) | 0x6)
#define MULU_ALU_OP  ((0x3<<8) | 0xb)
#define ROR_ALU_OP   ((0x3<<6) | 0x8)
#define CMOV_ALU_OP  ((0x0<<6) | 0xe)

#define SFEQ_OP     0x0
#define SFNE_OP     0x1
#define SFGTU_OP    0x2
#define SFGEU_OP    0x3
#define SFLTU_OP    0x4
#define SFLEU_OP    0x5
#define SFGTS_OP    0xa
#define SFGES_OP    0xb
#define SFLTS_OP    0xc
#define SFLES_OP    0xd

#define RS_SLLI_OP   0x0
#define RS_SRLI_OP   0x1
#define RS_SRAI_OP   0x2
#define RS_RORI_OP   0x3

#define OP_J    0x0
#define OP_JAL  0x1
#define OP_JALR 0x12
#define OP_BNF  0x3
#define OP_BF   0x4
#define OP_NOP  0x5
#define OP_JR   0x11
#define OP_LWZ  0x21
#define OP_LWS  0x22
#define OP_LBZ  0x23
#define OP_LBS  0x24
#define OP_LHZ  0x25
#define OP_LHS  0x26
#define OP_ADDI 0x27
#define OP_ADDIC 0x28
#define OP_ORI  0x2a
#define OP_XORI 0x2b
#define OP_MULI 0x2c
#define OP_SFI  0x2f
#define OP_SW   0x35
#define OP_SB   0x36
#define OP_SH   0x37
#define OP_ALU  0x38
#define OP_MAC  0x31
#define OP_MACI 0x13
#define OP_MACRC_MOVHI 0x6
#define OP_MTSPR 0x30
#define OP_MFSPR 0x2d
#define OP_ANDI 0x29
#define OP_RO_SHIFT_I 0x2e
#define OP_SF 0x39
#define OP_SYS_TRAP_SYNC 0x08
#define OP_TRAP 0x21
#define OP_PM_SYNC 0x22
#define OP_CSYNC 0x23
#define OP_RFE 0x9

#define IS_BIT_SET(a,bit) (((a) & (0x1 << (bit))) != 0)
#define IS_NEG(a) (((a) & 1<<31) != 0)
#define IS_POS(a) (!IS_NEG(a))

struct control {
    u32 inst;
    u32 opcode; _(invariant \this->opcode == ((\this->inst >> 26) & 0x3f))
    u32 sf_op;  _(invariant \this->sf_op == ((\this->inst >> 21) & 0x1f))
    u32 alu_op; _(invariant \this->alu_op < (1<<10))
    u32 ro_shift_i_op;
    u32 rD;     _(invariant \this->rD == ((\this->inst >> 21) & 0x1f))
    u32 rA;     _(invariant \this->rA == ((\this->inst >> 16) & 0x1f))
    u32 rB;     _(invariant \this->rB == ((\this->inst >> 11) & 0x1f))
    u32 N;      _(invariant \this->N == (\this->inst & 0x03ffffff))
//  u32 K; _(invariant \this->K == (\this->inst & 0x0000ffff)) //OLD INVARIANT
    u32 K;      _(invariant \this->K < (1<<16)) //NEW INVARIANT
    u32 I;      _(invariant \this->I < (1<<16))
    u32 L;
};

/****************************** Logic functions ***************************/
_(logic bool bit_set(u32 value, u32 bit) = ((value & (0x1 << bit)) != 0))
_(logic i32 to_i32(u32 value) = _(unchecked)((i32) value))
_(logic i32 to_i32(u64 value) = _(unchecked)((i32) value))
_(logic i32 to_i32(i64 value) = _(unchecked)((i32) value))
_(logic u32 to_u32(i32 value) = _(unchecked)((u32) value))
_(logic u32 to_u32(i64 value) = _(unchecked)((u32) value))
_(logic u64 to_u64(u32 value) = _(unchecked)((u64) value))
_(logic u64 to_u64(i64 value) = _(unchecked)((u64) value))
_(logic i64 to_i64(i32 value) = _(unchecked)((i64) value))
_(logic i64 to_i64(u64 value) = _(unchecked)((i64) value))

_(logic u32 pow2(u32 n) = (1 << n) )
//_(logic u64 pow2(u32 n) = (1 << n) )
/****************************** Pure functions ***************************/
_(pure) u32 maxNbit32( u32 n )
    _(requires n <= 32 )
    _(ensures \result == (0xffffffff >> (32-n)))
{ 
    return _(unchecked)(u32)((((u64)1) << n)-1); 
}

/****************************** Shared helper functions ***************************/

static u32 zero_extend(u32 value, u32 num_bits) 
    _(requires num_bits < 32)
    _(ensures \result < pow2(num_bits))
    _(ensures (\result >> (num_bits+1)) == 0)
    _(ensures ((\result >> 31)&1) == 0) //msb is always 0
    _(ensures \result == (value & maxNbit32(num_bits)))
{
    return value & ((1<<num_bits)-1);
}

static i32 sign_extend(u32 value, u32 sign_bit) 
    _(requires sign_bit < 31)
    _(requires value < (1<<(sign_bit+1)))
    _(ensures (to_u32(\result) & maxNbit32(sign_bit+1)) == 
                       (value  & maxNbit32(sign_bit+1))    )
    _(ensures !bit_set(value, sign_bit) ==> \result >= 0)
    _(ensures !bit_set(value, sign_bit) ==> (to_u32(\result) ==        value))
    _(ensures !bit_set(value, sign_bit) ==> (       \result  == to_i32(value)))
    _(ensures  bit_set(value, sign_bit) ==> \result <  0)
    _(ensures  bit_set(value, sign_bit) ==> 
             ((to_u32(\result) & maxNbit32(sign_bit+1)) == value))
    _(ensures  bit_set(value, sign_bit) ==>
           (((to_u32(\result)) & (0xffffffff << sign_bit)) 
                              == (0xffffffff << sign_bit) ) )
    _(ensures  bit_set(value, sign_bit) ==>
            ((to_u32(\result) >= (0xffffffff << sign_bit)) && 
                    (\result  <   0 )))
{
    //NOTE: casting without _(unchecked) can create unsoundness!!! (see the lemma below)
    _(assert {:bv} \forall u32 x,y; (y<31) ==> 
              (to_i32(x | (0xffffffff << y)) ) < 0) 
    _(assert {:bv} \forall u32 x,y; (y<31) ==> 
             (to_i32((x | (0xffffffff << y)) & pow2(31)) < 0  )) 
    _(assert {:bv} \forall u32 x,y; // the key lemma for the first postcondition
             (y < 31 && bit_set(x, y) && x < pow2(y+1)) ==> 
           (((x | (0xffffffff << y)) & (pow2(y+1)-1)) == x) ) 
    _(assert {:bv} \forall u32 x,y; 
            (y < 32 && x < pow2(y)) ==> (x == (x & (pow2(y)-1))) )
//TODO: see if this can be used somewhere else
//_(assert {:bv} \forall u32 x,y; (y<31) ==> ((i32)(x|(0xffffffff << y ))) < 0) 
//    _(assert {:bv} \forall i32 x; u32 y; // the key lemma for the last postcondition
//             (y<32 && _(unchecked)(u32)x < (1<<y)) ==> 
//             (_(unchecked)((u32)x) == (((u32)x) & ((1<<y)-1))) )

    if(IS_BIT_SET(value, sign_bit)) {
        value = value | (0xffffffff << sign_bit);
        _(assert to_i32(value) < 0)
        _(assert value >= (0xffffffff << sign_bit))
    }
    return to_i32(value);
}

static i32 exts(u32 imm) 
    _(requires imm < (1 << 16))
    _(ensures (to_u32(\result) & maxNbit32(16)) == (imm  & maxNbit32(16)))
    _(ensures !bit_set(imm, 15) ==> \result >= 0)
    _(ensures !bit_set(imm, 15) ==> (to_u32(\result) == imm))
    _(ensures !bit_set(imm, 15) ==> (\result == to_i32(imm)))
    _(ensures  bit_set(imm, 15) ==> (\result < 0))
    _(ensures  bit_set(imm, 15) ==> 
             ((to_u32(\result) & maxNbit32(16)) == imm))
    _(ensures  bit_set(imm, 15) ==> 
             ((to_u32(\result) & 0xffff8000) == 0xffff8000))
    _(ensures  bit_set(imm, 15) ==>
             ((to_u32(\result) >= 0xffff8000)))
{
    _(assert {:bv} \forall u32 x;(x==15) ==> (0xffff8000==(0xffffffff << x)))
    return sign_extend(imm, 15);
}

static bool is_overflow(u32 a, u32 b, u32 r) 
    _(ensures IS_NEG(a) && IS_POS(b) ==> \result == false)
    _(ensures IS_POS(a) && IS_NEG(b) ==> \result == false)
    _(ensures IS_POS(a) && IS_POS(b) && IS_NEG(r) ==> \result == true)
    _(ensures IS_POS(a) && IS_POS(b) && IS_POS(r) ==> \result == false)
    _(ensures IS_NEG(a) && IS_NEG(b) && IS_POS(r) ==> \result == true)
    _(ensures IS_NEG(a) && IS_NEG(b) && IS_NEG(r) ==> \result == false)
{
    bool o = (IS_NEG(a) && IS_NEG(b) && IS_POS(r)) ||
        (IS_POS(a) && IS_POS(b) && IS_NEG(r));
    
    _(assert IS_NEG(a) && IS_NEG(b) && IS_POS(r) ==> o);
    _(assert IS_NEG(a) && IS_NEG(b) && IS_NEG(r) ==> !o);
    _(assert IS_NEG(a) && IS_POS(b) ==> !o);
    _(assert IS_POS(a) && IS_POS(b) && IS_NEG(r) ==> o);
    _(assert IS_POS(a) && IS_POS(b) && IS_POS(r) ==> !o);
    _(assert IS_POS(a) && IS_NEG(b) ==> !o);
    
    return o;
}

static void calc_add(bool carry_in, u32 a, u32 b, u32 *res, bool *overflow, bool *carry) {
    u32 r=0;
    u32 mask, idx, A, B, cin;
    bool c=carry_in;
    bool o=false;

    for(idx = 0; idx < 32; idx++) {
        cin = c ? 1<<idx : 0;
        mask = 1<<idx;        
        A = a&mask;
        B = b&mask;
        r |= A^B^cin;
        cin = (A&B) | (cin&(A^B));
        c = cin != 0;
    }

    o = is_overflow(a, b, r);

    *res = r;
    *carry = c;
    *overflow = o;
}

/*
//TODO: bug in vcc? if the paramater is named result, then vcc reports spurious error 'invalid indirection'
//TODO: clean up the code
static void calc_add(bool carry_in, u32 a, u32 b, u32 *res, bool *overflow, bool *carry) 
    _(requires overflow != carry)
    _(writes overflow)
    _(writes carry)
    _(writes res)
    _(ensures ((a + b + (u32) carry_in) % (UINT_MAX+1)) == *res )
    _(ensures ((u64)a + (u64)b + (u64)carry_in) 
           == ((u64)(*res) + ((u64)(*carry) <<32)) )
    _(ensures *res <  a && *res <= b  ==> *carry)
    _(ensures *res <= a && *res <  b  ==> *carry)
    _(ensures (((u64)a + (u64)b + (u64)carry_in) <= UINT_MAX) 
         <==> !(*carry) )
    _(ensures (((u64)a + (u64)b + (u64)carry_in) >  UINT_MAX) 
         <==>  (*carry) )
    _(ensures (IS_NEG(a) && IS_NEG(b) && IS_POS(*res)) 
           || (IS_POS(a) && IS_POS(b) && IS_NEG(*res)) <==> *overflow)
{
    u32 r=0;
    u32 e=0;
    bool c=false;
    bool o=false;
    u64 r64=0;

    e = (carry_in) ? 1 : 0;
    r64 = ((u64) a) + ((u64) b) + ((u64) e);

    _(assert {:bv} \forall u64 x; _(unchecked)(u32)(x & ((((u64) (1))<<32) -1)) == (_(unchecked)(u32)x ))
//  _(assert {:bv} \forall u32 y; ((u64)(y) & (((u64) (1)<<32) -1))  == (u64)y )
//  _(assert {:bv} \forall u64 x,y,z; (x <= (u64)(UINT_MAX) && y <= (u64)(UINT_MAX) && z <= (u64)(1)) ==>
//             ( (x + y + z) < (((u64) 1)<<33) ) )
//   _(assert {:bv} \forall u64 x,y; (x <= (UINT_MAX) && y <= (UINT_MAX)) ==>
//             ( x <= (x+y) && y <= (x+y) ) )
    _(assert {:bv} \forall u64 x; (x <= UINT_MAX) ==> (x & (((u64) 1)<<32)) == 0 )
//  _(assert {:bv} \forall u64 x,y,z; (x<UINT_MAX && y<UINT_MAX && z<=1 && (x+y+z) <= UINT_MAX) ==> ((x+y+z) & (((u64) 1)<<32)) == 0 ) 

    r = _(unchecked) (u32) r64;  
//   r = (u32)(r64 & ((((u64) 1)<<32)-1) );

    c = (r64 & (((u64) 1)<<32)) != 0;
    _(assert {:bv} \forall u64 x; (x >= (((u64) 1)<<32) && (x < (((u64) 1)<<33)) )
                    ==> ( (x & (((u64) 1)<<32)) != 0 ) ) // the key lemma for proving properties of carry out
    o = is_overflow(a, b, r);

    _(assert r == ((a+b+e) % (((u64)UINT_MAX)+1)))
//    _(assert r64 == ((u64)a + (u64)b + (u64)e))
//    _(assert _(unchecked)(((u64)1)<<32) == (((u64) UINT_MAX)+1) )
    _(assert c == false ==> r64 == _(unchecked)((u64)r) )
    _(assert c == true  ==> (r64 == (((u64)r) + (((u64) 1)<<32))))
    _(assert r64 == (((u64)r) + (((u64) c)<<32)))
    _(assert r < a && r <= b ==> c )
    _(assert r <= a && r < b ==> c )
    _(assert r <= a && r < b || r < a && r <=b ==> c )
    _(assert r64 <= UINT_MAX <==> !c )
    _(assert r64 >  UINT_MAX <==>  c )

    *res = r;
    *carry = c;
    *overflow = o;
}
*/

//_(pure) u64 prod_sum(u32 a, u32 b, u32 i)
// helper implementation -- used to figure how to get the calc_mul right
void peasant_mulu(u32 a, u32 b)
{
    u32 idx  = 0;
    u64 prod = 0;
    u64 mand = to_u64(a);
    u32 mier = b;
    _(ghost u32 gmier = mier)

//    _(assert a*b == mand * mier + prod)
    _(assert \forall u64 x; u32 y; !(y % 2) ==> ((x*2) * (y/2) == x*y))
    _(assert \forall u64 x; u32 y; (y % 2) ==> (((x*2) * (y/2) + x) == x*y))
    _(assert {:bv} \forall u32 x; ((x >> 31) >> 1) == 0)
    _(assert {:bv} \forall u32 x; (x >> 1) == (x/2))
    //_(assert {:bv} \forall u32 x,i; (i<=32) ==> (x >> i) == (x/(pow2(i))))
    for (idx = 0; idx < 32; idx++)
        _(invariant idx >= 0 && idx <= 32)
       _(invariant gmier == mier)
        _(invariant gmier == (b >> idx))
        _(invariant (mier == 0) ==> (mier * mand == 0))
        _(invariant !(mier % 2) ==> ((mand*2) * (mier/2) == mier*mand) )
        _(invariant (mier % 2) ==> (((mand*2) * (mier/2) + mand) == mier*mand) )
        _(invariant a*b == (mand*mier + prod))
    {
      //_(assert a*b == (mand*mier + prod))
        if (mier % 2){
            _(unchecked) prod += mand;
        }
        _(unchecked) mand *= 2;
        mier /= 2;
       _(ghost gmier >>= 1)
    }
    _(assert idx == 32)
    _(assert mier == 0)
    _(assert prod == a*b)
}

static void calc_mulu(u32 a, u32 b, u64 *prod_out) 
    _(writes prod_out)
    _(ensures *prod_out == a*b)
{
    u32 idx = 0;       // int idx -> u32 idx
    u64 prod = 0;      //product -> prod
    _(ghost u64 gprod = prod)
    u64 mand = to_u64(a);  //multipicand -> mand
    _(ghost u64 gmand = mand)
    u32 mier = b;  //multiplier  -> mier
    _(ghost u32 gmier = mier)
    _(assert mand <= 0xffffffff)

//   _(assert {:bv} \forall u64 x; \forall int y; ( (y<32 && y>=0) && (x <= 0x00000000ffffffff)) ==> (\forall int z; (z<y) ==> ((x << y) + (x << z)) < (u64)(-1)))
//   _(assert {:bv} \forall u32 x; int i; x >= (x >> i) )
//   _(assert {:bv} \forall u64 x; int i; (x <= 0x00000000ffffffff && i < 32 && i >= 0) ==> x <= (x << i))
//    _(assert {:bv} \forall u32 x,i; (i <= 32) ==> (x >> i) <= x)
//    _(assert {:bv} \forall u64 x; u32 i; (i<32 && x <= 0xffffffff) ==> 
//                    ((x << i) >= x))

    // the _key_ lemma for the second part of the proof (mier == 0)
    _(assert {:bv} \forall u32 x; ((x >> 31) >> 1) == 0)
    // need this lemma to prove the invariant (mier & 0x1 == b & (1<<i))
//    _(assert {:bv} \forall u32 x,i; (i<32) ==> (((x >> i) & 0x1) 
//                                            <==> (x & (1 << i)) ))
    _(assert {:bv} \forall u32 x; (x & 0x1) == (x % 2))
    _(assert {:bv} \forall u32 x; (x >> 1) == (x/2))
    _(assert {:bv} \forall u64 x; (x << 1) == (x*2))
    _(assert \forall u64 x; u32 y; !(y % 2) ==> ((x*2) * (y/2) == x*y))
    _(assert \forall u64 x; u32 y; (y % 2) ==> (((x*2) * (y/2) + x) == x*y))
//    _(assert {:bv} \forall u64 x; u32 y; !(y & 0x1) ==> 
//                    ((x<<1) * (y>>1) == x*y) )
//    _(assert {:bv} \forall u32 x,i; (i<32) ==> ((x >> i) == (x/(1<<i))))
//    _(assert a*b == (gmand * gmier + gprod))
    for(idx = 0; idx < 32; idx++) 
        _(invariant idx >= 0 && idx <= 32)
        _(invariant mier == (b >> idx) )
//        _(invariant (mand >> idx) == a)
//        _(invariant (mier & 0x1) <==> (b & (1<<idx) ))
        _(invariant gmand == mand)
        _(invariant gmier == mier)
        _(invariant (mier & 0x1) == (gmier % 2))
//        _(invariant (gmand * gmier) == (mand * mier) )
        _(invariant gprod == prod)
//        _(invariant ((gmand * gmier) + gprod) == ((mand * mier) + prod) )
        _(invariant (gmier == 0) ==> (gmier * gmand == 0))
        _(invariant !(gmier % 2) ==> ((gmand*2) * (gmier/2) == gmier*gmand) )
        _(invariant (gmier % 2) ==> (((gmand*2) * (gmier/2) + gmand) == gmier*gmand) )
//        _(invariant !(gmier % 2) ==> ((gmand*2) * (gmier/2) == prod) )
//        _(invariant !(gmier % 2) ==> (((gmand*2) * (gmier/2) + gprod) == a*b) )
        _(invariant a*b == (gmand * gmier + gprod) ) // this is the key thing to prove
//        _(invariant b == 0 ==> prod == 0)
//        _(invariant !(mier % 2) ==> (prod == mand * mier) )
    {
        _(assert idx < 32)
 //       _(ghost old_gprod = gprod)
        if(mier & 0x1) {
            _(unchecked) prod += mand;
            _(ghost _(unchecked) gprod += gmand)
        }
        mand <<= 1;
        _(ghost _(unchecked)gmand *= 2)
        mier >>= 1;
        _(ghost gmier /= 2)
       
    }
    _(assert a*b == (mand * mier + prod) ) // this is the key thing to prove
    _(assert mier == 0)
    _(assert prod == a*b)

    *prod_out = prod;
    _(assert *prod_out == a*b )
}



static void calc_mul(i32 a, i32 b, i64 *prod_out) 
    _(writes prod_out)
    _(ensures *prod_out == a*b )
{
    i32 sign_a = a & 0x80000000;
    i32 sign_b = b & 0x80000000;
    u64 prod;
    _(ghost u64 old_prod;)
    _(assert {:bv} \forall i32 x; ((x & 0x80000000) == 0) <==> x >= 0 )
    _(assert {:bv} \forall i32 x; ((x & 0x80000000) == 0x80000000) <==> x < 0 )
    // absolute value of a and b
    // I am not sure what to do if a or b == 0x80000000
    // I don't think this works for that case

    _(assert {:bv} \forall u32 x; (x >= 0x80000000) ==> 
             (((x ^ ((u32) -1)) + 1) <= 0x80000000) ) 
    _(assert {:bv} \forall i32 x; (x < 0 && x >  0x80000000) ==> // one of the key lemmas
             (_(unchecked)(i32)((to_u32(x) ^ ((u32) -1)) + 1) == -x ) ) 
    _(assert {:bv} \forall i32 x; (x ==  0x80000000) ==> 
             (_(unchecked)(i32)((to_u32(x) ^ ((u32) -1)) + 1) == 0x80000000 ) ) 
    //_(assert {:bv} \forall i32 x; (x >= 0) ==> (to_u32(x) >= 0))
    //the lemma below helps prove to_u32(A) <= 0x80000000
    _(assert {:bv} \forall i32 x; (x <  0) ==> (to_u32(x) >= 0x80000000))

    _(assert  sign_a ==> a <  0)
    _(assert !sign_a ==> a >= 0)
    if(sign_a) a = _(unchecked)(i32)( (to_u32(a) ^ ((u32) -1)) + 1 );
    _(assert a >= 0x80000000)
    _(assert to_u32(a) <= 0x80000000)
    _(assert \old(a) < 0 && \old(a) >  0x80000000 ==> (a == -(\old(a)) ))
    _(assert \old(a) == 0x80000000 ==> (a == 0x80000000) )

    _(assert  sign_b ==> b <  0)
    _(assert !sign_b ==> b >= 0)
    if(sign_b) b = _(unchecked)(i32) ( (to_u32(b) ^ ((u32) -1)) + 1 );
    _(assert b >= 0x80000000)
    _(assert to_u32(b) <= 0x80000000)
    _(assert \old(b) < 0 && \old(b) >  0x80000000 ==> (b == -(\old(b)) ))
    _(assert \old(b) == 0x80000000 ==> (b == 0x80000000) )
    
    _(assert {:bv} \forall u32 x,y; (x <= 0x80000000 && y <= 0x80000000)
                    ==> (((u64) x*y) <= (((u64)0x80000000) << 31)))
    calc_mulu(to_u32(a), to_u32(b), &prod);
    _(assert prod == to_u32(a) * to_u32(b))
    _(assert prod <= (((u64) 0x80000000) << 31))
    _(assert \forall i32 x,y; (x < 0 && y < 0) ==> x * y == -x * -y)
    _(assert \old(a) < 0 && \old(b) < 0 ==> (to_i64(prod) == \old(a) * \old(b)))

    _(assert {:bv} \forall u64 x; (to_i64(x) >= 0) ==>
            ( to_i64((u64)(_(unchecked)(x-1) ^ ((u64) -1))) <= 0 ))
    _(assert {:bv} \forall u64 x; (to_i64(x) >= 0) ==>
            ( to_i64((u64)(_(unchecked)(x-1) ^ ((u64) -1))) == -to_i64(x) ))
    if(sign_a ^ sign_b) {
        _(ghost old_prod = prod)
        _(assert to_i64(prod) >= 0)
        _(assert \old(a) >= 0 && \old(b) < 0 || \old(a) < 0 && \old(b) >= 0)
        prod = _(unchecked)(prod-1) ^ ((u64) -1);
        _(assert to_i64(prod) <= 0)
        _(assert to_i64(prod) == -to_i64(old_prod))
    }
    _(assert \old(a) >= 0 && \old(b) >= 0 ==> (a == \old(a) && b == \old(b)) )
  //  _(assert \old(a) >= 0 && \old(b) >= 0 ==> (to_i64(prod) == \old(a) * \old(b)))
  //  _(assert \old(a) < 0 && \old(b)  < 0 ==> (to_i64(prod) == \old(a) * \old(b)))
    _(assert to_i64(prod) == \old(a) * \old(b))

    *prod_out = to_i64(prod);
    _(assert \old(a) * \old(b) == *prod_out)
}

// this is algorithm three from patterson and hennesey
static void calc_divu(u32 divisor, u32 dividend, u32 *quo_out, u32 *rem_out) 
    _(requires divisor > 0)
    _(requires quo_out != rem_out) // the memory locations to do not overlap
    _(writes quo_out)
    _(writes rem_out)
//    _(ensures dividend == (*quo_out) * divisor + (*rem_out))
{
    u32 idx, quotient, reminder;
    i64 rem;
    u64 rq = dividend;
    _(ghost u32 r;)
    _(ghost u32 q;)

    rq <<= 1;
    
    {
        _(assert {:bv} \forall u64 x; // the key lemma: shows r == dividend
          (_(unchecked)(u32)(((x << 1) & (((u64)0xffffffff) << 1)) >> 1) == (_(unchecked)(u32)x)) );
        // the lemma below points to the bug when reminder is larger than 31 bits
        _(assert {:bv} \forall u64 x; u32 i; (i <= 32) ==> // the generalization of the lemma above
          (_(unchecked)(u32)(((x << i) & (((u64)0xffffffff) << i)) >> i) == (_(unchecked)(u32)x)) );
        _(assert rq <= (((u64) 0xffffffff) << 1));
        _(ghost q = _(unchecked)(u32)((rq & ((((u64)1)<<1)-1)) << 32 ) );
        _(ghost r = _(unchecked)(u32)((rq & (((u64)0xffffffff) << 1)) >> 1) );
        _(assert q == 0);
        _(assert r == dividend);
    }

    for(idx = 0; idx < 32; idx++) 
    _(invariant idx >= 0 && idx <= 32)
//    _(invariant dividend == ((q * divisor) + r)) //TODO: the key invariant
    {
        _(ghost q = _(unchecked)(u32)((rq & ((((u64)1)<<(idx+1))-1)) << (32-idx) ) );
        _(ghost r = _(unchecked)(u32)((rq & (((u64)0xffffffff) << (idx+1))) >> (idx+1)) );

        rem = (i64) ((rq >> 32) & 0xffffffff);
        rem = rem - divisor; //bug: becomes positive when divisor is greater than 0x80000000
        if(rem < 0) {
            rq <<= 1;
        } else { // rem >= 0
            rq = (rq & 0xffffffff) | (((u64) rem) << 32);
            rq <<= 1;
            rq |= 0x1;
        }
    }

    quotient = _(unchecked)(u32) (rq & 0xffffffff);
    reminder = _(unchecked)(u32) (rq >> 33);
    
    *quo_out = quotient;
    *rem_out = reminder;
}


/**********************************************************************************/

/***************** Functions used by multiple instructions ************************/

static void mul_shared(struct CPU *cpu, i32 a, i32 b, u32 rD) 
    _(requires \wrapped(cpu))
    _(requires rD < NUM_REGS)
    _(writes cpu)
{
    i64 prod_out;
    u64 uprod_out;

    calc_mul(a, b, &prod_out);

    cpu_set_gpr(cpu, rD, to_u32(prod_out));

    if((prod_out < (i64) INT_MIN) || (prod_out > (i64) INT_MAX)) {
        cpu_set_ov(cpu, true);
    } else {
        cpu_set_ov(cpu, false);
    }

    calc_mulu(to_u32(a), to_u32(b), &uprod_out);

    if(uprod_out > UINT_MAX) {
        cpu_set_cy(cpu, true);
    } else {
        cpu_set_cy(cpu, false);
    }
}


static void add_base(struct CPU *cpu, bool carry_in, u32 rD, u32 a, u32 b) 
    _(requires \wrapped(cpu))
    _(requires rD < NUM_REGS)
    _(writes cpu)
{
    bool overflow, carry;
    u32 result;

    calc_add(carry_in, a, b, &result, &overflow, &carry);

    cpu_set_gpr(cpu, rD, result);
    cpu_set_ov(cpu, overflow);
    cpu_set_cy(cpu, carry);
}

static void alignment_exception(struct CPU *cpu, struct control *cont, u32 ea)
{
        if(is_in_delay_slot(cpu))
	{
	    /* Address of last branch stored in EPCR */
	    cpu_set_epcr(cpu, cpu_get_pc(cpu) - 4);
	    /* If exception was in delay slot set SR[DSX] */
	    cpu_set_dsx(cpu, 1);
	}
	else
	{
	    /* PC stored in EPCR */
	    cpu_set_epcr(cpu, cpu_get_pc(cpu));
	    /* If exception was in delay slot set SR[DSX] */
	    cpu_set_dsx(cpu, 0);
	}

	/* Set the EEAR to the effective address used for the instruction */
	cpu_set_eear(cpu, ea);

	/* Save the current SR to ESR */
	cpu_set_esr(cpu, cpu_get_sr(cpu));

	/* Set NPC to address of handler */
	cpu_set_npc(cpu, cpu_get_eph(cpu) ? 0xF0000600 : 0x600);

	/* Disable MMUs, go to supervisor mode, and interrupts
	   and timer exceptions disabled */
	cpu_set_dme(cpu, 0);
	cpu_set_ime(cpu, 0);
	cpu_set_sm(cpu, 1);
	cpu_set_iee(cpu, 0);
	cpu_set_tee(cpu, 0);
}

static void range_exception(struct CPU *cpu, struct control *cont)
{
        if(is_in_delay_slot(cpu))
	{
	    /* Address of last branch stored in EPCR */
	    cpu_set_epcr(cpu, cpu_get_pc(cpu) - 4);
	    /* If exception was in delay slot set SR[DSX] */
	    cpu_set_dsx(cpu, 1);
	}
	else
	{
	    /* PC stored in EPCR */
	    cpu_set_epcr(cpu, cpu_get_pc(cpu));
	    /* If exception was in delay slot set SR[DSX] */
	    cpu_set_dsx(cpu, 0);
	}

	/* Save the current SR to ESR */
	cpu_set_esr(cpu, cpu_get_sr(cpu));

	/* Set NPC to address of handler */
	cpu_set_npc(cpu, cpu_get_eph(cpu) ? 0xF0000B00 : 0xB00);

	/* Disable MMUs, go to supervisor mode, and interrupts
	   and timer exceptions disabled */
	cpu_set_dme(cpu, 0);
	cpu_set_ime(cpu, 0);
	cpu_set_sm(cpu, 1);
	cpu_set_iee(cpu, 0);
	cpu_set_tee(cpu, 0);
}

/**********************************************************************************/



/**************************** Instructions ****************************************/


static void unimpl(struct CPU *cpu, struct control *cont) 
//FIXME: think about this
//   _(requires \wrapped(cpu))
//   _(requires \wrapped(cont))
{
    cpu = cpu;
    cont = cont;
    unsigned int insn;
    guestLoad(cpu_get_pc(cpu), &insn);
    myprint("Unimplemented instruction\nPC: 0x%8.8x\nInstruction: 0x%8.8x\nOpcode: 0x%8.8x\n", cpu_get_pc(cpu), insn, cont->opcode);
    assert(false);
// FIXME: ?
//  _(assert false)
//  assert(false);
}


static void muli(struct CPU *cpu, struct control *cont) 
    _(requires \wrapped(cpu))
    _(requires \thread_local(cont))
    _(requires \thread_local(&cpu->regs->gpr[cont->rA]))
    _(requires cont->rA < NUM_REGS)
    _(requires cont->rD < NUM_REGS)
    _(writes cpu)
{
    myprintf("muli r%u,r%u,%u\n", cont->rD, cont->rA, exts(cont->I));
    mul_shared(cpu, to_i32(cpu_get_gpr(cpu, cont->rA)), 
                    exts(cont->I), cont->rD);
    /* Check for range exception */
    if(cpu_get_ove(cpu) && cpu_get_ov(cpu))
    {
      range_exception(cpu, cont);
    }
}

static void mul(struct CPU *cpu, struct control *cont) 
    _(requires \wrapped(cpu))
    _(requires \thread_local(&cpu->regs->gpr[cont->rA]))
    _(requires \thread_local(&cpu->regs->gpr[cont->rB]))
    _(requires \thread_local(cont))
    _(requires cont->rA < NUM_REGS)
    _(requires cont->rB < NUM_REGS)
    _(requires cont->rD < NUM_REGS)
    _(writes cpu)
{
    myprintf("mul r%u,r%u,r%u\n", cont->rD, cont->rA, cont->rB);
    mul_shared(cpu, to_i32(cpu_get_gpr(cpu, cont->rA)), 
                    to_i32(cpu_get_gpr(cpu, cont->rB)), cont->rD);
    /* Check for range exception */
    if(cpu_get_ove(cpu) && cpu_get_ov(cpu))
    {
      range_exception(cpu, cont);
    }
}

static void mulu(struct CPU *cpu, struct control *cont) 
    _(requires \wrapped(cpu))
    _(requires \thread_local(&cpu->regs->gpr[cont->rA]))
    _(requires \thread_local(&cpu->regs->gpr[cont->rB]))
    _(requires \thread_local(cont))
    _(requires cont->rA < NUM_REGS)
    _(requires cont->rB < NUM_REGS)
    _(requires cont->rD < NUM_REGS)
    _(writes cpu)
{
    u64 prod;
    myprintf("mulu r%u,r%u,r%u\n", cont->rD, cont->rA, cont->rB);
    calc_mulu(cpu_get_gpr(cpu, cont->rA), 
              cpu_get_gpr(cpu, cont->rB), &prod);

    cpu_set_gpr(cpu, cont->rD, _(unchecked)(u32)prod);

    cpu_set_ov(cpu, false);
    if(prod > UINT_MAX) {
        cpu_set_cy(cpu, true);
    } else {
        cpu_set_cy(cpu, false);
    }
    /* Check for range exception */
    if(cpu_get_ove(cpu) && cpu_get_ov(cpu))
    {
      range_exception(cpu, cont);
    }
}

static void divu(struct CPU *cpu, struct control *cont) 
    _(requires \thread_local(cont))
    _(requires \thread_local(&cpu->regs->gpr[cont->rA]))
    _(requires \thread_local(&cpu->regs->gpr[cont->rB]))
    _(requires \wrapped(cont))
    _(writes cpu)
{
    u32 q, r;
    u32 divisor, dividend;

    myprintf("divu r%u,r%u,r%u\n", cont->rD, cont->rA, cont->rB);

    divisor  = cpu_get_gpr(cpu, cont->rB);
    dividend = cpu_get_gpr(cpu, cont->rA);
    
    if(divisor != 0) {
        calc_divu(divisor, dividend, &q, &r);
        cpu_set_gpr(cpu, cont->rD, q);
    }
    
    // this is how the hardware defines it, same for div also
    cpu_set_ov(cpu, false);
    cpu_set_cy(cpu, (divisor == 0));

    /* Check for range exception */
    if(cpu_get_ove(cpu) && cpu_get_ov(cpu))
    {
      range_exception(cpu, cont);
    }
}

static void or32_div(struct CPU *cpu, struct control *cont) 
{
    u32 q, r;
    i32 divisor, dividend;
    u32 sign_dsor, sign_dend;

    myprintf("div r%u,r%u,r%u\n", cont->rD, cont->rA, cont->rB);

    divisor  = cpu_get_gpr(cpu, cont->rB);
    dividend = cpu_get_gpr(cpu, cont->rA);

    sign_dsor = divisor & 0x80000000;
    sign_dend = dividend & 0x80000000;

    if(sign_dsor) divisor = (~divisor) + 1;
    if(sign_dend) dividend = (~dividend) + 1;

    if(divisor != 0) {
        calc_divu(divisor, dividend, &q, &r);

        if(sign_dsor ^ sign_dend) {
            q = ~(q-1);
        }

        cpu_set_gpr(cpu, cont->rD, q);
    }

    // this is how the hardware defines it
    cpu_set_ov(cpu, false);
    cpu_set_cy(cpu, (divisor == 0));

    /* Check for range exception */
    if(cpu_get_ove(cpu) && cpu_get_ov(cpu))
    {
      range_exception(cpu, cont);
    }
}

static void fl1(struct CPU *cpu, struct control *cont) 
    _(requires \wrapped(cpu))
    _(requires \thread_local(&cpu->regs->gpr[cont->rA]))
    _(requires \thread_local(cont))
    _(requires \wrapped(cont))
    _(writes cpu)
{
    u32 a;
    u32 idx;

    a = cpu_get_gpr(cpu, cont->rA);
    for(idx = 0; idx < 32; idx++) 
        _(invariant idx<=32)
    {
        if(a & (1<<(31-idx)))
            break;
    }
    _(assert idx <= 32)
    cpu_set_gpr(cpu, cont->rD, 32-idx);

}

static void ff1(struct CPU *cpu, struct control *cont) 
{
    u32 a;
    u32 idx;

    a = cpu_get_gpr(cpu, cont->rA);
    for(idx = 0; idx < 32; idx++) 
        _(invariant idx<=32)
    {
        if(a & (1<<idx))
            break;
    }
    _(assert idx <= 32);
    if(idx == 32)
        idx = (u32) -1;
    cpu_set_gpr(cpu, cont->rD, idx+1);

}

static void mac(struct CPU *cpu, struct control *cont) 
    _(requires \thread_local(cpu))
    _(requires \thread_local(&cpu->regs->gpr[cont->rA]))
    _(requires \thread_local(&cpu->regs->gpr[cont->rB]))
    _(requires \thread_local(cont))
    _(requires cont->rA < NUM_REGS)
    _(requires cont->rB < NUM_REGS)
{
    i32 rA, rB;
    i64 mac, r;
    //FIXME: cpu_get_mac should imply that the cont->opcode == OP_MACI or OP_MAC or OP_MSB)
    mac = _(unchecked)cpu_get_mac(cpu);
    //FIXME: contract for cpu_get_gpr
    rA = _(unchecked)(i32)cpu_get_gpr(cpu, cont->rA);
    rB = _(unchecked)(i32)cpu_get_gpr(cpu, cont->rB);
    calc_mul(rA, rB, &r);
    _(unchecked) mac += r;
    cpu_set_mac(cpu, mac);
}

static void msb(struct CPU *cpu, struct control *cont) 
    _(requires \thread_local(cpu))
    _(requires \thread_local(&cpu->regs->gpr[cont->rA]))
    _(requires \thread_local(&cpu->regs->gpr[cont->rB]))
    _(requires \thread_local(cont))
    _(requires cont->rA < NUM_REGS)
    _(requires cont->rB < NUM_REGS)
{
    i32 rA, rB;
    i64 mac, r;
    //FIXME: cpu_get_mac should imply that the cont->opcode == OP_MACI or OP_MAC or OP_MSB)
    mac = _(unchecked)cpu_get_mac(cpu);
    //FIXME: contract for cpu_get_gpr
    rA = _(unchecked)(i32)cpu_get_gpr(cpu, cont->rA);
    rB = _(unchecked)(i32)cpu_get_gpr(cpu, cont->rB);
    calc_mul(rA, rB, &r);
    _(unchecked) mac -= r;
    cpu_set_mac(cpu, mac);
}

static void maci(struct CPU *cpu, struct control *cont) 
    _(requires \thread_local(cpu))
    _(requires \thread_local(&cpu->regs->gpr[cont->rA]))
    _(requires \thread_local(cont))
    _(requires cont->rA < NUM_REGS)
{
    i32 a, imm;
    i64 m, r;
    //FIXME: cpu_get_mac should imply that the cont->opcode == OP_MACI or OP_MAC or OP_MSB)
    m = _(unchecked)cpu_get_mac(cpu);
    //FIXME: contract for cpu_get_gpr
    a = _(unchecked)(i32)cpu_get_gpr(cpu, cont->rA);
    //FIXME: _(assert cont->opcode == OP_MACI) implies that I part contains 11 bits
    _(assume cont->I < (1<<11)-1)
    imm = sign_extend(cont->I, 10);
    calc_mul(a, imm, &r);
     _(unchecked) m += r;
    cpu_set_mac(cpu, m);
}
    

static void addi(struct CPU *cpu, struct control *cont)
    _(requires \wrapped(cpu))
    _(requires \thread_local(cont))
    _(requires \wrapped(cont))
    _(writes cpu)
{    
    myprintf("addi r%u,r%u,0x%x\n", cont->rD, cont->rA, exts(cont->I));
    add_base(cpu, false, cont->rD, cpu_get_gpr(cpu, cont->rA), to_u32(exts(cont->I)));
    /* Check for range exception */
    if(cpu_get_ove(cpu) && cpu_get_ov(cpu))
    {
      range_exception(cpu, cont);
    }
}

static void addic(struct CPU *cpu, struct control *cont)
    _(requires \wrapped(cpu))
    _(requires \thread_local(cont))
    _(requires \wrapped(cont))
    _(writes cpu)
{    
    myprintf("addic r%u,r%u,0x%x\n", cont->rD, cont->rA, exts(cont->I));
    add_base(cpu, cpu_get_cy(cpu), cont->rD, cpu_get_gpr(cpu, cont->rA), to_u32(exts(cont->I)));
    /* Check for range exception */
    if(cpu_get_ove(cpu) && cpu_get_ov(cpu))
    {
      range_exception(cpu, cont);
    }
}

static void add(struct CPU *cpu, struct control *cont) 
    _(requires \wrapped(cpu))
    _(requires \thread_local(cont))
    _(requires \wrapped(cont))
    _(writes cpu)
{ 
    myprintf("add r%u,r%u,r%u\n", cont->rD, cont->rA, cont->rB);
    add_base(cpu, false, cont->rD, cpu_get_gpr(cpu, cont->rA), cpu_get_gpr(cpu, cont->rB));
    /* Check for range exception */
    if(cpu_get_ove(cpu) && cpu_get_ov(cpu))
    {
      range_exception(cpu, cont);
    }
}

static void addc(struct CPU *cpu, struct control *cont) 
    _(requires \wrapped(cpu))
    _(requires \thread_local(cont))
    _(requires \wrapped(cont))
    _(writes cpu)
{ 
    myprintf("addc r%u,r%u,r%u\n", cont->rD, cont->rA, cont->rB);
    add_base(cpu, cpu_get_cy(cpu), cont->rD, cpu_get_gpr(cpu, cont->rA), cpu_get_gpr(cpu, cont->rB));
    /* Check for range exception */
    if(cpu_get_ove(cpu) && cpu_get_ov(cpu))
    {
      range_exception(cpu, cont);
    }
}

static void sub(struct CPU *cpu, struct control *cont) 
    _(requires \wrapped(cpu))
    _(requires \thread_local(cont))
    _(requires \wrapped(cont))
    _(writes cpu)
{ 
    i32 a, b, r;

    myprintf("sub r%u,r%u,r%u\n", cont->rD, cont->rA, cont->rB);
    
    a = (i32) cpu_get_gpr(cpu, cont->rA);
    b = (i32) cpu_get_gpr(cpu, cont->rB);
    
    add_base(cpu, false, cont->rD, a, -b);

    r = (i32) cpu_get_gpr(cpu, cont->rD);

    if((u32) b > (u32) a) {
        cpu_set_cy(cpu, true);
    } else {
        cpu_set_cy(cpu, false);
    }

    if((( a <  0) &&
        ( b >= 0) &&
        ( r >= 0)) ||
       (( a >= 0) &&
        ( b <  0) &&
        ( r <  0))) {
        cpu_set_ov(cpu, true);
    } else {
        cpu_set_ov(cpu, false);
    }

    /* Check for range exception */
    if(cpu_get_ove(cpu) && cpu_get_ov(cpu))
    {
      range_exception(cpu, cont);
    }
}

static void ori(struct CPU *cpu, struct control *cont) 
    _(requires \wrapped(cpu))
    _(requires \thread_local(cont))
    _(requires \wrapped(cont))
    _(writes cpu)
{
    myprintf("ori r%u,r%u,0x%x\n", cont->rD, cont->rA, cont->K);
    cpu_set_gpr(cpu, cont->rD, cpu_get_gpr(cpu, cont->rA) | cont->K);
}

static void and(struct CPU *cpu, struct control *cont) 
    _(requires \wrapped(cpu))
    _(requires \thread_local(cont))
    _(requires \wrapped(cont))
    _(writes cpu)
{
    myprintf("and r%u,r%u,r%u\n", cont->rD, cont->rA, cont->rB);
    cpu_set_gpr(cpu, cont->rD, cpu_get_gpr(cpu, cont->rA) & cpu_get_gpr(cpu, cont->rB));
}

static void xor(struct CPU *cpu, struct control *cont) 
    _(requires \wrapped(cpu))
    _(requires \thread_local(cont))
    _(requires \wrapped(cont))
    _(writes cpu)
{
    myprintf("xor r%u,r%u,r%u\n", cont->rD, cont->rA, cont->rB);
    cpu_set_gpr(cpu, cont->rD, cpu_get_gpr(cpu, cont->rA) ^ cpu_get_gpr(cpu, cont->rB));
}

static void xori(struct CPU *cpu, struct control *cont) 
    _(requires \wrapped(cpu))
    _(requires \thread_local(cont))
    _(requires \wrapped(cont))
    _(writes cpu)
{
    myprintf("xori r%u,r%u,%u\n", cont->rD, cont->rA, cont->I);
    cpu_set_gpr(cpu, cont->rD, cpu_get_gpr(cpu, cont->rA) ^ (u32) exts(cont->I));
}

static void or(struct CPU *cpu, struct control *cont) 
    _(requires \wrapped(cpu))
    _(requires \thread_local(cont))
    _(requires \wrapped(cont))
    _(writes cpu)
{
    myprintf("or r%u,r%u,r%u\n", cont->rD, cont->rA, cont->rB);
    cpu_set_gpr(cpu, cont->rD, cpu_get_gpr(cpu, cont->rA) | cpu_get_gpr(cpu, cont->rB));
}

static void extws(struct CPU *cpu, struct control *cont) 
    _(requires \thread_local(cont))
    _(requires \wrapped(cont))
    _(requires \wrapped(cpu))
    _(writes cpu)
{
    myprintf("extws r%u,r%u\n", cont->rD, cont->rA);
    cpu_set_gpr(cpu, cont->rD, cont->rA);
}

static void extwz(struct CPU *cpu, struct control *cont) 
    _(requires \thread_local(cont))
    _(requires \wrapped(cont))
    _(requires \wrapped(cpu))
    _(writes cpu)
{
    myprintf("extwz r%u,r%u\n", cont->rD, cont->rA);
    cpu_set_gpr(cpu, cont->rD, cont->rA);
}

static void exths(struct CPU *cpu, struct control *cont) 
    _(requires \thread_local(cont))
    _(requires \wrapped(cont))
    _(requires \wrapped(cpu))
    _(writes cpu)
{
    i32 result;
    u32 input;
    myprintf("exths r%u,r%u\n", cont->rD, cont->rA);
    input = cpu_get_gpr(cpu, cont->rA);
    result = sign_extend(input & 0xffff, 15);
    //_(assert input & 0xffff == ((u32)result & 0xffff));
    //_(assert result & 0xffff == input & 0xffff);
    //_(assert IS_BIT_SET(input, 15) ==> (result & 0xffff0000) == 0xffff0000);
    cpu_set_gpr(cpu, cont->rD, (u32) _(unchecked) result);
}

static void extbs(struct CPU *cpu, struct control *cont) 
    _(requires \thread_local(&cpu->regs->gpr[cont->rA]))
    _(requires \thread_local(cont))
    _(requires \wrapped(cont))
    _(requires \wrapped(cpu))
    _(ensures  \wrapped(cont))
    _(ensures  \wrapped(cpu))
    _(writes cpu)
    _(ensures (!cont->rA && cont->rD) ==> (cpu->regs->gpr[cont->rD] == 0))
    _(ensures  !cont->rD ==> cpu->regs->gpr[cont->rD] == \old(cpu->regs->gpr[cont->rD]))
    _(ensures cont->rA && cont->rD && bit_set(cpu->regs->gpr[cont->rA] & 0xff, 7) ==> 
             ((cpu->regs->gpr[cont->rD] & 0xffffff80) == 0xffffff80))
    _(ensures  cont->rA && cont->rD ==> 
     (cpu->regs->gpr[cont->rD] & 0xff) == ((cpu->regs->gpr[cont->rA] & 0xff)) )
{
    i32 result;
    u32 input;
    _(ghost u32 uresult;)
      myprintf("extbs r%u,r%u\n", cont->rD, cont->rA);
    input = cpu_get_gpr(cpu, cont->rA);
    _(assert cont->rA == 0 ==> (input == 0))
    _(assert cont->rA != 0 ==> (input == cpu->regs->gpr[cont->rA]))
    result = sign_extend(input & 0xff, 7);
    _(ghost uresult = to_u32(result))

    _(assert  bit_set(input & 0xff, 7) ==> result <  0)
    _(assert !bit_set(input & 0xff, 7) ==> result >= 0)
    _(assert  bit_set(input & 0xff, 7) ==> ((uresult & 0xff) == (input & 0xff)))
    _(assert !bit_set(input & 0xff, 7) ==>  (uresult         == (input & 0xff) ))
    _(assert {:bv} \forall u32 x; (x & 0xff) == ((x & 0xff) & 0xff))
    _(assert  _(unchecked)(uresult & 0xff) == (input & 0xff))
   
    // suprisingly, the lemma below is crucial for proving the last two assertions
    _(assert {:bv} \forall u32 x;(x==7) ==> (0xffffff80==(0xffffffff << x)))
    _(assert bit_set(input & 0xff, 7) ==> (uresult >= 0xffffff80))
    _(assert bit_set(input & 0xff, 7) ==> ((uresult & 0xffffff80) == 0xffffff80))
  
    _(assert  cont->rA && cont->rA != cont->rD ==> (cpu->regs->gpr[cont->rA] == input))
    cpu_set_gpr(cpu, cont->rD, to_u32(result));
    _(assert  cont->rA && cont->rA != cont->rD ==> (cpu->regs->gpr[cont->rA] == input))
    _(assert  cont->rD ==> (cpu->regs->gpr[cont->rD] == uresult))
    _(assert !cont->rA && cont->rD ==> (cpu->regs->gpr[cont->rD] == 0))
    _(assert !cont->rD ==> cpu->regs->gpr[cont->rD] == \old(cpu->regs->gpr[cont->rD]))
    _(assert  cont->rA && cont->rD ==> 
     (cpu->regs->gpr[cont->rD] & 0xff) == ((cpu->regs->gpr[cont->rA] & 0xff)) )
    _(assert cont->rA  && cont->rD  && bit_set(cpu->regs->gpr[cont->rA] & 0xff, 7)==> 
             ((cpu->regs->gpr[cont->rD] & 0xffffff80) == 0xffffff80))
}

static void extbz(struct CPU *cpu, struct control *cont) 
    _(requires \wrapped(cpu))
    _(requires \thread_local(cont))
    _(requires \wrapped(cont))
    _(writes cpu)
{
    u32 result;
    myprintf("extbz r%u,r%u\n", cont->rD, cont->rA);
    result = zero_extend(cpu_get_gpr(cpu, cont->rA), 8);
    _(assert result <= 0xff);
    cpu_set_gpr(cpu, cont->rD, result);
}

static void exthz(struct CPU *cpu, struct control *cont) 
    _(requires \thread_local(cont))
    _(requires \wrapped(cont))
    _(requires \wrapped(cpu))
    _(writes cpu)
{
    u32 result;
    myprintf("exthz r%u,r%u\n", cont->rD, cont->rA);
    result = zero_extend(cpu_get_gpr(cpu, cont->rA), 16);
    _(assert result <= 0xffff);
    cpu_set_gpr(cpu, cont->rD, result);
}

static void srli(struct CPU *cpu, struct control *cont) {
    u32 rA;

    myprintf("srli r%u,r%u,%u\n", cont->rD, cont->rA, cont->L);

    rA = cpu_get_gpr(cpu, cont->rA);
    rA >>= cont->L;
    cpu_set_gpr(cpu, cont->rD, rA);
}

static void srai(struct CPU *cpu, struct control *cont) {
    u32 rA;

    myprintf("srai r%u,r%u,%u\n", cont->rD, cont->rA, cont->L);

    rA = cpu_get_gpr(cpu, cont->rA);
    rA >>= cont->L;
    if(cont->L > 0) {
        rA = sign_extend(rA, (31-cont->L));
    }
    cpu_set_gpr(cpu, cont->rD, rA);
}

static void slli(struct CPU *cpu, struct control *cont) {
    u32 rA;

    myprintf("slli r%u,r%u,%u\n", cont->rD, cont->rA, cont->L);

    rA = cpu_get_gpr(cpu, cont->rA);
    rA <<= cont->L;
    cpu_set_gpr(cpu, cont->rD, rA);
}

static void sll(struct CPU *cpu, struct control *cont) {
    u32 rA;

    myprintf("sll r%u,r%u,r%u\n", cont->rD, cont->rA, cont->rB);

    rA = cpu_get_gpr(cpu, cont->rA);
    rA <<= (cpu_get_gpr(cpu, cont->rB)&0x1f);
    cpu_set_gpr(cpu, cont->rD, rA);
}

static void srl(struct CPU *cpu, struct control *cont) {
    myprintf("srl r%u,r%u,r%u\n", cont->rD, cont->rA, cont->rB);
    cpu_set_gpr(cpu, cont->rD, cpu_get_gpr(cpu, cont->rA) >> cpu_get_gpr(cpu, cont->rB));
}

static void sra(struct CPU *cpu, struct control *cont) {
    u32 rA;
    u32 shift;

    myprintf("sra r%u,r%u,r%u\n", cont->rD, cont->rA, cont->rB);

    rA = cpu_get_gpr(cpu, cont->rA);
    shift = cpu_get_gpr(cpu, cont->rB) & 0x1f; 
    rA >>= shift;
    if(shift > 0) {
        rA = sign_extend(rA, 31-shift);
    }
    cpu_set_gpr(cpu, cont->rD, rA);
}


static void ror(struct CPU *cpu, struct control *cont) {
    u32 rA;
    u32 shift;

    myprintf("ror r%u,r%u,r%u\n", cont->rD, cont->rA, cont->rB);

    rA = cpu_get_gpr(cpu, cont->rA);
    shift = cpu_get_gpr(cpu, cont->rB) & 0x1f; 
    rA = (rA >> shift) | (rA << (0x1f-shift));
    cpu_set_gpr(cpu, cont->rD, rA);
}

static void rori(struct CPU *cpu, struct control *cont) {
    u32 rA;
    u32 shift;

    myprintf("rori r%u,r%u,%u\n", cont->rD, cont->rA, cont->L);

    rA = cpu_get_gpr(cpu, cont->rA);
    shift = cont->L;
    rA = (rA >> shift) | (rA << (0x1f-shift));
    cpu_set_gpr(cpu, cont->rD, rA);
}

static void cmov(struct CPU *cpu, struct control *cont) {
  bool flag = cpu_get_f(cpu);

    myprintf("cmov r%u,r%u,r%u\n", cont->rD, cont->rA, cont->rB);
    cpu_set_gpr(cpu, cont->rD, (flag ? cpu_get_gpr(cpu, cont->rA) : cpu_get_gpr(cpu, cont->rB)));
}


static void bf(struct CPU *cpu, struct control *cont) 
    _(requires \thread_local(cont))
    _(requires \wrapped(cont))
{     
    myprintf("bf 0x%x\n", cpu_get_pc(cpu) + (u32) sign_extend(cont->N << 2, 27));
    if(cpu_is_set_f(cpu)) {
        cpu_set_branch_pc(cpu, _(unchecked) (cpu_get_pc(cpu) + _(unchecked)(u32) sign_extend(cont->N << 2, 27)));
    }
}

static void bnf(struct CPU *cpu, struct control *cont) 
    _(requires \thread_local(cont))
    _(requires \wrapped(cont))
{     
    myprintf("bnf 0x%x\n", cpu_get_pc(cpu) + (u32) sign_extend(cont->N << 2, 27));
    if(!cpu_is_set_f(cpu)) {
        cpu_set_branch_pc(cpu, _(unchecked) (cpu_get_pc(cpu) + _(unchecked)(u32) sign_extend(cont->N << 2, 27)));
    }
}

static void j(struct CPU *cpu, struct control *cont) 
    _(requires \thread_local(cont))
    _(requires \wrapped(cont))
{ 
    myprintf("j 0x%x\n", cpu_get_pc(cpu) + (u32) sign_extend(cont->N << 2, 27));
    cpu_set_branch_pc(cpu, _(unchecked) (cpu_get_pc(cpu) + (u32) sign_extend(cont->N << 2, 27)));
}

static void jr(struct CPU *cpu, struct control *cont) 
    _(requires \thread_local(cpu))
    _(requires \thread_local(&cpu->regs->gpr[cont->rB]))
    _(requires \thread_local(cont))
    _(requires \wrapped(cont))
    
{ 
    myprintf("jr r%u\n", cont->rB);
    cpu_set_branch_pc(cpu, cpu_get_gpr(cpu, cont->rB));
}


static void jal(struct CPU *cpu, struct control *cont) 
    _(requires \thread_local(cont))
    _(requires \wrapped(cont))
{ 
    myprintf("jal 0x%x\n", cpu_get_pc(cpu) + (u32) sign_extend(cont->N << 2, 27));
    cpu_set_branch_pc(cpu, _(unchecked) (cpu_get_pc(cpu) + to_u32(sign_extend(cont->N << 2, 27))));
    cpu_set_lr(cpu, _(unchecked) (cpu_get_pc(cpu)+8));
}

static void jalr(struct CPU *cpu, struct control *cont) 
    _(requires \thread_local(cont))
    _(requires \wrapped(cont))
{ 
    u32 address = cpu_get_gpr(cpu, cont->rB);
    myprintf("jalr r%u\n", cont->rB);
    if(address & 0x3)
    {
      alignment_exception(cpu, cont, address);
    }
    else
    {
      cpu_set_branch_pc(cpu, address);
      cpu_set_lr(cpu, _(unchecked) (cpu_get_pc(cpu)+8));
    }
}

static void lwz(struct CPU *cpu, struct control *cont) 
    _(requires \thread_local(&cpu->regs->gpr[cont->rA]))
    _(requires \wrapped(cpu))
    _(requires \thread_local(cont))
    _(requires \wrapped(cont))
    _(writes cpu)
{
    u32 ea, value;
    myprintf("lwz r%u,%d(r%u)\n", cont->rD, exts(cont->I), cont->rA);
    ea =  _(unchecked) (to_u32(exts(cont->I)) + cpu_get_gpr(cpu, cont->rA));
    if(ea & 0x3)
    {
      alignment_exception(cpu, cont, ea);
    }
    else
    {
      guestLoad(ea, &value);
      cpu_set_gpr(cpu, cont->rD, value);
    }
}

static void lbz(struct CPU *cpu, struct control *cont) 
    _(requires \thread_local(&cpu->regs->gpr[cont->rA]))
    _(requires \wrapped(cpu))
    _(requires \thread_local(cont))
    _(requires \wrapped(cont))
    _(writes cpu)
{
    u32 ea, value, shift;

    myprintf("lbz r%u,%d(r%u)\n", cont->rD, exts(cont->I), cont->rA);
    ea =  _(unchecked) (to_u32(exts(cont->I)) + cpu_get_gpr(cpu, cont->rA));
    guestLoad(ea & ~0x3, &value);
    
    shift = (0x3-(ea & 0x3)) * 8;

    cpu_set_gpr(cpu, cont->rD, (value>>shift) & 0xff);
}

static void lbs(struct CPU *cpu, struct control *cont) 
    _(requires \thread_local(&cpu->regs->gpr[cont->rA]))
    _(requires \wrapped(cpu))
    _(requires \thread_local(cont))
    _(requires \wrapped(cont))
    _(writes cpu)
{

    u32 ea, value, shift;

    myprintf("lbs r%u,%d(r%u)\n", cont->rD, exts(cont->I), cont->rA);
    ea =  _(unchecked) (to_u32(exts(cont->I)) + cpu_get_gpr(cpu, cont->rA));
    guestLoad(ea & ~0x3, &value);
    
    shift = (0x3-(ea & 0x3)) * 8;

    cpu_set_gpr(cpu, cont->rD, sign_extend((value>>shift) & 0xff, 7));
}

static void lhz(struct CPU *cpu, struct control *cont) 
    _(requires \thread_local(&cpu->regs->gpr[cont->rA]))
    _(requires \wrapped(cpu))
    _(requires \thread_local(cont))
    _(requires \wrapped(cont))
    _(writes cpu)
{

    u32 ea, value, shift;
    
    myprintf("lhz r%u,%d(r%u)\n", cont->rD, exts(cont->I), cont->rA);
    ea =  _(unchecked) (to_u32(exts(cont->I)) + cpu_get_gpr(cpu, cont->rA));

    if(ea & 0x1)
    {
      alignment_exception(cpu, cont, ea);
    }
    else
    {
      /* Load a word and shift out garbage */
    guestLoad(ea & ~0x3, &value);
    shift = (ea & 0x3) == 0 ? 16 : 0;

    cpu_set_gpr(cpu, cont->rD, (value >> shift) & 0xffff);
    }
}

static void lhs(struct CPU *cpu, struct control *cont) 
    _(requires \thread_local(&cpu->regs->gpr[cont->rA]))
    _(requires \wrapped(cpu))
    _(requires \thread_local(cont))
    _(requires \wrapped(cont))
    _(writes cpu)
{

    u32 ea, value, shift;
    
    myprintf("lhs r%u,%d(r%u)\n", cont->rD, exts(cont->I), cont->rA);
    ea =  _(unchecked) (to_u32(exts(cont->I)) + cpu_get_gpr(cpu, cont->rA));

    if(ea & 0x1)
    {
      alignment_exception(cpu, cont, ea);
    }
    else
    {
      /* Load a word and shift out garbage */
    guestLoad(ea & ~0x3, &value);
    shift = (ea & 0x3) == 0 ? 16 : 0;

    cpu_set_gpr(cpu, cont->rD, sign_extend((value >> shift) & 0xffff, 15));
    }
}

static void sw(struct CPU *cpu, struct control *cont) 
    _(requires \thread_local(cpu))
    _(requires \thread_local(&cpu->regs->gpr[cont->rA]))
    _(requires \thread_local(&cpu->regs->gpr[cont->rB]))
    _(requires \thread_local(cont))
    _(requires \wrapped(cont))
{
    i32 imm = exts(cont->I);
    u32 ea = _(unchecked) (to_u32(imm) + cpu_get_gpr(cpu, cont->rA));

    myprintf("sw %d(r%u), r%u ([0x%08x] <- 0x%08x)\n",
             imm, cont->rA, cont->rB, ea, cpu_get_gpr(cpu, cont->rB));

    if(ea & 0x3)
    {
      alignment_exception(cpu, cont, ea);
    }
    else
    {
      guestStore(ea, cpu_get_gpr(cpu, cont->rB));
    }
}

static void sb(struct CPU *cpu, struct control *cont) 
    _(requires \thread_local(cpu))
    _(requires \thread_local(&cpu->regs->gpr[cont->rA]))
    _(requires \thread_local(&cpu->regs->gpr[cont->rB]))
    _(requires \thread_local(cont))
    _(requires \wrapped(cont))
{
    i32 imm = exts(cont->I);
    u32 ea = _(unchecked) (to_u32(imm) + cpu_get_gpr(cpu, cont->rA));
    u32 value, shift, mask;

    myprintf("sb %d(r%u), r%u ([0x%08x] <- 0x%08x)\n",
             imm, cont->rA, cont->rB, ea, cpu_get_gpr(cpu, cont->rB));
    
    guestLoad(ea & ~0x3, &value);
    shift = (0x3-(ea & 0x3)) * 8;
    mask = 0xff << shift;

    value &= ~mask;
    value |= (cpu_get_gpr(cpu, cont->rB) & 0xff) << shift;

    guestStore(ea & ~0x3, value);
}

static void sh(struct CPU *cpu, struct control *cont) 
    _(requires \thread_local(cpu))
    _(requires \thread_local(&cpu->regs->gpr[cont->rA]))
    _(requires \thread_local(&cpu->regs->gpr[cont->rB]))
    _(requires \thread_local(cont))
    _(requires \wrapped(cont))
{
    i32 imm = exts(cont->I);
    u32 ea = _(unchecked) (to_u32(imm) + cpu_get_gpr(cpu, cont->rA));
    u32 value, mask, shift;

    myprintf("sh %d(r%u), r%u ([0x%08x] <- 0x%08x)\n",
             imm, cont->rA, cont->rB, ea, cpu_get_gpr(cpu, cont->rB));
    if(ea & 0x1)
    {
      alignment_exception(cpu, cont, ea);
    }
    else
    {
      /* Operate on word sized chunks */
      /* Only overwrite the specified half-word */
    guestLoad(ea & ~0x3, &value);

    shift = (ea & 3) == 0 ? 16 : 0;
    mask = 0xffff << shift;
    
    value &= ~mask;
    value |= (cpu_get_gpr(cpu, cont->rB) & 0xffff) << shift;

    guestStore(ea & ~0x3, value);
    }
}


static void or32_nop(struct CPU *cpu, struct control *cont) {
#ifdef SIMULATOR_TEST
    if(cont->K == 2) {
      myprint("report(%8.8x: 0x%8.8x)\n", cpu->regs->pc, cpu_get_gpr(cpu, 3));
    } else if(cont->K == 1) {
      myprint("exit (%d)\n", cpu_get_gpr(cpu, 3));
      exit(cpu_get_gpr(cpu, 3));
    } else if(cont->K == 4) {
        printf("%c", (char) cpu_get_gpr(cpu, 3));
    } else if(cont->K != 0) {
        myprintf("l.nop %d\n", cont->K);
    }
#endif
    cpu = cpu;
    cont = cont;
}

static void sfnei(struct CPU *cpu, struct control *cont) 
    _(requires \thread_local(cpu))
    _(requires \thread_local(&cpu->regs->gpr[cont->rA]))
    _(requires \thread_local(cont))
    _(requires \wrapped(cont))
{
    myprintf("sfnei r%d, 0x%x\n", cont->rA, exts(cont->I));
    cpu_set_f(cpu, to_i32(cpu_get_gpr(cpu, cont->rA)) != exts(cont->I));
}

static void sfne(struct CPU *cpu, struct control *cont) 
    _(requires \thread_local(cpu))
    _(requires \thread_local(&cpu->regs->gpr[cont->rA]))
    _(requires \thread_local(cont))
    _(requires \wrapped(cont))
{
    myprintf("sfne r%u r%u\n", cont->rA, cont->rB);
    cpu_set_f(cpu, cpu_get_gpr(cpu, cont->rA) != cpu_get_gpr(cpu, cont->rB));
}

static void sfeq(struct CPU *cpu, struct control *cont) 
    _(requires \thread_local(&cpu->regs->gpr[cont->rA]))
    _(requires \thread_local(&cpu->regs->gpr[cont->rB]))
    _(requires \thread_local(cont))
    _(requires cont->rA < NUM_REGS)
    _(requires cont->rB < NUM_REGS)
    _(writes cpu)
{
    myprintf("sfeq r%u, r%u\n", cont->rA, cont->rB);
    cpu_set_f(cpu, cpu_get_gpr(cpu, cont->rA) == cpu_get_gpr(cpu, cont->rB));
}


static void sfeqi(struct CPU *cpu, struct control *cont) 
    _(requires \thread_local(&cpu->regs->gpr[cont->rA]))
    _(requires \thread_local(&cpu->regs->gpr[cont->rB]))
    _(requires \thread_local(cont))
    _(requires cont->rA < NUM_REGS)
    _(requires cont->rB < NUM_REGS)
    _(writes cpu)
{
    myprintf("sfeqi r%u,%u\n", cont->rA, cont->I);
    cpu_set_f(cpu, cpu_get_gpr(cpu, cont->rA) == (u32) exts(cont->I));
}

static void sfltu(struct CPU *cpu, struct control *cont) {
    myprintf("sfltu r%u, r%u\n", cont->rA, cont->rB);
    cpu_set_f(cpu, cpu_get_gpr(cpu, cont->rA) < cpu_get_gpr(cpu, cont->rB));
}

static void sfltui(struct CPU *cpu, struct control *cont) {
    myprintf("sfltui r%u, r%u\n", cont->rA, cont->I);
    cpu_set_f(cpu, cpu_get_gpr(cpu, cont->rA) < (u32) exts(cont->I));
}

static void sflts(struct CPU *cpu, struct control *cont) {
    myprintf("sflts r%u, r%u\n", cont->rA, cont->rB);
    cpu_set_f(cpu, (i32) cpu_get_gpr(cpu, cont->rA) < (i32) cpu_get_gpr(cpu, cont->rB));
}

static void sfltsi(struct CPU *cpu, struct control *cont) {
    myprintf("sfltsi r%u, r%u\n", cont->rA, cont->I);
    cpu_set_f(cpu, (i32) cpu_get_gpr(cpu, cont->rA) < exts(cont->I));
}

static void sfleu(struct CPU *cpu, struct control *cont) {
    myprintf("sfleu r%u, r%u\n", cont->rA, cont->rB);
    cpu_set_f(cpu, cpu_get_gpr(cpu, cont->rA) <= cpu_get_gpr(cpu, cont->rB));
}

static void sfleui(struct CPU *cpu, struct control *cont) {
    myprintf("sfleui r%u, %u\n", cont->rA, cont->I);
    cpu_set_f(cpu, cpu_get_gpr(cpu, cont->rA) <= (u32) exts(cont->I));
}

static void sfles(struct CPU *cpu, struct control *cont) {
    myprintf("sfles r%u, r%u\n", cont->rA, cont->rB);
    cpu_set_f(cpu, (i32) cpu_get_gpr(cpu, cont->rA) <= (i32) cpu_get_gpr(cpu, cont->rB));
}

static void sflesi(struct CPU *cpu, struct control *cont) {
    myprintf("sflesi r%u, %u\n", cont->rA, cont->I);
    cpu_set_f(cpu, (i32) cpu_get_gpr(cpu, cont->rA) <= exts(cont->I));
}

static void sfgtu(struct CPU *cpu, struct control *cont) {
    myprintf("sfgtu r%u, r%u\n", cont->rA, cont->rB);
    cpu_set_f(cpu, cpu_get_gpr(cpu, cont->rA) > cpu_get_gpr(cpu, cont->rB));
}

static void sfgts(struct CPU *cpu, struct control *cont) {
    myprintf("sfgts r%u, r%u\n", cont->rA, cont->rB);
    cpu_set_f(cpu, (i32) cpu_get_gpr(cpu, cont->rA) > (i32) cpu_get_gpr(cpu, cont->rB));
}

static void sfgtsi(struct CPU *cpu, struct control *cont) {
    myprintf("sfgtsi r%u, r%u\n", cont->rA, cont->I);
    cpu_set_f(cpu, (i32) cpu_get_gpr(cpu, cont->rA) > exts(cont->I));
}

static void sfgeu(struct CPU *cpu, struct control *cont) {
    myprintf("sfgeu r%u, r%u\n", cont->rA, cont->rB);
    cpu_set_f(cpu, cpu_get_gpr(cpu, cont->rA) >= cpu_get_gpr(cpu, cont->rB));
}

static void sfges(struct CPU *cpu, struct control *cont) {
    myprintf("sfges r%u, r%u\n", cont->rA, cont->rB);
    cpu_set_f(cpu, (i32) cpu_get_gpr(cpu, cont->rA) >= (i32) cpu_get_gpr(cpu, cont->rB));
}

static void sfgesi(struct CPU *cpu, struct control *cont) {
    myprintf("sfgesi r%u, r%u\n", cont->rA, cont->I);
    cpu_set_f(cpu, (i32) cpu_get_gpr(cpu, cont->rA) >= exts(cont->I));
}

static void sfgtui(struct CPU *cpu, struct control *cont) {
    myprintf("sfgtui r%u, r%u\n", cont->rA, cont->rB);
    cpu_set_f(cpu, cpu_get_gpr(cpu, cont->rA) > (u32) exts(cont->I));
}

static void sfgeui(struct CPU *cpu, struct control *cont) {
    myprintf("sfgeui r%u, %u\n", cont->rA, exts(cont->I));
    cpu_set_f(cpu, cpu_get_gpr(cpu, cont->rA) >= (u32) exts(cont->I));
}

static void sfi(struct CPU *cpu, struct control *cont) 
    _(requires \thread_local(cpu))
    _(requires \thread_local(&cpu->regs->gpr[cont->rA]))
    _(requires \thread_local(cont))
    _(requires \wrapped(cont))
{
    switch(cont->sf_op) {
    case SFNE_OP:
        sfnei(cpu, cont);
        break;
    case SFGTU_OP:
        sfgtui(cpu, cont);
        break;
    case SFEQ_OP:
        sfeqi(cpu, cont);
        break;
    case SFGEU_OP:
        sfgeui(cpu, cont);
        break;
    case SFGES_OP:
        sfgesi(cpu, cont);
        break;
    case SFLTU_OP:
        sfltui(cpu, cont);
        break;
    case SFLTS_OP:
        sfltsi(cpu, cont);
        break;
    case SFLEU_OP:
        sfleui(cpu, cont);
        break;
    case SFLES_OP:
        sflesi(cpu, cont);
        break;
    case SFGTS_OP:
        sfgtsi(cpu, cont);
        break;
    default:
        unimpl(cpu, cont);
    }
}

static void sf(struct CPU *cpu, struct control *cont) 
    _(requires \thread_local(&cpu->regs->gpr[cont->rA]))
    _(requires \thread_local(&cpu->regs->gpr[cont->rB]))
    _(requires \thread_local(cont))
    _(requires cont->rA < NUM_REGS)
    _(requires cont->rB < NUM_REGS)
    _(writes cpu)
{
    switch(cont->sf_op) {
    case SFNE_OP:
        sfne(cpu, cont);
        break;
    case SFEQ_OP:
        sfeq(cpu, cont);
        break;
    case SFLTU_OP:
        sfltu(cpu, cont);
        break;
    case SFLEU_OP:
        sfleu(cpu, cont);
        break;
    case SFGTU_OP:
        sfgtu(cpu, cont);
        break;
    case SFGTS_OP:
        sfgts(cpu, cont);
        break;
    case SFGEU_OP:
        sfgeu(cpu, cont);
        break;
    case SFGES_OP:
        sfges(cpu, cont);
        break;
    case SFLTS_OP:
        sflts(cpu, cont);
        break;
    case SFLES_OP:
        sfles(cpu, cont);
        break;
    default:
        unimpl(cpu, cont);
    }
}


static void movhi(struct CPU *cpu, struct control *cont) 
    _(requires \wrapped(cpu))
    _(requires \thread_local(cont))
    _(requires cont->rD < NUM_REGS)
    _(writes cpu)
{
    myprintf("movhi r%u,0x%04x\n", cont->rD, cont->K);
    cpu_set_gpr(cpu, cont->rD, cont->K << 16);
}

static void macrc(struct CPU *cpu, struct control *cont) 
    _(requires \wrapped(cpu))
    _(requires \thread_local(cont))
    _(requires cont->rD < NUM_REGS)
    _(writes cpu)
{
    u32 r;
    i64 m;

    m = cpu_get_mac(cpu);
    r = to_u32(m & 0xffffffff);

    cpu_set_gpr(cpu, cont->rD, r);
    cpu_set_mac(cpu, 0);
}

static void macrc_movhi(struct CPU *cpu, struct control *cont) 
    _(requires \wrapped(cpu))
    _(requires \thread_local(cont))
    _(requires cont->rD < NUM_REGS)
    _(writes cpu)
{
    if((cont->inst & 0x1ffff) == 0x10000) {
        macrc(cpu, cont);
    } else {
        movhi(cpu, cont);
    }
}

static void mac_msb(struct CPU *cpu, struct control *cont) 
    _(requires \wrapped(cpu))
    _(requires \thread_local(cont))
    _(requires cont->rA < NUM_REGS)
    _(requires cont->rB < NUM_REGS)
    _(writes cpu)
{
    if((cont->inst & 0xf) == 0x2) {
        msb(cpu, cont);
    } else if((cont->inst & 0xf) == 0x1) {
        mac(cpu, cont);
    }
    else {
      unimpl(cpu, cont);
    }
}

static void or32_mtspr(struct CPU *cpu, struct control *cont) 
    _(requires \thread_local(cpu))
    _(requires \thread_local(&cpu->regs->gpr[cont->rA]))
    _(requires \thread_local(&cpu->regs->gpr[cont->rB]))
    _(requires cont->rA < NUM_REGS)
    _(requires cont->rB < NUM_REGS)
    _(requires \thread_local(cont))
{
    myprintf("mtspr r%u, r%u, 0x%04x\n", cont->rA, cont->rB, cont->K);        
    cpu_set_spr(cpu, cpu_get_gpr(cpu, cont->rA) | cont->K, cpu_get_gpr(cpu, cont->rB));
}

static void or32_mfspr(struct CPU *cpu, struct control *cont) 
    _(requires \thread_local(&cpu->regs->gpr[cont->rA]))
    _(requires \wrapped(cpu))
    _(requires \thread_local(cont))
    _(requires cont->rA < NUM_REGS)
    _(requires cont->rD < NUM_REGS)
    _(writes cpu)
{
    myprintf("mfspr r%u, r%u, 0x%04x\n", cont->rD, cont->rA, cont->K);
    cpu_set_gpr(cpu, cont->rD, cpu_get_spr(cpu, (cpu_get_gpr(cpu, cont->rA) | cont->K)));
}

static void andi(struct CPU *cpu, struct control *cont) 
    _(requires \thread_local(&cpu->regs->gpr[cont->rA]))
    _(requires \wrapped(cpu))
    _(requires \thread_local(cont))
    _(requires cont->rA < NUM_REGS)
    _(requires cont->rD < NUM_REGS)
    _(writes cpu)
{
    u32 res;
    myprintf("andi r%u, r%u, 0x%04x\n", cont->rD, cont->rA, cont->K);
    res = cpu_get_gpr(cpu, cont->rA) & cont->K;
    cpu_set_gpr(cpu, cont->rD, res);
}

static void sys(struct CPU *cpu, struct control *cont)
{
        if(is_in_delay_slot(cpu))
	{
		/* Address of last branch stored in EPCR */
		cpu_set_epcr(cpu, cpu_get_pc(cpu) - 4);
	}
	else
	{
		/* NPC stored in EPCR */
	  cpu_set_epcr(cpu, cpu_get_npc(cpu));
	}

	/* Save the current SR to ESR */
	cpu_set_esr(cpu, cpu_get_sr(cpu));

	/* If exception was in delay slot set SR[DSX] */
	cpu_set_dsx(cpu, is_in_delay_slot(cpu));

	/* Set NPC to address of handler */
	cpu_set_npc(cpu, cpu_get_eph(cpu) ? 0xF0000C00 : 0xC00);

	/* Disable MMUs, go to supervisor mode, and interrupts
	   and timer exceptions disabled */
	cpu_set_dme(cpu, 0);
	cpu_set_ime(cpu, 0);
	cpu_set_sm(cpu, 1);
	cpu_set_iee(cpu, 0);
	cpu_set_tee(cpu, 0);
}


static void trap(struct CPU *cpu, struct control *cont)
{
        if(is_in_delay_slot(cpu))
	{
	    /* Address of last branch stored in EPCR */
	    cpu_set_epcr(cpu, cpu_get_pc(cpu) - 4);
	    /* If exception was in delay slot set SR[DSX] */
	    cpu_set_dsx(cpu, 1);
	}
	else
	{
	    /* PC stored in EPCR */
	    cpu_set_epcr(cpu, cpu_get_pc(cpu));
	    /* If exception was in delay slot set SR[DSX] */
	    cpu_set_dsx(cpu, 0);
	}

	/* Save the current SR to ESR */
	cpu_set_esr(cpu, cpu_get_sr(cpu));

	/* Set NPC to address of handler */
	cpu_set_npc(cpu, cpu_get_eph(cpu) ? 0xF0000E00 : 0xE00);

	/* Disable MMUs, go to supervisor mode, and interrupts
	   and timer exceptions disabled */
	cpu_set_dme(cpu, 0);
	cpu_set_ime(cpu, 0);
	cpu_set_sm(cpu, 1);
	cpu_set_iee(cpu, 0);
	cpu_set_tee(cpu, 0);
}


static void sys_trap_sync(struct CPU *cpu, struct control *cont)
{
    switch((cont->inst & 0xffff0000))
    {
        case 0x20000000:
	  sys(cpu, cont);
	  break;
        case 0x21000000:
	  trap(cpu, cont);
	  break;
        case 0x23000000:
        case 0x22000000:
        case 0x22800000:
        default:
          unimpl(cpu, cont);
    }
}

static void rfe(struct CPU *cpu, struct control *cont)
{
    myprintf("rfe\n", cpu);

    /* Restore the SR of the interrupted flow */
    cpu_set_sr(cpu, cpu_get_esr(cpu));
    
    /* Update the NPC to that of the last non-executed instruction */
    cpu_set_npc(cpu, cpu_get_epcr(cpu));
}

/**********************************************************************************/

/************************* Decode and execute logic *******************************/

static void ro_shift_i(struct CPU *cpu, struct control *cont) {
    switch(cont->ro_shift_i_op) {
    case RS_SLLI_OP:
        slli(cpu, cont);
        break;
    case RS_SRLI_OP:
        srli(cpu, cont);
        break;
    case RS_SRAI_OP:
        srai(cpu, cont);
        break;
    case RS_RORI_OP:
        rori(cpu, cont);
        break;
    default:
        unimpl(cpu, cont);       
    }
}

static void alu(struct CPU *cpu, struct control *cont) 
    _(requires \wrapped(cpu))
    _(requires \thread_local(cont))
    _(requires \wrapped(cont))
    _(ensures  \wrapped(cont))
    _(writes cpu)
{
    switch(cont->alu_op) {        
    case ADD_ALU_OP:
        add(cpu, cont);
        break;
    case ADDC_ALU_OP:
        addc(cpu, cont);
        break;
    case EXTWS_ALU_OP:
        extws(cpu, cont);
        break;
    case EXTWZ_ALU_OP:
        extwz(cpu, cont);
        break;
    case EXTHS_ALU_OP:
        exths(cpu, cont);
        break;
    case EXTBS_ALU_OP:
        extbs(cpu, cont);
        break;
    case EXTBZ_ALU_OP:
        extbz(cpu, cont);
        break;
    case EXTHZ_ALU_OP:
        exthz(cpu, cont);
        break;
    case DIVU_ALU_OP:
        divu(cpu, cont);
        break;
    case DIV_ALU_OP:
        or32_div(cpu, cont);
        break;
    case FF1_ALU_OP:
        ff1(cpu, cont);
        break;
    case FL1_ALU_OP:
        fl1(cpu, cont);
        break;
    case MUL_ALU_OP:
        mul(cpu, cont);
        break;
    case MULU_ALU_OP:
        mulu(cpu, cont);
        break;
    case SUB_ALU_OP:
        sub(cpu, cont);
        break;
    case AND_ALU_OP:
        and(cpu, cont);
        break;
    case XOR_ALU_OP:
        xor(cpu, cont);
        break;
    case SLL_ALU_OP:
        sll(cpu, cont);
        break;
    case SRL_ALU_OP:
        srl(cpu, cont);
        break;
    case SRA_ALU_OP:
        sra(cpu, cont);
        break;
    case ROR_ALU_OP:
        ror(cpu, cont);
        break;
    case OR_ALU_OP:
        or(cpu, cont);
        break;
    case CMOV_ALU_OP:
        cmov(cpu, cont);
        break;
   default:
        unimpl(cpu, cont);
    }
}

static u32 fetch(struct CPU *cpu) {
    u32 inst = 0xdeadbeef;
    bool ret;

    ret = guestLoad(cpu_get_pc(cpu), &inst);
    if(!ret) {
        exit(0);
    }

    return inst;
}

static void execute(u32 op, struct CPU *cpu, struct control *cont) 
    _(requires \wrapped(cpu))
    _(requires \wrapped(cont))
    _(requires op < NUM_OPCODES)
    _(writes cpu)
{
    switch(op) {
    case OP_J:
        j(cpu, cont);
        break;
    case OP_JAL:
        jal(cpu, cont);
        break;
    case OP_JALR:
        jalr(cpu, cont);
        break;
    case OP_BF:
        bf(cpu, cont);
        break;
    case OP_BNF:
        bnf(cpu, cont);
        break;
    case OP_NOP:
        or32_nop(cpu, cont);
        break;
    case OP_JR:
        jr(cpu, cont);
        break;
    case OP_LBZ:
        lbz(cpu, cont);
        break;
    case OP_LHZ:
        lhz(cpu, cont);
        break;
    case OP_LBS:
        lbs(cpu, cont);
        break;
    case OP_LHS:
        lhs(cpu, cont);
        break;
    case OP_LWZ:
        lwz(cpu, cont);
        break;
    case OP_LWS:
        lwz(cpu, cont);
        break;
    case OP_ADDI:
        addi(cpu, cont);
        break;
    case OP_ADDIC:
        addic(cpu, cont);
        break;
    case OP_ORI:
        ori(cpu, cont);
        break;
    case OP_SFI:
        sfi(cpu, cont);
        break;
    case OP_SW:
        sw(cpu, cont);
        break;
    case OP_SB:
        sb(cpu, cont);
        break;
    case OP_SH:
        sh(cpu, cont);
        break;
    case OP_ALU:
        alu(cpu, cont);
        break;
    case OP_MAC:
        mac_msb(cpu, cont);
        break;
    case OP_MACI:
        maci(cpu, cont);
        break;
    case OP_MACRC_MOVHI:
        macrc_movhi(cpu, cont);
        break;
    case OP_MULI:
        muli(cpu, cont);
        break;
    case OP_MTSPR:
        or32_mtspr(cpu, cont);
        break;
    case OP_MFSPR:
        or32_mfspr(cpu, cont);
        break;
    case OP_ANDI:
        andi(cpu, cont);
        break;
    case OP_XORI:
        xori(cpu, cont);
        break;
    case OP_SF:
        sf(cpu, cont);
        break;
    case OP_RO_SHIFT_I:
        ro_shift_i(cpu, cont);
        break;
    case OP_SYS_TRAP_SYNC:
        sys_trap_sync(cpu, cont);
        break;
    case OP_RFE:
        rfe(cpu, cont);
        break;
    default:
        unimpl(cpu, cont);
    }

    cpu_advance_pc(cpu);
}

static void decode(struct control *cont, u32 inst) 
    _(writes \span(cont))
    _(ensures \wrapped(cont))
{
    cont->inst = inst;
    cont->opcode = OPCODE(inst);
    cont->sf_op = SF_OP(inst);    
    cont->alu_op = ALU_OP(inst);
    if(ALU_SHIFT(inst)) {
        cont->alu_op &= ~0x30;
    } else {        
        cont->alu_op &= ~0xf0;
    }
    cont->ro_shift_i_op = RO_SHIFT_I_OP(inst);

    cont->rD = RD(inst);
    cont->rA = RA(inst);
    cont->rB = RB(inst);

    cont->N = N(inst);
    if(cont->opcode == OP_MTSPR) {
        cont->K = SPLIT_K(inst);
    } else {
        cont->K = K(inst);
    }
    if((cont->opcode == OP_SW) || (cont->opcode == OP_SH) || (cont->opcode == OP_SB)) {
        cont->I = SPLIT_I(inst);
    } else if(cont->opcode == OP_MACI) {
        cont->I = I_MAC(inst);
    } else {
        cont->I = I(inst);
    }

    cont->L = L(inst);

    _(wrap cont);
}

/**********************************************************************************/


/***************************** Public functions ***********************************/

static int inSim = 0;

bool cpu_exec_inst(struct CPU *cpu) 
   _(requires \wrapped(cpu))
   _(writes cpu)
{
    u32 inst;
    u32 op;
    struct control cont;

    if(inSim > 5) {
        //asm __volatile__("l.add r4, r0, %0; l.trap 0x0" : : "r"(cpu_get_pc(cpu)));
        assert(0);
    }
    inSim++;

    inst = fetch(cpu);
    op = OPCODE(inst);

    _(assert op < NUM_OPCODES);

    decode(&cont, inst);
    execute(op, cpu, &cont);

    _(unwrap &cont); // gets rid of stack_free warning

    inSim--;

    return true;
}

/**********************************************************************************/
