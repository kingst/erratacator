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

#include "spr_defs.h"
#ifndef __CPU_H__
#define __CPU_H__

#ifdef __KERNEL__

#define PRINT_INST 1
#define myprintf(format, ...) do{ if(PRINT_INST) {printk(KERN_CRIT "%04x ", cpu_get_pc(cpu)); printk(KERN_CRIT format, __VA_ARGS__);} } while(0)
#define myprint(format, ...) do{ printk(KERN_CRIT format, __VA_ARGS__); } while(0)

#define _(c, ...)
#include <asm/types.h>
#include <asm/bug.h>
#include <linux/kernel.h>
#include <linux/mm.h>
#include <linux/slab.h>

//typedef __u32 u32;
typedef __s32 i32;
typedef __s64 i64;

#define assert(x) do { if(!(x)) asm __volatile__("l.trap 0x42"); } while(0)
#define exit(x) assert(0)

#define mymalloc(x) kmalloc(x, GFP_KERNEL)
#define myfree(x) kfree(x)

#else

#include <stdlib.h>
#include <assert.h>
#include <stdio.h>
#include <limits.h>
#include <string.h>

#define mymalloc(x) malloc(x)
#define myfree(x) free(x)

#ifdef _WIN32

#define myprintf(format, ...)
#define myprint(format, ...)
#include <vcc.h>
typedef unsigned __int32 u32;
typedef unsigned __int64 u64;
typedef __int32 i32;
typedef __int64 i64;

//extern memset(void *s, int c, size_t n);

#else

#define PRINT_INST 0
#define myprintf(format, ...) do{ if(PRINT_INST) {printf("%04x ", cpu_get_pc(cpu)); printf(format, __VA_ARGS__);} } while(0)
#define myprint(format, ...) do{ printf(format, __VA_ARGS__); } while(0)
#define _(c, ...)
typedef __uint32_t u32;
typedef __uint64_t u64;
typedef __int32_t i32;
typedef __int64_t i64;
typedef __uint8_t u8;
typedef __uint16_t u16;
typedef char bool;

#endif



#endif

#define false 0
#define true 1

#ifdef _WIN32

#else

#define to_u32(x) ((u32) (x))
#define to_i32(x) ((i32) (x))
#define to_u64(x) ((u64) (x))
#define to_i64(x) ((i64) (x))

/*********************** logic functions **************************/
_(logic u32 to_u32(i64 value) = _(unchecked)((u32) value))
_(logic i64 to_i64(u32 value) = _(unchecked)((i64) value))
/******************************************************************/

#endif


#define NUM_REGS 32
// Stack pointer
#define PT_SP 1
// Frame pointer
#define PT_FP 2
// Return value
#define PT_RV 11
// Link register
#define PT_LR 9

//TODO: invariants for the pt_regs structure

struct pt_regs {
    u32 gpr[32];
    u32 pc;
    u32 npc;
    u32 sr;
    u32 orig_gpr11;
    u32 syscallno;
    u32 machi;
    u32 maclo;
};

//struct CPU;
/*_(dynamic_owns)*/ 
struct CPU {
    struct pt_regs *regs; 
    u32 branch_pc;
    u32 esr;
    u32 epcr;
    u32 eear;
    u32 ttmr;
    u32 ttcr;
    _(invariant \mine(regs)) // CPU owns regs
    _(invariant \malloc_root(\this))
};

void cpu_init0(struct pt_regs *regs, struct CPU *cpu);
void cpu_reset(struct CPU *cpu);
void cpu_free(struct CPU *cpu);
void cpu_advance_pc(struct CPU *cpu);
/* Require special handling since the simulator only implements a small
 * subset of the special purpose registers found in real hardware
*/
void cpu_set_spr(struct CPU *cpu, u32 spr, u32 value);
u32 cpu_get_spr(struct CPU *cpu, u32 spr);

#define cpu_get_gpr(cpu, reg) (cpu)->regs->gpr[(reg)]
void cpu_set_gpr(struct CPU *cpu, u32 reg, u32 value);
#define cpu_get_pc(cpu) (cpu)->regs->pc
#define cpu_set_pc(cpu, pc2) (cpu)->regs->pc = pc2
#define cpu_get_npc(cpu) (cpu)->regs->npc
#define cpu_set_npc(cpu, npc2) (cpu)->regs->npc = (npc2)
#define cpu_get_branch_pc(cpu) (cpu)->branch_pc
#define cpu_set_branch_pc(cpu, branch_pc2) (cpu)->branch_pc = (branch_pc2)
#define is_in_delay_slot(cpu) (cpu_get_npc(cpu) != (cpu_get_pc((cpu)) + 4))
#define cpu_has_shadow_state(cpu) is_in_delay_slot((cpu))

#define cpu_get_maclo(cpu) (cpu)->regs->maclo
#define cpu_set_maclo(cpu, maclo2) (cpu)->regs->maclo = (maclo2)
#define cpu_get_machi(cpu) (cpu)->regs->machi
#define cpu_set_machi(cpu, machi2) (cpu)->regs->machi = (machi2)
#define cpu_get_mac(cpu) (cpu_get_maclo(cpu) | ((to_i64(cpu_get_machi(cpu))) << 32)) 
#define cpu_set_mac(cpu, m) cpu_set_machi((cpu), to_u32((u64)(m) >> 32)); cpu_set_maclo((cpu), to_u32((u64)(m) & 0xffffffff))

#define cpu_get_sp(cpu) (cpu)->regs->gpr[PT_SP]
#define cpu_set_sp(cpu, sp2) (cpu)->regs->gpr[PT_SP] = sp2

#define cpu_get_lr(cpu) (cpu)->regs->gpr[PT_LR]
#define cpu_set_lr(cpu, lr2) (cpu)->regs->gpr[PT_LR] = lr2

#define cpu_get_sr(cpu) (cpu)->regs->sr
#define cpu_set_sr(cpu, sr2) (cpu)->regs->sr = (sr2)
#define cpu_is_set_sr_flag(cpu, flag) ((cpu_get_sr(cpu) & (flag)) != 0)
/* Assumes set is in {0, 1} */
/* Clears flag and then uses set value to determine if flag is set */
/* Avoids creating an extra path for the verifier to prove */
#define cpu_set_sr_flag(cpu, flag, set) (cpu)->regs->sr = (cpu)->regs->sr & ~(flag) | ((flag) & (0 - (set)))
#define cpu_get_sm(cpu)    cpu_is_set_sr_flag((cpu), SPR_SR_SM)
#define cpu_get_tee(cpu)   cpu_is_set_sr_flag((cpu), SPR_SR_TEE)
#define cpu_get_iee(cpu)   cpu_is_set_sr_flag((cpu), SPR_SR_IEE)
#define cpu_get_dce(cpu)   cpu_is_set_sr_flag((cpu), SPR_SR_DCE)
#define cpu_get_ice(cpu)   cpu_is_set_sr_flag((cpu), SPR_SR_ICE)
#define cpu_get_dme(cpu)   cpu_is_set_sr_flag((cpu), SPR_SR_DME)
#define cpu_get_ime(cpu)   cpu_is_set_sr_flag((cpu), SPR_SR_IME)
#define cpu_get_lee(cpu)   cpu_is_set_sr_flag((cpu), SPR_SR_LEE)
#define cpu_get_ce(cpu)    cpu_is_set_sr_flag((cpu), SPR_SR_CE)
#define cpu_get_f(cpu)     cpu_is_set_sr_flag((cpu), SPR_SR_F)
#define cpu_is_set_f(cpu)  cpu_is_set_sr_flag((cpu), SPR_SR_F)
#define cpu_get_cy(cpu)    cpu_is_set_sr_flag((cpu), SPR_SR_CY)
#define cpu_get_ov(cpu)    cpu_is_set_sr_flag((cpu), SPR_SR_OV)
#define cpu_get_ove(cpu)   cpu_is_set_sr_flag((cpu), SPR_SR_OVE)
#define cpu_get_dsx(cpu)   cpu_is_set_sr_flag((cpu), SPR_SR_DSX)
#define cpu_get_eph(cpu)   cpu_is_set_sr_flag((cpu), SPR_SR_EPH)
#define cpu_get_fo(cpu)    cpu_is_set_sr_flag((cpu), SPR_SR_FO)
#define cpu_get_sumra(cpu) cpu_is_set_sr_flag((cpu), SPR_SR_SUMRA)
#define cpu_set_sm(cpu, set)    cpu_set_sr_flag((cpu), SPR_SR_SM, (set))
#define cpu_set_tee(cpu, set)   cpu_set_sr_flag((cpu), SPR_SR_TEE, (set))
#define cpu_set_iee(cpu, set)   cpu_set_sr_flag((cpu), SPR_SR_IEE, (set))
#define cpu_set_dce(cpu, set)   cpu_set_sr_flag((cpu), SPR_SR_DCE, (set))
#define cpu_set_ice(cpu, set)   cpu_set_sr_flag((cpu), SPR_SR_ICE, (set))
#define cpu_set_dme(cpu, set)   cpu_set_sr_flag((cpu), SPR_SR_DME, (set))
#define cpu_set_ime(cpu, set)   cpu_set_sr_flag((cpu), SPR_SR_IME, (set))
#define cpu_set_lee(cpu, set)   cpu_set_sr_flag((cpu), SPR_SR_LEE, (set))
#define cpu_set_ce(cpu, set)    cpu_set_sr_flag((cpu), SPR_SR_CE, (set))
#define cpu_set_f(cpu, set)     cpu_set_sr_flag((cpu), SPR_SR_F, (set))
#define cpu_set_cy(cpu, set)    cpu_set_sr_flag((cpu), SPR_SR_CY, (set))
#define cpu_set_ov(cpu, set)    cpu_set_sr_flag((cpu), SPR_SR_OV, (set))
#define cpu_set_ove(cpu, set)   cpu_set_sr_flag((cpu), SPR_SR_OVE, (set))
#define cpu_set_dsx(cpu, set)   cpu_set_sr_flag((cpu), SPR_SR_DSX, (set))
#define cpu_set_eph(cpu, set)   cpu_set_sr_flag((cpu), SPR_SR_EPH, (set))
#define cpu_set_fo(cpu, set)    cpu_set_sr_flag((cpu), SPR_SR_FO, (set))
#define cpu_set_sumra(cpu, set) cpu_set_sr_flag((cpu), SPR_SR_SUMRA, (set))

#define cpu_set_esr(cpu, esr2) (cpu)->esr = (esr2)
#define cpu_get_esr(cpu) (cpu)->esr
#define cpu_set_epcr(cpu, epcr2) cpu->epcr = (epcr2)
#define cpu_get_epcr(cpu) (cpu)->epcr
#define cpu_set_eear(cpu, eear2) (cpu)->eear = (eear2)
#define cpu_get_eear(cpu) (cpu)->eear

#define cpu_set_ttmr(cpu, ttmr2) (cpu)->ttmr = (ttmr2)
#define cpu_get_ttmr(cpu) (cpu)->ttmr
#define cpu_set_ttcr(cpu, ttcr2) (cpu)->ttcr = (ttcr2)
#define cpu_get_ttcr(cpu) (cpu)->ttcr

#endif



_(assert PT_SP < NUM_REGS)
_(assert PT_LR < NUM_REGS)
_(assert PT_SR < NUM_REGS)
