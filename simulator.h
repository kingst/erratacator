#ifndef __SIMULATOR_H__
#define __SIMULATOR_H__

#include "cpu.h"


// these functions need to be implemented to be able to link to 
// the simulator code
bool guestLoad(u32 guestAddr, u32 *value);
bool guestStore(u32 guestAddr, u32 value);


// these are the function that the simulator implements and exports
bool cpu_exec_inst(struct CPU *cpu);

#endif
