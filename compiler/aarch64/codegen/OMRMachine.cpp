/*******************************************************************************
 * Copyright (c) 2018, 2018 IBM Corp. and others
 *
 * This program and the accompanying materials are made available under
 * the terms of the Eclipse Public License 2.0 which accompanies this
 * distribution and is available at http://eclipse.org/legal/epl-2.0
 * or the Apache License, Version 2.0 which accompanies this distribution
 * and is available at https://www.apache.org/licenses/LICENSE-2.0.
 *
 * This Source Code may also be made available under the following Secondary
 * Licenses when the conditions for such availability set forth in the
 * Eclipse Public License, v. 2.0 are satisfied: GNU General Public License,
 * version 2 with the GNU Classpath Exception [1] and GNU General Public
 * License, version 2 with the OpenJDK Assembly Exception [2].
 *
 * [1] https://www.gnu.org/software/classpath/license.html
 * [2] http://openjdk.java.net/legal/assembly-exception.html
 *
 * SPDX-License-Identifier: EPL-2.0 OR Apache-2.0 OR GPL-2.0 WITH Classpath-exception-2.0 OR LicenseRef-GPL-2.0 WITH Assembly-exception
 *******************************************************************************/

#include "aarch64/codegen/OMRMachine.hpp"

#include <stdint.h> // for uint16_t, int32_t, etc

#include "codegen/CodeGenerator.hpp"
#include "codegen/Machine.hpp"
#include "codegen/Machine_inlines.hpp"
#include "codegen/RealRegister.hpp" // for RealRegister, etc
#include "infra/Assert.hpp" // for TR_ASSERT

OMR::ARM64::Machine::Machine(TR::CodeGenerator *cg) :
      OMR::Machine(NUM_ARM64_GPR, NUM_ARM64_FPR)
   {
   _registerFile = (TR::RealRegister **)cg->trMemory()->allocateMemory(sizeof(TR::RealRegister *)*TR::RealRegister::NumRegisters, heapAlloc);
   self()->initialiseRegisterFile();
   }

TR::RealRegister *OMR::ARM64::Machine::findBestFreeRegister(TR_RegisterKinds rk,
                                                            bool excludeGPR0,
                                                            bool considerUnlatched)
   {
   int first;
   int last;

   switch(rk)
      {
      case TR_GPR:
         first = TR::RealRegister::FirstGPR;
         if (excludeGPR0)
            first++;
         last  = TR::RealRegister::LastAssignableGPR;
         break;
      case TR_FPR:
         first = TR::RealRegister::FirstFPR;
         last  = TR::RealRegister::LastFPR;
         break;
   }

   uint32_t bestWeightSoFar = 0xffffffff;
   TR::RealRegister *freeRegister = NULL;
   for (int i = first; i <= last; i++)
      {
      if ((_registerFile[i]->getState() == TR::RealRegister::Free ||
           (considerUnlatched &&
            _registerFile[i]->getState() == TR::RealRegister::Unlatched)) &&
          _registerFile[i]->getWeight() < bestWeightSoFar)
         {
         freeRegister    = _registerFile[i];
         bestWeightSoFar = freeRegister->getWeight();
         }
      }
   if (freeRegister != NULL && freeRegister->getState() == TR::RealRegister::Unlatched)
      {
      freeRegister->setAssignedRegister(NULL);
      freeRegister->setState(TR::RealRegister::Free);
      }
   return freeRegister;
   }

TR::RealRegister *OMR::ARM64::Machine::freeBestRegister(TR::Instruction *currentInstruction,
                                                        TR_RegisterKinds rk,
                                                        TR::RealRegister *forced,
                                                        bool excludeGPR0)
   {
   TR_ASSERT(false, "Not implemented yet.");

   return NULL;
   }

void OMR::ARM64::Machine::initialiseRegisterFile()
   {
   _registerFile[TR::RealRegister::NoReg] = NULL;
   _registerFile[TR::RealRegister::SpilledReg] = NULL;

   _registerFile[TR::RealRegister::x0] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_GPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::x0,
                                                 _cg);

   _registerFile[TR::RealRegister::x1] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_GPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::x1,
                                                 _cg);

   _registerFile[TR::RealRegister::x2] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_GPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::x2,
                                                 _cg);

   _registerFile[TR::RealRegister::x3] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_GPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::x3,
                                                 _cg);

   _registerFile[TR::RealRegister::x4] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_GPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::x4,
                                                 _cg);

   _registerFile[TR::RealRegister::x5] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_GPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::x5,
                                                 _cg);

   _registerFile[TR::RealRegister::x6] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_GPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::x6,
                                                 _cg);

   _registerFile[TR::RealRegister::x7] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_GPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::x7,
                                                 _cg);

   _registerFile[TR::RealRegister::x8] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_GPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::x8,
                                                 _cg);

   _registerFile[TR::RealRegister::x9] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_GPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::x9,
                                                 _cg);

   _registerFile[TR::RealRegister::x10] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_GPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::x10,
                                                 _cg);

   _registerFile[TR::RealRegister::x11] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_GPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::x11,
                                                 _cg);

   _registerFile[TR::RealRegister::x12] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_GPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::x12,
                                                 _cg);

   _registerFile[TR::RealRegister::x13] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_GPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::x13,
                                                 _cg);

   _registerFile[TR::RealRegister::x14] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_GPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::x14,
                                                 _cg);

   _registerFile[TR::RealRegister::x15] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_GPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::x15,
                                                 _cg);

   _registerFile[TR::RealRegister::x16] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_GPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::x16,
                                                 _cg);

   _registerFile[TR::RealRegister::x17] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_GPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::x17,
                                                 _cg);

   _registerFile[TR::RealRegister::x18] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_GPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::x18,
                                                 _cg);

   _registerFile[TR::RealRegister::x19] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_GPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::x19,
                                                 _cg);

   _registerFile[TR::RealRegister::x20] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_GPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::x20,
                                                 _cg);

   _registerFile[TR::RealRegister::x21] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_GPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::x21,
                                                 _cg);

   _registerFile[TR::RealRegister::x22] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_GPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::x22,
                                                 _cg);

   _registerFile[TR::RealRegister::x23] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_GPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::x23,
                                                 _cg);

   _registerFile[TR::RealRegister::x24] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_GPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::x24,
                                                 _cg);

   _registerFile[TR::RealRegister::x25] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_GPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::x25,
                                                 _cg);

   _registerFile[TR::RealRegister::x26] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_GPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::x26,
                                                 _cg);

   _registerFile[TR::RealRegister::x27] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_GPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::x27,
                                                 _cg);

   _registerFile[TR::RealRegister::x28] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_GPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::x28,
                                                 _cg);

   _registerFile[TR::RealRegister::x29] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_GPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::x29,
                                                 _cg);

   /* x30 is used as LR on ARM64 */
   _registerFile[TR::RealRegister::lr] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_GPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::lr,
                                                 _cg);

   /* x31 is unavailable as GPR on ARM64 */

   _registerFile[TR::RealRegister::v0] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_FPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::v0,
                                                 _cg);

   _registerFile[TR::RealRegister::v1] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_FPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::v1,
                                                 _cg);

   _registerFile[TR::RealRegister::v2] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_FPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::v2,
                                                 _cg);

   _registerFile[TR::RealRegister::v3] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_FPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::v3,
                                                 _cg);

   _registerFile[TR::RealRegister::v4] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_FPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::v4,
                                                 _cg);

   _registerFile[TR::RealRegister::v5] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_FPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::v5,
                                                 _cg);

   _registerFile[TR::RealRegister::v6] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_FPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::v6,
                                                 _cg);

   _registerFile[TR::RealRegister::v7] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_FPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::v7,
                                                 _cg);

   _registerFile[TR::RealRegister::v8] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_FPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::v8,
                                                 _cg);

   _registerFile[TR::RealRegister::v9] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_FPR,
                                                  0,
                                                  TR::RealRegister::Free,
                                                  TR::RealRegister::v9,
                                                  _cg);
 
   _registerFile[TR::RealRegister::v10] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_FPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::v10,
                                                 _cg);

   _registerFile[TR::RealRegister::v11] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_FPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::v11,
                                                 _cg);

   _registerFile[TR::RealRegister::v12] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_FPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::v12,
                                                 _cg);

   _registerFile[TR::RealRegister::v13] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_FPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::v13,
                                                 _cg);

   _registerFile[TR::RealRegister::v14] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_FPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::v14,
                                                 _cg);

   _registerFile[TR::RealRegister::v15] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_FPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::v15,
                                                 _cg);

   _registerFile[TR::RealRegister::v16] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_FPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::v16,
                                                 _cg);

   _registerFile[TR::RealRegister::v17] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_FPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::v17,
                                                 _cg);

   _registerFile[TR::RealRegister::v18] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_FPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::v18,
                                                 _cg);

   _registerFile[TR::RealRegister::v19] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_FPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::v19,
                                                 _cg);

   _registerFile[TR::RealRegister::v20] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_FPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::v20,
                                                 _cg);

   _registerFile[TR::RealRegister::v21] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_FPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::v21,
                                                 _cg);

   _registerFile[TR::RealRegister::v22] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_FPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::v22,
                                                 _cg);

   _registerFile[TR::RealRegister::v23] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_FPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::v23,
                                                 _cg);

   _registerFile[TR::RealRegister::v24] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_FPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::v24,
                                                 _cg);

   _registerFile[TR::RealRegister::v25] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_FPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::v25,
                                                 _cg);

   _registerFile[TR::RealRegister::v26] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_FPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::v26,
                                                 _cg);

   _registerFile[TR::RealRegister::v27] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_FPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::v27,
                                                 _cg);

   _registerFile[TR::RealRegister::v28] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_FPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::v28,
                                                 _cg);

   _registerFile[TR::RealRegister::v29] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_FPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::v29,
                                                 _cg);
   _registerFile[TR::RealRegister::v30] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_FPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::v30,
                                                 _cg);

   _registerFile[TR::RealRegister::v31] = new (self()->cg()->trHeapMemory()) TR::RealRegister(TR_FPR,
                                                 0,
                                                 TR::RealRegister::Free,
                                                 TR::RealRegister::v31,
                                                 _cg);
   }
