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

#ifndef OMR_ARM64_MACHINE_INCL
#define OMR_ARM64_MACHINE_INCL

/*
 * The following #define and typedef must appear before any #includes in this file
 */
#ifndef OMR_MACHINE_CONNECTOR
#define OMR_MACHINE_CONNECTOR
namespace OMR { namespace ARM64 { class Machine; } }
namespace OMR { typedef OMR::ARM64::Machine MachineConnector; }
#else
#error OMR::ARM64::Machine expected to be a primary connector, but an OMR connector is already defined
#endif

#include "compiler/codegen/OMRMachine.hpp"

#include "codegen/RealRegister.hpp" // for RealRegister, etc
#include "infra/Annotations.hpp"

namespace TR { class CodeGenerator; }

#define NUM_ARM64_GPR 32
#define NUM_ARM64_FPR 32

namespace OMR
{

namespace ARM64
{

class OMR_EXTENSIBLE Machine : public OMR::Machine
   {

public:

   /**
    * @param[in] cg : the TR::CodeGenerator object
    */
   Machine(TR::CodeGenerator *cg);

   /**
    * @param[in] regNum : register number
    */
   TR::RealRegister *getARM64RealRegister(TR::RealRegister::RegNum regNum)
      {
      return _registerFile[regNum];
      }

   /**
    * @param[in] rk : register kind
    * @param[in] excludeGPR0 : exclude GPR0 or not
    * @param[in] considerUnlatched : consider unlatched state or not
    */
   TR::RealRegister *findBestFreeRegister(TR_RegisterKinds rk,
                                            bool excludeGPR0 = false,
                                            bool considerUnlatched = false);

   TR::RealRegister *freeBestRegister(TR::Instruction  *currentInstruction,
                                        TR_RegisterKinds rk,
                                        TR::RealRegister *forced = NULL,
                                        bool excludeGPR0 = false);

   bool getLinkRegisterKilled()
      {
      return _registerFile[TR::RealRegister::lr]->getHasBeenAssignedInMethod();
      }

   bool setLinkRegisterKilled(bool b)
      {
      return _registerFile[TR::RealRegister::lr]->setHasBeenAssignedInMethod(b);
      }

   TR::CodeGenerator *cg() {return _cg;}

private:

   TR::CodeGenerator *_cg;
   TR::RealRegister  **_registerFile;

   void initialiseRegisterFile();

   };
}
}
#endif
