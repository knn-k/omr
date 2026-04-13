/*******************************************************************************
 * Copyright IBM Corp. and others 2000
 *
 * This program and the accompanying materials are made available under
 * the terms of the Eclipse Public License 2.0 which accompanies this
 * distribution and is available at https://www.eclipse.org/legal/epl-2.0/
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
 * [2] https://openjdk.org/legal/assembly-exception.html
 *
 * SPDX-License-Identifier: EPL-2.0 OR Apache-2.0 OR GPL-2.0-only WITH Classpath-exception-2.0 OR GPL-2.0-only WITH OpenJDK-assembly-exception-1.0
 *******************************************************************************/

#include "codegen/IA32LinkageUtils.hpp"

#include <stddef.h>
#include <stdint.h>
#include "codegen/CodeGenerator.hpp"
#include "codegen/Machine.hpp"
#include "codegen/MemoryReference.hpp"
#include "codegen/RealRegister.hpp"
#include "codegen/Register.hpp"
#include "codegen/RegisterConstants.hpp"
#include "compile/Compilation.hpp"
#include "compile/SymbolReferenceTable.hpp"
#include "env/jittypes.h"
#include "il/ILOpCodes.hpp"
#include "il/ILOps.hpp"
#include "il/Node.hpp"
#include "il/Node_inlines.hpp"
#include "il/StaticSymbol.hpp"
#include "il/Symbol.hpp"
#include "il/SymbolReference.hpp"
#include "infra/Assert.hpp"
#include "x/codegen/X86Instruction.hpp"
#include "codegen/InstOpCode.hpp"

namespace TR {

TR::Register *IA32LinkageUtils::pushIntegerWordArg(TR::Node *child, TR::CodeGenerator *cg)
{
    TR::Register *pushRegister;
    if (child->getRegister() == NULL) {
        if (child->getOpCode().isLoadConst()) {
            int32_t value = child->getInt();
            OP::Mnemonic pushOp;
            if (value >= -128 && value <= 127) {
                pushOp = OP::PUSHImms;
            } else {
                pushOp = OP::PUSHImm4;
            }

            Inst_Imm(pushOp, child, value, cg);
            cg->decReferenceCount(child);
            return NULL;
        } else if (child->getOpCodeValue() == TR::loadaddr) {
            TR::SymbolReference *symRef = child->getSymbolReference();
            TR::StaticSymbol *sym = symRef->getSymbol()->getStaticSymbol();
            if (sym) {
                TR_ASSERT(!symRef->isUnresolved(), "pushIntegerWordArg loadaddr expecting resolved symbol");
                Inst_ImmSym(OP::PUSHImm4, child,
                    static_cast<int32_t>(reinterpret_cast<intptr_t>(sym->getStaticAddress())), symRef, cg);
                cg->decReferenceCount(child);
                return NULL;
            }
        } else if (child->getOpCodeValue() == TR::fbits2i && !child->normalizeNanValues()
            && child->getReferenceCount() == 1) {
            pushRegister = pushFloatArg(child->getFirstChild(), cg);
            cg->decReferenceCount(child);
            return pushRegister;
        } else if (child->getOpCode().isMemoryReference() && (child->getReferenceCount() == 1)
            && (child->getSymbolReference() != cg->comp()->getSymRefTab()->findVftSymbolRef())) {
            TR::MemoryReference *tempMR = MRef_node(child, cg);
            Inst_Mem(OP::PUSHMem, child, tempMR, cg);
            tempMR->decNodeReferenceCounts(cg);
            cg->decReferenceCount(child);
            return NULL;
        }
    }

    pushRegister = cg->evaluate(child);
    Inst_Reg(OP::PUSHReg, child, pushRegister, cg);
    cg->decReferenceCount(child);
    return pushRegister;
}

TR::Register *IA32LinkageUtils::pushLongArg(TR::Node *child, TR::CodeGenerator *cg)
{
    TR::Register *pushRegister;
    if (child->getRegister() == NULL) {
        if (child->getOpCode().isLoadConst()) {
            OP::Mnemonic pushOp;

            int32_t highValue = child->getLongIntHigh();
            if (highValue >= -128 && highValue <= 127) {
                pushOp = OP::PUSHImms;
            } else {
                pushOp = OP::PUSHImm4;
            }
            Inst_Imm(pushOp, child, highValue, cg);

            int32_t lowValue = child->getLongIntLow();
            if (lowValue >= -128 && lowValue <= 127) {
                pushOp = OP::PUSHImms;
            } else {
                pushOp = OP::PUSHImm4;
            }
            Inst_Imm(pushOp, child, lowValue, cg);
            cg->decReferenceCount(child);
            return NULL;
        } else if (child->getOpCodeValue() == TR::dbits2l && !child->normalizeNanValues()
            && child->getReferenceCount() == 1) {
            pushRegister = pushDoubleArg(child->getFirstChild(), cg);
            cg->decReferenceCount(child);
            return pushRegister;
        } else if (child->getOpCode().isMemoryReference() && child->getReferenceCount() == 1) {
            TR::MemoryReference *lowMR = MRef_node(child, cg);
            Inst_Mem(OP::PUSHMem, child, MRef_MRefOff(*lowMR, 4, cg), cg);
            Inst_Mem(OP::PUSHMem, child, lowMR, cg);
            lowMR->decNodeReferenceCounts(cg);
            return NULL;
        }
    }

    pushRegister = cg->evaluate(child);
    Inst_Reg(OP::PUSHReg, child, pushRegister->getHighOrder(), cg);
    Inst_Reg(OP::PUSHReg, child, pushRegister->getLowOrder(), cg);
    cg->decReferenceCount(child);
    return pushRegister;
}

TR::Register *IA32LinkageUtils::pushFloatArg(TR::Node *child, TR::CodeGenerator *cg)
{
    TR::Register *pushRegister;
    if (child->getRegister() == NULL) {
        if (child->getOpCodeValue() == TR::fconst) {
            int32_t value = child->getFloatBits();
            OP::Mnemonic pushOp;
            if (value >= -128 && value <= 127) {
                pushOp = OP::PUSHImms;
            } else {
                pushOp = OP::PUSHImm4;
            }
            Inst_Imm(pushOp, child, value, cg);
            cg->decReferenceCount(child);
            return NULL;
        } else if (child->getReferenceCount() == 1) {
            if (child->getOpCode().isLoad()) {
                TR::MemoryReference *tempMR = MRef_node(child, cg);
                Inst_Mem(OP::PUSHMem, child, tempMR, cg);
                tempMR->decNodeReferenceCounts(cg);
                cg->decReferenceCount(child);
                return NULL;
            } else if (child->getOpCodeValue() == TR::ibits2f) {
                pushRegister = pushIntegerWordArg(child->getFirstChild(), cg);
                cg->decReferenceCount(child);
                return pushRegister;
            }
        }
    }

    pushRegister = cg->evaluate(child);
    TR::RealRegister *espReal = cg->machine()->getRealRegister(TR::RealRegister::esp);
    Inst_RegImm(OP::SUB4RegImms, child, espReal, 4, cg);

    Inst_MemReg(OP::MOVSSMemReg, child, MRef_Bdisp32(espReal, 0, cg), pushRegister, cg);

    cg->decReferenceCount(child);
    return pushRegister;
}

TR::Register *IA32LinkageUtils::pushDoubleArg(TR::Node *child, TR::CodeGenerator *cg)
{
    TR::Register *pushRegister;
    if (child->getRegister() == NULL) {
        if (child->getOpCodeValue() == TR::dconst) {
            OP::Mnemonic pushOp;

            int32_t highValue = child->getLongIntHigh();
            if (highValue >= -128 && highValue <= 127) {
                pushOp = OP::PUSHImms;
            } else {
                pushOp = OP::PUSHImm4;
            }
            Inst_Imm(pushOp, child, highValue, cg);

            int32_t lowValue = child->getLongIntLow();
            if (lowValue >= -128 && lowValue <= 127) {
                pushOp = OP::PUSHImms;
            } else {
                pushOp = OP::PUSHImm4;
            }
            Inst_Imm(pushOp, child, lowValue, cg);
            cg->decReferenceCount(child);
            return NULL;
        } else if (child->getReferenceCount() == 1) {
            if (child->getOpCode().isLoad()) {
                TR::MemoryReference *lowMR = MRef_node(child, cg);
                Inst_Mem(OP::PUSHMem, child, MRef_MRefOff(*lowMR, 4, cg), cg);
                Inst_Mem(OP::PUSHMem, child, lowMR, cg);
                lowMR->decNodeReferenceCounts(cg);
                cg->decReferenceCount(child);
                return NULL;
            } else if (child->getOpCodeValue() == TR::lbits2d) {
                pushRegister = pushLongArg(child->getFirstChild(), cg);
                cg->decReferenceCount(child);
                return pushRegister;
            }
        }
    }

    pushRegister = cg->evaluate(child);
    TR::RealRegister *espReal = cg->machine()->getRealRegister(TR::RealRegister::esp);
    Inst_RegImm(OP::SUB4RegImms, child, espReal, 8, cg);

    Inst_MemReg(OP::MOVSDMemReg, child, MRef_Bdisp32(espReal, 0, cg), pushRegister, cg);

    cg->decReferenceCount(child);
    return pushRegister;
}

} // namespace TR
