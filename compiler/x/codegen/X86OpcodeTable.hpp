/*******************************************************************************
 * Copyright IBM Corp. and others 2023
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

#ifndef OMR_X86OPCODETABLE_HPP
#define OMR_X86OPCODETABLE_HPP

#include <cstdint>
#include "codegen/InstOpCode.hpp"

enum ArithmeticOps : uint32_t {
    ArithmeticInvalid,
    BinaryArithmeticAdd,
    BinaryArithmeticSub,
    BinaryArithmeticMul,
    BinaryArithmeticDiv,
    BinaryArithmeticAnd,
    BinaryArithmeticOr,
    BinaryArithmeticXor,
    BinaryArithmeticMin,
    BinaryArithmeticMax,
    BinaryLogicalShiftLeft,
    BinaryLogicalShiftRight,
    BinaryArithmeticShiftRight,
    BinaryRotateLeft,
    BinaryRotateRight,
    NumBinaryArithmeticOps,
    UnaryArithmeticAbs,
    UnaryArithmeticSqrt,
    LastOp,
    NumUnaryArithmeticOps = LastOp - NumBinaryArithmeticOps + 1
};

// clang-format off

// TODO: Truncate the table
static const OP::Mnemonic BinaryArithmeticOpCodesForReg[NumBinaryArithmeticOps][TR::NumOMRTypes] = {
    //                NoType                         Int8,                          Int16, Int32, Int64, Float, Double,
    //                Address,                        Aggregate
    { OP::bad, OP::bad, OP::bad, OP::bad, OP::bad,
     OP::bad,         OP::bad, OP::bad,OP::bad                                                                           }, // BinaryArithmeticInvalid
    { OP::bad, OP::bad, OP::bad, OP::bad, OP::bad,
     OP::ADDSSRegReg, OP::ADDSDRegReg, OP::bad,
     OP::bad                                                                       }, // BinaryArithmeticAdd
    { OP::bad, OP::bad, OP::bad, OP::bad, OP::bad,
     OP::SUBSSRegReg, OP::SUBSDRegReg, OP::bad,
     OP::bad                                                                       }, // BinaryArithmeticSub
    { OP::bad, OP::bad, OP::bad, OP::bad, OP::bad,
     OP::MULSSRegReg, OP::MULSDRegReg, OP::bad,
     OP::bad                                                                       }, // BinaryArithmeticMul
    { OP::bad, OP::bad, OP::bad, OP::bad, OP::bad,
     OP::DIVSSRegReg, OP::DIVSDRegReg, OP::bad,
     OP::bad                                                                       }, // BinaryArithmeticDiv
    { OP::bad, OP::bad, OP::bad, OP::bad, OP::bad,
     OP::bad,         OP::bad, OP::bad, OP::bad }, // BinaryArithmeticAnd
    { OP::bad, OP::bad, OP::bad, OP::bad, OP::bad,
     OP::bad,         OP::bad, OP::bad, OP::bad }, // BinaryArithmeticOr,
    { OP::bad, OP::bad, OP::bad, OP::bad, OP::bad,
     OP::bad,         OP::bad, OP::bad, OP::bad }, // BinaryArithmeticXor
    { OP::bad, OP::bad, OP::bad, OP::bad, OP::bad,
     OP::bad,         OP::bad, OP::bad, OP::bad }, // BinaryArithmeticMin
    { OP::bad, OP::bad, OP::bad, OP::bad, OP::bad,
     OP::bad,         OP::bad, OP::bad, OP::bad }, // BinaryArithmeticMax
};

// TODO: Truncate the table
static const OP::Mnemonic BinaryArithmeticOpCodesForMem[NumBinaryArithmeticOps][TR::NumOMRTypes] = {
    //                NoType                         Int8,                          Int16, Int32, Int64, Float, Double,
    //                Address,                        Aggregate
    { OP::bad, OP::bad, OP::bad, OP::bad, OP::bad,
     OP::bad,         OP::bad, OP::bad,OP::bad                                                                           }, // BinaryArithmeticInvalid
    { OP::bad, OP::bad, OP::bad, OP::bad, OP::bad,
     OP::ADDSSRegMem, OP::ADDSDRegMem, OP::bad,
     OP::bad                                                                       }, // BinaryArithmeticAdd
    { OP::bad, OP::bad, OP::bad, OP::bad, OP::bad,
     OP::SUBSSRegMem, OP::SUBSDRegMem, OP::bad,
     OP::bad                                                                       }, // BinaryArithmeticSub
    { OP::bad, OP::bad, OP::bad, OP::bad, OP::bad,
     OP::MULSSRegMem, OP::MULSDRegMem, OP::bad,
     OP::bad                                                                       }, // BinaryArithmeticMul
    { OP::bad, OP::bad, OP::bad, OP::bad, OP::bad,
     OP::DIVSSRegMem, OP::DIVSDRegMem, OP::bad,
     OP::bad                                                                       }, // BinaryArithmeticDiv
    { OP::bad, OP::bad, OP::bad, OP::bad, OP::bad,
     OP::bad,         OP::bad, OP::bad, OP::bad }, // BinaryArithmeticAnd
    { OP::bad, OP::bad, OP::bad, OP::bad, OP::bad,
     OP::bad,         OP::bad, OP::bad, OP::bad }, // BinaryArithmeticOr,
    { OP::bad, OP::bad, OP::bad, OP::bad, OP::bad,
     OP::bad,         OP::bad, OP::bad, OP::bad }, // BinaryArithmeticXor
    { OP::bad, OP::bad, OP::bad, OP::bad, OP::bad,
     OP::bad,         OP::bad, OP::bad, OP::bad }, // BinaryArithmeticMin
    { OP::bad, OP::bad, OP::bad, OP::bad, OP::bad,
     OP::bad,         OP::bad, OP::bad, OP::bad }, // BinaryArithmeticMax
};

static const OP::Mnemonic VectorBinaryArithmeticOpCodesForReg[NumBinaryArithmeticOps]
                                                                         [TR::NumVectorElementTypes]
    = {
          //          Int8,                          Int16,                         Int32,
          //          Int64,                         Float,                         Double
          {OP::bad,              OP::bad,              OP::bad,
           OP::bad,              OP::bad,              OP::bad}, // BinaryArithmeticInvalid

          {OP::PADDBRegReg,      OP::PADDWRegReg,      OP::PADDDRegReg,
           OP::PADDQRegReg,      OP::ADDPSRegReg,      OP::ADDPDRegReg}, // BinaryArithmeticAdd

          {OP::PSUBBRegReg,      OP::PSUBWRegReg,      OP::PSUBDRegReg,
           OP::PSUBQRegReg,      OP::SUBPSRegReg,      OP::SUBPDRegReg}, // BinaryArithmeticSub

          {OP::bad,              OP::PMULLWRegReg,     OP::PMULLDRegReg,
           OP::bad,              OP::MULPSRegReg,      OP::MULPDRegReg}, // BinaryArithmeticMul

          {OP::bad,              OP::bad,              OP::bad,
           OP::bad,              OP::DIVPSRegReg,      OP::DIVPDRegReg}, // BinaryArithmeticDiv

          {OP::PANDRegReg,       OP::PANDRegReg,       OP::PANDRegReg,
           OP::PANDRegReg,       OP::bad,              OP::bad}, // BinaryArithmeticAnd

          {OP::PORRegReg,        OP::PORRegReg,        OP::PORRegReg,
           OP::PORRegReg,        OP::bad,              OP::bad}, // BinaryArithmeticOr,

          {OP::PXORRegReg,       OP::PXORRegReg,       OP::PXORRegReg,
           OP::PXORRegReg,       OP::bad,              OP::bad}, // BinaryArithmeticXor

          {OP::PMINSBRegReg,     OP::PMINSWRegReg,     OP::PMINSDRegReg,
           OP::PMINSQRegReg,     OP::MINPSRegReg,      OP::MINPDRegReg}, // BinaryArithmeticMin

          {OP::PMAXSBRegReg,     OP::PMAXSWRegReg,     OP::PMAXSDRegReg,
           OP::PMAXSQRegReg,     OP::MAXPSRegReg,      OP::MAXPDRegReg}, // BinaryArithmeticMax

          {OP::bad,              OP::VPSLLVWRegRegReg, OP::VPSLLVDRegRegReg,
           OP::VPSLLVQRegRegReg, OP::bad,              OP::bad}, // BinaryLogicalShiftLeft

          {OP::bad,              OP::VPSRLVWRegRegReg, OP::VPSRLVDRegRegReg,
           OP::VPSRLVQRegRegReg, OP::bad,              OP::bad}, // BinaryLogicalShiftRight

          {OP::bad,              OP::VPSRAVWRegRegReg, OP::VPSRAVDRegRegReg,
           OP::VPSRAVQRegRegReg, OP::bad,              OP::bad}, // BinaryArithmeticShiftRight

          {OP::bad,              OP::bad,              OP::VPROLVDRegRegReg,
           OP::VPROLVQRegRegReg, OP::bad,              OP::bad}, // BinaryRotateLeft

          {OP::bad,              OP::bad,              OP::VPRORVDRegRegReg,
           OP::VPRORVQRegRegReg, OP::bad,              OP::bad}  // BinaryRotateRight
};

static const OP::Mnemonic VectorBinaryArithmeticOpCodesForMem[NumBinaryArithmeticOps]
                                                                         [TR::NumVectorElementTypes]
    = {
          //    Int8,                          Int16,                           Int32,
          //    Int64,                         Float,                           Double
          {OP::bad,              OP::bad,              OP::bad,
           OP::bad,              OP::bad,              OP::bad}, // BinaryArithmeticInvalid

          {OP::PADDBRegMem,      OP::PADDWRegMem,      OP::PADDDRegMem,
           OP::PADDQRegMem,      OP::ADDPSRegMem,      OP::ADDPDRegMem}, // BinaryArithmeticAdd

          {OP::PSUBBRegMem,      OP::PSUBWRegMem,      OP::PSUBDRegMem,
           OP::PSUBQRegMem,      OP::SUBPSRegMem,      OP::SUBPDRegMem}, // BinaryArithmeticSub

          {OP::bad,              OP::PMULLWRegMem,     OP::PMULLDRegMem,
           OP::bad,              OP::MULPSRegMem,      OP::MULPDRegMem}, // BinaryArithmeticMul

          {OP::bad,              OP::bad,              OP::bad,
           OP::bad,              OP::DIVPSRegMem,      OP::DIVPDRegMem}, // BinaryArithmeticDiv

          {OP::bad,              OP::bad,              OP::PANDRegMem,
           OP::PANDRegMem,       OP::bad,              OP::bad}, // BinaryArithmeticAnd

          {OP::bad,              OP::bad,              OP::PORRegMem,
           OP::PORRegMem,        OP::bad,              OP::bad}, // BinaryArithmeticOr,

          {OP::bad,              OP::bad,              OP::PXORRegMem,
           OP::PXORRegMem,       OP::bad,              OP::bad}, // BinaryArithmeticXor

          {OP::PMINSBRegMem,     OP::PMINSWRegMem,     OP::PMINSDRegMem,
           OP::PMINSQRegMem,     OP::bad,              OP::bad}, // BinaryArithmeticMin

          {OP::PMAXSBRegMem,     OP::PMAXSWRegMem,     OP::PMAXSDRegMem,
           OP::PMAXSQRegMem,     OP::bad,              OP::bad}, // BinaryArithmeticMax

          {OP::bad,              OP::bad,              OP::bad,
           OP::bad,              OP::bad,              OP::bad}, // BinaryLogicalShiftLeft

          {OP::bad,              OP::VPSRLVWRegRegMem, OP::VPSRLVDRegRegMem,
           OP::VPSRLVQRegRegMem, OP::bad,              OP::bad}, // BinaryLogicalShiftRight

          {OP::bad,              OP::VPSRAVWRegRegMem, OP::VPSRAVDRegRegMem,
           OP::VPSRAVQRegRegMem, OP::bad,              OP::bad}, // BinaryArithmeticShiftRight

          {OP::bad,              OP::bad,              OP::VPROLVDRegRegMem,
           OP::VPROLVQRegRegMem, OP::bad,              OP::bad}, // BinaryRotateLeft

          {OP::bad,              OP::bad,              OP::VPRORVDRegRegMem,
           OP::VPRORVQRegRegMem, OP::bad,              OP::bad}  // BinaryRotateRight
};

static const OP::Mnemonic VectorUnaryArithmeticOpCodesForReg[NumUnaryArithmeticOps]
                                                                        [TR::NumVectorElementTypes]
    = {
          //     Int8,                          Int16,                         Int32,
          //     Int64,                         Float,                         Double
          {OP::bad,          OP::bad,         OP::bad,
           OP::bad,          OP::bad,         OP::bad}, // UnaryArithmeticInvalid,

          {OP::PABSBRegReg,  OP::PABSWRegReg, OP::PABSDRegReg,
           OP::bad,          OP::bad,         OP::bad}, // UnaryArithmeticAbs,

          {OP::bad,          OP::bad,         OP::bad,
           OP::bad,          OP::SQRTPSRegReg,OP::SQRTPDRegReg} // UnaryArithmeticSqrt,
};

static const OP::Mnemonic VectorUnaryArithmeticOpCodesForMem[NumUnaryArithmeticOps]
                                                                        [TR::NumVectorElementTypes]
    = {
          //    Int8,                          Int16,                      Int32,
          //    Int64,                         Float,                      Double
          {OP::bad,         OP::bad,           OP::bad,
           OP::bad,         OP::bad,           OP::bad}, // UnaryArithmeticInvalid,

          {OP::PABSBRegMem, OP::PABSWRegMem,   OP::PABSDRegMem,
           OP::bad,         OP::bad,           OP::bad}, // UnaryArithmeticAbs,

          {OP::bad,         OP::bad,           OP::bad,
           OP::bad,         OP::VSQRTPSRegMem, OP::VSQRTPDRegMem}  // UnaryArithmeticSqrt,
};

// clang-format on

#endif
