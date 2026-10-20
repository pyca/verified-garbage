/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

The arithmetic schedule is adapted from s2n-bignum's `bignum_montsqr_p521_alt`
(arm/p521/bignum_montsqr_p521_alt.S), as distributed with AWS-LC in
aws-lc-sys 0.46.0. The Lean representation and proofs are maintained by
verified-garbage. Inputs are loaded before the arithmetic; caller state is
saved in caller-saved SIMD lanes rather than on the stack.
-/
module

public import VerifiedGarbage.Impl.Mont.AArch64

/-! Dedicated Montgomery squaring modulo P-521's field prime, using the
symmetry of the product and a fold at bit 521, followed by a 55-bit rotation.
The input is nine words below `2^521 - 1`, and the result is canonical and
congruent to its square times `2^-576`. -/

@[expose] public section
namespace VG.Impl.Mont.AArch64.P521Square
open VG VG.AArch64 VG.Impl.Mont.AArch64

/-- Input words, low first. The last word has at most nine bits. -/
def aRegs : List Reg := [.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x28]
/-- Seventeen words of the full square. -/
def uRegs : List Reg := [.x11,.x12,.x13,.x14,.x15,.x16,.x17,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x1]
def saved : List Reg := [.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x28,.x30]
def slot (i : Nat) : VReg × Nat :=
 ([VReg.v16,.v17,.v18,.v19,.v20,.v21].getD (i / 2) .v16, i % 2)
def saves : List Instr := saved.zipIdx.map fun (r,i) => .vop (.ins .d2 (slot i).1 (slot i).2 r)
def restores : List Instr := saved.zipIdx.map fun (r,i) => .umov .x r (slot i).1 (slot i).2

def cross0Code : List Instr := [
  .mul .x .x12 .x2 .x3,
  .umulh .x13 .x2 .x3,
  .mul .x .x10 .x2 .x4,
  .umulh .x14 .x2 .x4,
  .adds .x .x13 .x13 .x10,
  .mul .x .x10 .x2 .x5,
  .umulh .x15 .x2 .x5,
  .adcs .x .x14 .x14 .x10,
  .mul .x .x10 .x2 .x6,
  .umulh .x16 .x2 .x6,
  .adcs .x .x15 .x15 .x10,
  .mul .x .x10 .x2 .x7,
  .umulh .x17 .x2 .x7,
  .adcs .x .x16 .x16 .x10,
  .mul .x .x10 .x2 .x8,
  .umulh .x19 .x2 .x8,
  .adcs .x .x17 .x17 .x10,
  .mul .x .x10 .x2 .x9,
  .umulh .x20 .x2 .x9,
  .adcs .x .x19 .x19 .x10,
  .adc .x .x20 .x20 .x30
]

def cross1Code : List Instr := [
  .mul .x .x10 .x3 .x4,
  .adds .x .x14 .x14 .x10,
  .mul .x .x10 .x3 .x5,
  .adcs .x .x15 .x15 .x10,
  .mul .x .x10 .x3 .x6,
  .adcs .x .x16 .x16 .x10,
  .mul .x .x10 .x3 .x7,
  .adcs .x .x17 .x17 .x10,
  .mul .x .x10 .x3 .x8,
  .adcs .x .x19 .x19 .x10,
  .mul .x .x10 .x3 .x9,
  .adcs .x .x20 .x20 .x10,
  .adc .x .x21 .x30 .x30,
  .umulh .x10 .x3 .x4,
  .adds .x .x15 .x15 .x10,
  .umulh .x10 .x3 .x5,
  .adcs .x .x16 .x16 .x10,
  .umulh .x10 .x3 .x6,
  .adcs .x .x17 .x17 .x10,
  .umulh .x10 .x3 .x7,
  .adcs .x .x19 .x19 .x10,
  .umulh .x10 .x3 .x8,
  .adcs .x .x20 .x20 .x10,
  .umulh .x10 .x3 .x9,
  .adc .x .x21 .x21 .x10,
  .mul .x .x10 .x6 .x7,
  .umulh .x22 .x6 .x7,
  .adds .x .x21 .x21 .x10,
  .adc .x .x22 .x22 .x30
]

def cross2Code : List Instr := [
  .mul .x .x10 .x4 .x5,
  .adds .x .x16 .x16 .x10,
  .mul .x .x10 .x4 .x6,
  .adcs .x .x17 .x17 .x10,
  .mul .x .x10 .x4 .x7,
  .adcs .x .x19 .x19 .x10,
  .mul .x .x10 .x4 .x8,
  .adcs .x .x20 .x20 .x10,
  .mul .x .x10 .x4 .x9,
  .adcs .x .x21 .x21 .x10,
  .mul .x .x10 .x6 .x8,
  .adcs .x .x22 .x22 .x10,
  .adc .x .x23 .x30 .x30,
  .umulh .x10 .x4 .x5,
  .adds .x .x17 .x17 .x10,
  .umulh .x10 .x4 .x6,
  .adcs .x .x19 .x19 .x10,
  .umulh .x10 .x4 .x7,
  .adcs .x .x20 .x20 .x10,
  .umulh .x10 .x4 .x8,
  .adcs .x .x21 .x21 .x10,
  .umulh .x10 .x4 .x9,
  .adcs .x .x22 .x22 .x10,
  .umulh .x10 .x6 .x8,
  .adc .x .x23 .x23 .x10,
  .mul .x .x10 .x7 .x8,
  .umulh .x24 .x7 .x8,
  .adds .x .x23 .x23 .x10,
  .adc .x .x24 .x24 .x30
]

def cross3Code : List Instr := [
  .mul .x .x10 .x5 .x6,
  .adds .x .x19 .x19 .x10,
  .mul .x .x10 .x5 .x7,
  .adcs .x .x20 .x20 .x10,
  .mul .x .x10 .x5 .x8,
  .adcs .x .x21 .x21 .x10,
  .mul .x .x10 .x5 .x9,
  .adcs .x .x22 .x22 .x10,
  .mul .x .x10 .x6 .x9,
  .adcs .x .x23 .x23 .x10,
  .mul .x .x10 .x7 .x9,
  .adcs .x .x24 .x24 .x10,
  .adc .x .x25 .x30 .x30,
  .umulh .x10 .x5 .x6,
  .adds .x .x20 .x20 .x10,
  .umulh .x10 .x5 .x7,
  .adcs .x .x21 .x21 .x10,
  .umulh .x10 .x5 .x8,
  .adcs .x .x22 .x22 .x10,
  .umulh .x10 .x5 .x9,
  .adcs .x .x23 .x23 .x10,
  .umulh .x10 .x6 .x9,
  .adcs .x .x24 .x24 .x10,
  .umulh .x10 .x7 .x9,
  .adc .x .x25 .x25 .x10,
  .mul .x .x10 .x8 .x9,
  .umulh .x26 .x8 .x9,
  .adds .x .x25 .x25 .x10,
  .adc .x .x26 .x26 .x30
]

def doubleCode : List Instr := [
  .adds .x .x12 .x12 .x12,
  .adcs .x .x13 .x13 .x13,
  .adcs .x .x14 .x14 .x14,
  .adcs .x .x15 .x15 .x15,
  .adcs .x .x16 .x16 .x16,
  .adcs .x .x17 .x17 .x17,
  .adcs .x .x19 .x19 .x19,
  .adcs .x .x20 .x20 .x20,
  .adcs .x .x21 .x21 .x21,
  .adcs .x .x22 .x22 .x22,
  .adcs .x .x23 .x23 .x23,
  .adcs .x .x24 .x24 .x24,
  .adcs .x .x25 .x25 .x25,
  .adcs .x .x26 .x26 .x26,
  .adc .x .x27 .x30 .x30
]

def diagCode : List Instr := [
  .umulh .x10 .x2 .x2,
  .mul .x .x11 .x2 .x2,
  .adds .x .x12 .x12 .x10,
  .mul .x .x10 .x3 .x3,
  .adcs .x .x13 .x13 .x10,
  .umulh .x10 .x3 .x3,
  .adcs .x .x14 .x14 .x10,
  .mul .x .x10 .x4 .x4,
  .adcs .x .x15 .x15 .x10,
  .umulh .x10 .x4 .x4,
  .adcs .x .x16 .x16 .x10,
  .mul .x .x10 .x5 .x5,
  .adcs .x .x17 .x17 .x10,
  .umulh .x10 .x5 .x5,
  .adcs .x .x19 .x19 .x10,
  .mul .x .x10 .x6 .x6,
  .adcs .x .x20 .x20 .x10,
  .umulh .x10 .x6 .x6,
  .adcs .x .x21 .x21 .x10,
  .mul .x .x10 .x7 .x7,
  .adcs .x .x22 .x22 .x10,
  .umulh .x10 .x7 .x7,
  .adcs .x .x23 .x23 .x10,
  .mul .x .x10 .x8 .x8,
  .adcs .x .x24 .x24 .x10,
  .umulh .x10 .x8 .x8,
  .adcs .x .x25 .x25 .x10,
  .mul .x .x10 .x9 .x9,
  .adcs .x .x26 .x26 .x10,
  .umulh .x10 .x9 .x9,
  .adc .x .x27 .x27 .x10
]

def topCode : List Instr := [
  .mul .x .x1 .x28 .x28,
  .add .x .x28 .x28 .x28,
  .mul .x .x10 .x28 .x2,
  .adds .x .x20 .x20 .x10,
  .mul .x .x10 .x28 .x3,
  .adcs .x .x21 .x21 .x10,
  .mul .x .x10 .x28 .x4,
  .adcs .x .x22 .x22 .x10,
  .mul .x .x10 .x28 .x5,
  .adcs .x .x23 .x23 .x10,
  .mul .x .x10 .x28 .x6,
  .adcs .x .x24 .x24 .x10,
  .mul .x .x10 .x28 .x7,
  .adcs .x .x25 .x25 .x10,
  .mul .x .x10 .x28 .x8,
  .adcs .x .x26 .x26 .x10,
  .mul .x .x10 .x28 .x9,
  .adcs .x .x27 .x27 .x10,
  .adc .x .x1 .x1 .x30,
  .umulh .x10 .x28 .x2,
  .adds .x .x21 .x21 .x10,
  .umulh .x10 .x28 .x3,
  .adcs .x .x22 .x22 .x10,
  .umulh .x10 .x28 .x4,
  .adcs .x .x23 .x23 .x10,
  .umulh .x10 .x28 .x5,
  .adcs .x .x24 .x24 .x10,
  .umulh .x10 .x28 .x6,
  .adcs .x .x25 .x25 .x10,
  .umulh .x10 .x28 .x7,
  .adcs .x .x26 .x26 .x10,
  .umulh .x10 .x28 .x8,
  .adcs .x .x27 .x27 .x10,
  .umulh .x10 .x28 .x9,
  .adc .x .x1 .x1 .x10
]

def foldCode : List Instr := [
  .subs .x .x30 .x30 .x30,
  .extr .x .x10 .x21 .x20 9,
  .adcs .x .x11 .x11 .x10,
  .extr .x .x10 .x22 .x21 9,
  .adcs .x .x12 .x12 .x10,
  .extr .x .x10 .x23 .x22 9,
  .adcs .x .x13 .x13 .x10,
  .extr .x .x10 .x24 .x23 9,
  .adcs .x .x14 .x14 .x10,
  .extr .x .x10 .x25 .x24 9,
  .adcs .x .x15 .x15 .x10,
  .extr .x .x10 .x26 .x25 9,
  .adcs .x .x16 .x16 .x10,
  .extr .x .x10 .x27 .x26 9,
  .adcs .x .x17 .x17 .x10,
  .extr .x .x10 .x1 .x27 9,
  .adcs .x .x19 .x19 .x10,
  .subImm .x .x3 .x30 1,
  .lsl .x .x3 .x3 9,
  .logic .orr .x .x20 .x20 .x3,
  .lsr .x .x10 .x1 9,
  .adcs .x .x20 .x20 .x10
]

def correctCode : List Instr := [
  .sbcs .x .x11 .x11 .x30,
  .sbcs .x .x12 .x12 .x30,
  .sbcs .x .x13 .x13 .x30,
  .sbcs .x .x14 .x14 .x30,
  .sbcs .x .x15 .x15 .x30,
  .sbcs .x .x16 .x16 .x30,
  .sbcs .x .x17 .x17 .x30,
  .sbcs .x .x19 .x19 .x30,
  .sbc .x .x20 .x20 .x30,
  .movz .x .x3 511 0,
  .logic .and .x .x20 .x20 .x3
]

def rotateCode : List Instr := [
  .lsl .x .x10 .x11 9,
  .extr .x .x11 .x12 .x11 55,
  .extr .x .x12 .x13 .x12 55,
  .extr .x .x13 .x14 .x13 55,
  .extr .x .x14 .x15 .x14 55,
  .logic .orr .x .x20 .x20 .x10,
  .extr .x .x15 .x16 .x15 55,
  .extr .x .x16 .x17 .x16 55,
  .extr .x .x17 .x19 .x17 55,
  .extr .x .x19 .x20 .x19 55,
  .lsr .x .x20 .x20 55
]

/-- The full square, including the short top word. -/
def product : List Instr := cross0Code ++ cross1Code ++ cross2Code ++ cross3Code ++
 doubleCode ++ diagCode ++ topCode
/-- Canonical modular square and Montgomery conversion. -/
def core : List Instr := product ++ foldCode ++ correctCode ++ rotateCode
/-- Save caller state, set up pointers, and load all input words before any store. -/
def entry : List Instr :=
 [.addImm .w .x1 .x1 0,.addImm .w .x2 .x2 0,.addImm .w .x3 .x3 0] ++ saves ++
 [.add .x .x30 .x0 .x1,.add .x .x1 .x0 .x2] ++ loadsR .x1 aRegs 0 ++
 [.vop (.dup .d2 .v22 .x30),.movz .x .x30 0 0]
/-- Restore the output pointer, store the result, and restore caller state. -/
def exit : List Instr := [.umov .x .x30 .v22 0] ++ storesR .x30 (uRegs.take 9) 0 ++ restores
def square : Prog isa := .seq (.block entry) (.block (core ++ exit))
end VG.Impl.Mont.AArch64.P521Square
