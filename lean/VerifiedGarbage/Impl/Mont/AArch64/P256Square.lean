/-
Copyright 2015-2020 The OpenSSL Project Authors. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0 OR ISC

The instruction schedule is adapted from Andy Polyakov's p256-armv8-asm.pl,
as distributed in AWS-LC (aws-lc-sys 0.45.0). The Lean representation and
proofs are maintained by verified-garbage.
-/
import VerifiedGarbage.Impl.Mont.AArch64

/-! Dedicated Montgomery squaring modulo the P-256 field prime. -/
namespace VG.Impl.Mont.AArch64.P256Square
open VG.AArch64 VG.Impl.Mont

/-- The exact P-256 Montgomery reduction coefficients, including the leading zero word. -/
def reduction : Red := .friendly [.pow2 32,.zero,.gen 18446744069414584321,.zero]

/-- Recognition is entirely at code-generation time. -/
def supported (M : Mod) : Bool := M.n == 4 && decide (M.red = reduction)

def crossCode : List Instr := [
    .mul .x .x9 .x5 .x4,
    .umulh .x2 .x5 .x4,
    .mul .x .x10 .x16 .x4,
    .umulh .x3 .x16 .x4,
    .mul .x .x11 .x17 .x4,
    .umulh .x12 .x17 .x4,
    .adds .x .x10 .x10 .x2,
    .mul .x .x1 .x16 .x5,
    .umulh .x2 .x16 .x5,
    .adcs .x .x11 .x11 .x3,
    .mul .x .x3 .x17 .x5,
    .umulh .x6 .x17 .x5,
    .adc .x .x12 .x12 .x7,
    .mul .x .x13 .x17 .x16,
    .umulh .x14 .x17 .x16,
    .adds .x .x2 .x2 .x3,
    .mul .x .x8 .x4 .x4,
    .adc .x .x3 .x6 .x7,
    .adds .x .x11 .x11 .x1,
    .umulh .x4 .x4 .x4,
    .adcs .x .x12 .x12 .x2,
    .mul .x .x2 .x5 .x5,
    .adcs .x .x13 .x13 .x3,
    .umulh .x5 .x5 .x5,
    .adc .x .x14 .x14 .x7]

def doubleCode : List Instr := [
    .adds .x .x9 .x9 .x9,
    .mul .x .x3 .x16 .x16,
    .adcs .x .x10 .x10 .x10,
    .umulh .x16 .x16 .x16,
    .adcs .x .x11 .x11 .x11,
    .mul .x .x6 .x17 .x17,
    .adcs .x .x12 .x12 .x12,
    .umulh .x17 .x17 .x17,
    .adcs .x .x13 .x13 .x13,
    .adcs .x .x14 .x14 .x14,
    .adc .x .x15 .x7 .x7]

def diagCode : List Instr := [
    .adds .x .x9 .x9 .x4,
    .adcs .x .x10 .x10 .x2,
    .adcs .x .x11 .x11 .x5,
    .adcs .x .x12 .x12 .x3,
    .adcs .x .x13 .x13 .x16,
    .lsl .x .x1 .x8 32,
    .adcs .x .x14 .x14 .x6,
    .lsr .x .x2 .x8 32,
    .adc .x .x15 .x15 .x17]

def reduceCode (next : Bool) : List Instr :=
  [.subs .x .x3 .x8 .x1, .sbc .x .x6 .x8 .x2,
   .adds .x .x8 .x9 .x1, .adcs .x .x9 .x10 .x2] ++
  (if next then [.lsl .x .x1 .x8 32] else []) ++
  [.adcs .x .x10 .x11 .x3] ++
  (if next then [.lsr .x .x2 .x8 32] else []) ++
  [.adc .x .x11 .x6 .x7]

def finishCode : List Instr :=
  [.adds .x .x8 .x8 .x12,.adcs .x .x9 .x9 .x13,.adcs .x .x10 .x10 .x14,
   .adcs .x .x11 .x11 .x15,.adc .x .x12 .x7 .x7]

def square (M : Mod) (o a : Nat) : List Instr :=
  zero7 :: loads bRegs a ++ crossCode ++ doubleCode ++ diagCode ++
  reduceCode true ++ reduceCode true ++ reduceCode true ++ reduceCode false ++
  finishCode ++ csubR M [.x8,.x9,.x10,.x11] .x12 ++ stores [.x8,.x9,.x10,.x11] o

end VG.Impl.Mont.AArch64.P256Square
