module

public import VerifiedGarbage.Impl.Mont.AArch64

/-! Ordinary/Montgomery representation boundaries for native P-521 arithmetic. -/

@[expose] public section
namespace VG.Impl.Weierstrass.AArch64.P521Native
open VG.AArch64 VG.Impl.Mont.AArch64

def representationFromCode : List Instr := [
  .lsl .x .x1 .x8 9,
  .logic .orr .x .x21 .x21 .x1,
  .extr .x .x8 .x9 .x8 55,
  .extr .x .x9 .x10 .x9 55,
  .extr .x .x10 .x11 .x10 55,
  .extr .x .x11 .x12 .x11 55,
  .extr .x .x12 .x13 .x12 55,
  .extr .x .x13 .x14 .x13 55,
  .extr .x .x14 .x15 .x14 55,
  .extr .x .x15 .x21 .x15 55,
  .lsr .x .x21 .x21 55]

def representationToCode : List Instr := [
  .lsr .x .x1 .x15 18,
  .lsl .x .x2 .x21 46,
  .logic .orr .x .x1 .x1 .x2,
  .lsl .x .x2 .x8 55,
  .logic .orr .x .x1 .x1 .x2,
  .lsr .x .x21 .x15 9,
  .movz .x .x2 511 0,
  .logic .and .x .x21 .x21 .x2,
  .extr .x .x15 .x15 .x14 9,
  .extr .x .x14 .x14 .x13 9,
  .extr .x .x13 .x13 .x12 9,
  .extr .x .x12 .x12 .x11 9,
  .extr .x .x11 .x11 .x10 9,
  .extr .x .x10 .x10 .x9 9,
  .extr .x .x9 .x9 .x8 9,
  .addImm .x .x8 .x1 0]

def representationRegs : List Reg := [.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x21]

def representationMemoryCode (code : List Instr) (d : Nat) : List Instr :=
  loadsR .x0 representationRegs d++(code++storesR .x0 representationRegs d)

end VG.Impl.Weierstrass.AArch64.P521Native
