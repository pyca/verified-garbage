module

public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Impl.Gcm.Clmul

/-! # GHASH using POWER8 polynomial multiply

Three `vpmsumd` instructions form the three parts of a 128-bit product;
two more fold it modulo the reflected GHASH polynomial. The block loop
keeps Y and the adjusted hash key in volatile vector registers. No scratch
space, saved GPRs, or scalar bit-at-a-time multiplication is needed.
-/

@[expose] public section
namespace VG.Impl.Gcm.PPC64LE.Vpmsum
open VG.PPC64LE
open VG.Impl.Gcm.Clmul (poly xInv2Hi)

abbrev Y : VReg := .v0
abbrev C : VReg := .v1
abbrev U : VReg := .v2
abbrev LO : VReg := .v3
abbrev MID : VReg := .v4
abbrev HI : VReg := .v5
abbrev A : VReg := .v6
abbrev T : VReg := .v7
abbrev H : VReg := .v16
abbrev MASK : VReg := .v18
abbrev Z : VReg := .v19

def reverseMask : BitVec 128 := 0x0f0e0d0c0b0a09080706050403020100

def const64 (d : Reg) (x : BitVec 64) : List Instr :=
  [.lis d (x.extractLsb' 48 16), .ori d d (x.extractLsb' 32 16), .lsl d d 32,
   .oris d d (x.extractLsb' 16 16), .ori d d (x.extractLsb' 0 16)]

/-- Form both halves explicitly: MT VSR leaves its other half undefined. -/
def pair (d : VReg) (hi lo : Reg) : List Instr :=
  [.mtvsrd d hi, .mtvsrd T lo,
   .vop (.sldoi d Z d 8), .vop (.sldoi d d T 8)]

def consts : List Instr :=
  [.li .r0 0, .vop (.logic .xor Z Z Z)] ++
  const64 .r8 poly ++ pair C .r8 .r8 ++
  const64 .r8 (reverseMask.extractLsb' 64 64) ++
  const64 .r9 (reverseMask.extractLsb' 0 64) ++ pair MASK .r8 .r9 ++
  const64 .r8 xInv2Hi ++ [.li .r9 3] ++ pair H .r8 .r9

/-- Reverse the 16 loaded bytes: logical low doubleword = first big-endian half. -/
def loadRev (d : VReg) (p : Reg) : List Instr :=
  [.lxvd2x d p .r0, .vop (.perm d d d MASK)]

def products (a key : VReg) : List Instr :=
  [.vop (.sldoi U a Z 8), .vop (.pmsumd HI U key),
   .vop (.sldoi U Z a 8), .vop (.pmsumd LO U key),
   .vop (.pmsumd MID a key)]

def reduce (d : VReg) : List Instr :=
  [.vop (.sldoi T LO Z 8), .vop (.pmsumd T T C),
   .vop (.sldoi LO LO LO 8), .vop (.logic .xor MID MID LO), .vop (.logic .xor MID MID T),
   .vop (.sldoi T MID Z 8), .vop (.pmsumd T T C),
   .vop (.sldoi HI HI HI 8), .vop (.logic .xor HI HI MID),
   .vop (.sldoi T T T 8), .vop (.logic .xor d HI T)]

def mul (d a key : VReg) : List Instr := products a key ++ reduce d

def prologue : List Instr := consts ++ loadRev A .r3 ++ mul H A H ++
  [.vop (.sldoi H H H 8)] ++ loadRev Y .r4

def body : List Instr := loadRev A .r5 ++ [.vop (.logic .xor A A Y)] ++ mul Y A H ++
  [.addi .r5 .r5 16, .subi .r6 .r6 1]

def epilogue : List Instr := [.vop (.perm T Y Y MASK), .stxvd2x T .r4 .r0]

def ghash : Prog isa := .ite (.zero .d .r6) (.block [])
  (.seq (.block prologue) (.seq (.loop (.block body) (.nonzero .d .r6)) (.block epilogue)))

end VG.Impl.Gcm.PPC64LE.Vpmsum
