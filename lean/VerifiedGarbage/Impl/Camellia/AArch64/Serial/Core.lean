module

public import VerifiedGarbage.Impl.Camellia.AArch64.Ecb
import VerifiedGarbage.Impl.Modes.AArch64.CbcChained
public import VerifiedGarbage.Impl.Tbl.AArch64
public import VerifiedGarbage.Spec.Camellia
public import VerifiedGarbage.Impl.Modes.AArch64.Ctr
public import VerifiedGarbage.Impl.Modes.FbMode

/-! # A single-block Camellia core for dependent feedback modes

Keep the S-box in vector registers and the Feistel halves in scalar registers.
The existing NEON table selection uses public loads and secret register indices.
The buffer and total workspace retain the existing mode contract's allocation.
-/

@[expose] public section
namespace VG.Impl.Camellia.AArch64.Serial
open VG VG.AArch64 VG.Impl.Aes.AArch64


def tableWord (h : Nat) : BitVec 64 := BitVec.ofNat 64 <| (List.range 8).foldl
 (fun a j => a + (Spec.Camellia.sbox1Table.getD (8*h+j) 0).toNat * 2^(8*j)) 0

def tableEntries : List (Nat × BitVec 64) := (List.range 32).map fun h => (h,tableWord h)

def table : List Instr := VG.Impl.Camellia.AArch64.setSlots tableEntries

def loadSbox : List Instr :=
 (List.range 16).map fun i => Instr.ldrq (VG.Impl.Tbl.AArch64.treg i) .x5 (16*i)

def quarterConstants : List Instr :=
 [.movz .w .x15 64 0, .vop (.dup .b16 .v4 .x15),
  .movz .w .x15 128 0, .vop (.dup .b16 .v5 .x15),
  .movz .w .x15 192 0, .vop (.dup .b16 .v6 .x15)]

def maskConstants : List Instr :=
 imm .x15 0x000000ff0000ff00 ++ [.vop (.dup .d2 .v7 .x15)] ++
 imm .x13 0x00ff0000ff000000 ++ imm .x14 0x0000ff0000ff0000

def constants : List Instr := loadSbox ++ quarterConstants ++ maskConstants

/-- Rotate each selected byte, retaining all other bytes. -/
def rotateSelected (mask : VReg) (sh : Nat) : List Instr :=
 [.vop (.shift .shl .b16 .v1 .v0 sh),
  .vop (.shift .sri .b16 .v1 .v0 (8-sh)),
  .vop (.bsel .bit .v0 .v1 mask)]

def indices : List Instr :=
 [.vop (.logic .eor .v1 .v0 .v4), .vop (.logic .eor .v2 .v0 .v5),
  .vop (.logic .eor .v3 .v0 .v6)]

def substitute : List Instr := [.vop (.dup .d2 .v0 .x10)] ++
 rotateSelected .v7 1 ++ indices ++ VG.Impl.Tbl.AArch64.select true ++
 [.vop (.dup .d2 .v3 .x13)] ++ rotateSelected .v3 1 ++
 [.vop (.dup .d2 .v3 .x14)] ++ rotateSelected .v3 7 ++ [.umov .x .x10 .v0 0]

def linear : List Instr := [
 .lsr .x .x11 .x10 32, .addImm .w .x12 .x10 0,
 .logicRor .eor .w .x16 .x11 .x11 8, .logicRor .eor .w .x16 .x16 .x11 16,
 .extr .w .x17 .x12 .x12 8, .logicRor .eor .w .x17 .x17 .x12 16,
 .logicRor .eor .w .x17 .x17 .x12 24,
 .logic .eor .w .x16 .x16 .x17,
 .logicRor .eor .w .x12 .x11 .x11 24, .logic .eor .w .x12 .x12 .x17,
 .lsl .x .x10 .x16 32, .logic .orr .x .x10 .x10 .x12]

def mixKey (a : Reg) (k : Nat) : List Instr :=
 [.ldr .x .x8 .x5 (256+8*k), .rev .x8 .x8, .logic .eor .x .x10 a .x8]

def f (a b : Reg) (k : Nat) : List Instr :=
 mixKey a k ++ substitute ++ linear ++ [.logic .eor .x b b .x10]

def flLow : List Instr :=
 [.logic .and .w .x11 .x10 .x16, .extr .w .x11 .x11 .x11 31,
  .logic .eor .w .x12 .x12 .x11]

def flHigh : List Instr :=
 [.logic .orr .w .x11 .x12 .x8, .logic .eor .w .x10 .x10 .x11]

def flInput (r : Reg) (k : Nat) : List Instr :=
 [.ldr .x .x8 .x5 (256+8*k), .rev .x8 .x8, .lsr .x .x10 r 32,
  .addImm .w .x12 r 0, .lsr .x .x16 .x8 32]

def joinHalves (r : Reg) : List Instr :=
 [.lsl .x r .x10 32, .logic .orr .x r r .x12]

def fl (r : Reg) (k : Nat) (inv : Bool) : List Instr :=
 flInput r k ++ (if inv then flHigh ++ flLow else flLow ++ flHigh) ++ joinHalves r

def roundPair (k : Nat) : List Instr := f .x6 .x7 k ++ f .x7 .x6 (k+1)

def six (k : Nat) : List Instr :=
 (List.range 3).flatMap fun j => roundPair (k+2*j)

def flPair (k : Nat) : List Instr := fl .x6 k false ++ fl .x7 (k+1) true

def loadBE (r : Reg) (off : Nat) : List Instr :=
 [.ldr .x r .x5 off, .rev r r]

def xorKey (r : Reg) (k : Nat) : List Instr :=
 loadBE .x10 (256+8*k) ++ [.logic .eor .x r r .x10]

def loadBlock : List Instr :=
 loadBE .x6 768 ++ loadBE .x7 776 ++ xorKey .x6 0 ++ xorKey .x7 1

def storeBlock : List Instr :=
 [.rev .x7 .x7, .rev .x6 .x6, .str .x .x7 .x5 768, .str .x .x6 .x5 776]

def whitening (k : Nat) : List Instr := xorKey .x7 k ++ xorKey .x6 (k+1) ++ storeBlock

def copySchedule : Prog isa :=
 .seq (.block [movR .x14 .x0, .addImm .x .x15 .x5 256, .movz .x .x17 17 0])
   VG.Impl.Camellia.AArch64.copyBlocks

def roundsPrefix : List Instr := six 2 ++ flPair 8 ++ six 10 ++ flPair 16 ++ six 18

def cryptBody : Prog isa :=
 .seq (.block (roundsPrefix ++ [.subImm .x .x8 .x1 18]))
   (.ite (.zero .x .x8) (.block (whitening 24))
     (.block (flPair 24 ++ six 26 ++ whitening 32)))

def core : VG.Impl.Modes.AArch64.Core where
 prepare := .seq (.block table) copySchedule
 crypt := .seq (.block (constants ++ loadBlock)) cryptBody
 slots := 394
 total := 418
 buf := 96
 lgG := 0
 keyRegs := [.x0,.x1]
 dataReg := .x23
 leftReg := .x24



end VG.Impl.Camellia.AArch64.Serial
