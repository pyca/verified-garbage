module

import VerifiedGarbage.Impl.Sm4.AArch64.Ctr
public import VerifiedGarbage.Impl.Modes.AArch64.CbcChained
public import VerifiedGarbage.Impl.Tbl.AArch64
public import VerifiedGarbage.Impl.Modes.AArch64.Ctr
public import VerifiedGarbage.Impl.Sm4.AArch64.Ecb
public import VerifiedGarbage.Spec.Sm4
public import VerifiedGarbage.Spec.Sm4.Contract

/-! # A single-block SM4 core with a register-resident S-box

Sequential modes do not benefit from enciphering sixteen copies of each
block. Prepare the 256 constant S-box bytes and the 128 schedule bytes in
scratch, then use NEON register table lookups on the one block. Every table
load has a public fixed address; secret indices stay inside vector registers.
The existing mode interface retains validation, chaining, stack framing and
zeroization. The buffer and total workspace match the existing SM4 core.
-/

@[expose] public section

namespace VG.Impl.Sm4.AArch64.Serial

open VG VG.AArch64 VG.Impl.Aes.AArch64

def substitute : List Instr :=
 [.vop (.dup .s4 .v0 .x10), .vop (.logic .eor .v1 .v0 .v4),
  .vop (.logic .eor .v2 .v0 .v5), .vop (.logic .eor .v3 .v0 .v6)] ++
 VG.Impl.Tbl.AArch64.select true ++ [.umov .w .x10 .v0 0]

def quarterConstants : List Instr :=
 [.movz .w .x15 64 0, .vop (.dup .b16 .v4 .x15),
  .movz .w .x15 128 0, .vop (.dup .b16 .v5 .x15),
  .movz .w .x15 192 0, .vop (.dup .b16 .v6 .x15)]

def mixKey (b c d : Reg) (i : Nat) : List Instr :=
  [.ldr .w .x10 .x5 (256+4*i), .logic .eor .w .x10 .x10 b,
   .logic .eor .w .x10 .x10 c, .logic .eor .w .x10 .x10 d]

def wordReg (i : Nat) : Reg := (#[.x6,.x7,.x8,.x9] : Array Reg)[i]!

def roundInput (i : Nat) : List Instr :=
  mixKey (wordReg ((i+1)%4)) (wordReg ((i+2)%4)) (wordReg ((i+3)%4)) i

def linear : List Instr :=
  [.logicRor .eor .w .x11 .x10 .x10 30, .logicRor .eor .w .x11 .x11 .x10 22,
   .logicRor .eor .w .x11 .x11 .x10 14, .logicRor .eor .w .x11 .x11 .x10 8]

def roundOutput (i : Nat) : List Instr :=
  [.logic .eor .w (wordReg (i%4))
    (wordReg (i%4)) .x11]

def round (i : Nat) : List Instr := roundInput i ++ substitute ++ linear ++ roundOutput i

def tableWord (h : Nat) : BitVec 64 := BitVec.ofNat 64 <| (List.range 8).foldl
  (fun a j => a + (Spec.Sm4.sbox.getD (8*h+j) 0).toNat * 2^(8*j)) 0

def tableEntries : List (Nat × BitVec 64) := (List.range 32).map fun h => (h,tableWord h)

def preparedTable : List Instr := VG.Impl.Sm4.AArch64.setSlots tableEntries

def loadSbox : List Instr :=
  (List.range 16).map fun i => .ldrq (VG.Impl.Tbl.AArch64.treg i) .x5 (16*i)

def copySchedule : Prog isa :=
  .seq (.block [movR .x14 .x0,.addImm .x .x15 .x5 256,.movz .x .x17 8 0])
    VG.Impl.Sm4.AArch64.copyBlocks

def loadBlock : List Instr :=
  (List.range 4).flatMap fun i =>
    let r := wordReg i
    [.ldr .w r .x5 (768+4*i),.rev32 r r]

def storeBlock : List Instr :=
  (List.range 4).flatMap fun i =>
    let r := wordReg (3-i)
    [.rev32 r r,.str .w r .x5 (768+4*i)]

def core : VG.Impl.Modes.AArch64.Core where
 prepare := .seq (.block preparedTable) copySchedule
 crypt := .block (loadSbox ++ quarterConstants ++ loadBlock ++ (List.range 32).flatMap round ++ storeBlock)
 slots := 396
 total := 408
 buf := 96
 lgG := 0
 keyRegs := [.x0]
 dataReg := .x23
 leftReg := .x24

def cbcEncryptChained : Prog isa := core.cbcEncryptChained ⟨.x1,.x2,.x3,.x4⟩ .x19

end VG.Impl.Sm4.AArch64.Serial
