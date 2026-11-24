module

public import VerifiedGarbage.Impl.Gcm.AArch64.Stitch
public import VerifiedGarbage.Impl.Gcm.AArch64.Xor3

@[expose] public section
namespace VG.Impl.Gcm.AArch64.Stitch
open VG.AArch64

/-- Previous batch of ciphertext, reversed within each doubleword for GHASH. -/
def cipherReg : Nat → VReg
  | 0 => .v8 | 1 => .v9 | 2 => .v10 | 3 => .v11
  | 4 => .v12 | 5 => .v13 | 6 => .v14 | _ => .v15

def forwardLd (d : VReg) (j : Nat) : List Instr :=
  [.vop (.logic .orr d (cipherReg j) (cipherReg j))]

/-- Retain the eight just-encrypted blocks in GHASH byte order. -/
def capture : List Instr :=
  (List.range 8).map fun j => .vop (.rev .rev64b (cipherReg j) (breg j))

/-- Keep the schedule positions of the old memory loads when weaving the
two instruction streams. The empty group emits no instruction. -/
def forwardGroup (i : Instr) : List (List Instr) :=
  match i with
  | .vop (.logic .orr ..) => [[], [i]]
  | _ => [[i]]

def forwardParts (nr : Nat) : List Instr :=
  (VG.Impl.Weave.weaveG (fuse (aesPart nr 128 .x15)) ((ghWith forwardLd).flatMap forwardGroup)).flatMap lowerXor3

def forwardLoop (nr : Nat) : Prog isa :=
  let advance := [.addImm .x .x15 .x15 128, .addImm .x .x9 .x9 128]
  let step := forwardParts nr ++ stores 128 ++ advance ++ [.subImm .x .x11 .x11 1] ++ capture
  .seq (.block ((aesPart nr 0 .x15).flatMap lowerXor3 ++ stores 0 ++ [.subImm .x .x11 .x11 1] ++ capture)) <|
  .seq (.ite (.zero .x .x11) (.block []) (.loop (.block step) (.nonzero .x .x11))) <|
    .block ((ghWith forwardLd).flatMap lowerXor3 ++ advance)

/-- Volatile integer registers free throughout the batch loop. The round
count, pointers, and block count are already in the shared kernel's registers. -/
def vecSaves : List (VReg × Reg) :=
  [(.v8,.x0),(.v9,.x1),(.v10,.x2),(.v11,.x3),(.v12,.x4),(.v13,.x5),(.v14,.x6),(.v15,.x7)]

def forwardSave := vecSaves.map fun (v,r) => Instr.umov .x r v 0
def forwardRestore := vecSaves.map fun (v,r) => Instr.vop (.ins .d2 v 0 r)

def forwardCore : Prog isa := .seq (.block setup) (.seq (byRounds forwardLoop) (.block finish))

def forwardSeal : Prog isa := .seq (.block forwardSave) (.seq forwardCore (.block forwardRestore))

def forwardCall : Prog isa := .call "vg_aes_gcm_seal_batches_aes" forwardSeal

end VG.Impl.Gcm.AArch64.Stitch
