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
  let step := forwardParts nr ++ stores 128 ++ capture ++ advance ++ [.subImm .x .x11 .x11 1]
  .seq (.block ((aesPart nr 0 .x15).flatMap lowerXor3 ++ stores 0 ++ capture ++ [.subImm .x .x11 .x11 1])) <|
  .seq (.ite (.zero .x .x11) (.block []) (.loop (.block step) (.nonzero .x .x11))) <|
    .block ((ghWith forwardLd).flatMap lowerXor3 ++ advance)

/-- Save and restore the complete vector registers in unused bytes below the
GHASH table in the caller's existing scratch. The caller scrubs this region. -/
def forwardSeal : Prog isa :=
  let save := (List.range 8).map fun j => Instr.strq (cipherReg j) .x19 (368 + 16 * j)
  let restore := (List.range 8).map fun j => Instr.ldrq (cipherReg j) .x19 (368 + 16 * j)
  .seq (.block (save ++ setup)) (.seq (byRounds forwardLoop) (.block (finish ++ restore)))

end VG.Impl.Gcm.AArch64.Stitch
