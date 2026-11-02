module

public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Scalar
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Freeze
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Comb

/-!
# `vg_ed25519_scalar_base(out = r3, scalar = r4, scratch = r5)` on PPC64LE

`[s] B` by the comb (`combMultiply`, `Comb.lean`), which reads the static
`combSym`, and its encoding into `out` (whose pointer is in `r27`).
`r14`–`r19` and `r26`–`r31` are saved at `SAVE` and `lr`, which the comb's
`adrSym` changes, at `LRS`.
-/

@[expose] public section

namespace VG.Impl.Ed25519.PPC64LE
open VG.PPC64LE

def scalarBaseEngine : Prog isa :=
  .seq (.block initFields) (.seq combMultiply pointEncode)

def scalarBaseSetup : List Instr :=
  scalarSave .r5 ++ [.addi .r6 .r5 0, .addi .r27 .r3 0, .mflr .r7, .store .d .r7 .r6 LRS,
    .addi .r14 .r4 0]

def scalarBaseFinish : List Instr :=
  [.load .d .r7 .r6 LRS, .mtlr .r7, .addi .r14 .r27 0] ++ packField FR 0 ++ scalarRestore

def scalarBase : Prog isa :=
  .seq (.block scalarBaseSetup) (.seq scalarBaseEngine (.block scalarBaseFinish))

end VG.Impl.Ed25519.PPC64LE
