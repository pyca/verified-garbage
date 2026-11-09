module

public import VerifiedGarbage.Impl.X25519.AArch64
public import VerifiedGarbage.Impl.Ed25519.AArch64.PointDecode
public import VerifiedGarbage.Impl.Ed25519.AArch64.Word

/-! Four-word X25519, sharing Ed25519's field operations and inversion. -/

@[expose] public section

namespace VG.Impl.X25519.AArch64.Word
open VG.AArch64
open VG.Impl.Ed25519.AArch64

abbrev ld := VG.Impl.Ed25519.AArch64.ld
abbrev st := VG.Impl.Ed25519.AArch64.st
abbrev freeze := VG.Impl.Ed25519.AArch64.freeze

abbrev SWAP : Nat := 768
abbrev OUT : Nat := 48
abbrev BITS : Nat := VG.Impl.X25519.AArch64.BITS

def setup : List Instr :=
  VG.Impl.X25519.AArch64.save ++ VG.Impl.X25519.AArch64.bits ++
  [VG.Impl.X25519.AArch64.st .x0 OUT, mov .x1 .x0, mov .x0 .x3] ++
  loadY ++ store4 (offset 0) ++
  fieldCode [.copy 3 0, .const 1 1, .const 2 0, .const 4 1, .const 18 121665] ++
  [.movz .x .x2 0 0, st .x2 SWAP]

def finish : List Instr :=
  fieldMul (offset 1) (offset 1) (offset 15) ++ freeze (offset 1) ++
  [.str .x .x4 .x1 0, .str .x .x5 .x1 8,
    .str .x .x6 .x1 16, .str .x .x7 .x1 24] ++
  VG.Impl.Ed25519.AArch64.saved.map (fun (r,o) => ld r o)

end VG.Impl.X25519.AArch64.Word
