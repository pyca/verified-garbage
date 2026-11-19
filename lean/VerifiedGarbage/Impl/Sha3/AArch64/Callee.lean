module

public import VerifiedGarbage.Impl.Sha3.AArch64
public import VerifiedGarbage.Impl.Residue.AArch64.Union

@[expose] public section

namespace VG.Impl.Sha3.AArch64

/-- A permutation implementation and the suffix propagated to every caller. -/
structure Callee where
  name : String
  code : Prog VG.AArch64.isa
  suffix : String
  /-- The registers its code writes, of those the calling convention does not
  preserve: what a function that calls it clears for it before returning,
  with those its own instructions write (`Clear.union`). The proofs hold it to
  the code (`Proof.Sha3.AArch64.Permutation.scrub`). -/
  clear : Impl.Residue.AArch64.Clear
  /-- Paired-state sponge kernels may use ARM SHA3 instructions on this backend. -/
  pairedSha3 : Bool := false
  /-- An independently verified full absorb entry point, when this backend
  keeps the permutation state resident across complete input blocks. -/
  absorbOverride : Option (Prog VG.AArch64.isa) := none

def Callee.scalar : Callee where
  name := "vg_keccak_f1600"
  code := permute
  suffix := ""
  clear := ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15], [], []⟩

/-- The registers `vg_keccak_f1600_sha3` writes (`Sha3.Vector.permute`): the
`clear` of every `Callee` whose code it is. -/
def Callee.sha3Clear : Impl.Residue.AArch64.Clear :=
  ⟨[.x16, .x17],
   [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26,
    .v27, .v28, .v29, .v30, .v31],
   [.v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15]⟩

end VG.Impl.Sha3.AArch64
