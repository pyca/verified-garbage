module
public import VerifiedGarbage.Impl.Scrub.AArch64.Scrub


@[expose] public section

namespace VG.Impl.CmacAes.AArch64
open VG.AArch64
/-- A whole-block CMAC chaining implementation for streaming callers. -/
structure Update where
  name : String
  code : Prog isa
  /-- The registers its code writes, of those the calling convention does not
  preserve: what a function that calls it clears for it before returning,
  with those its own instructions write (`Impl.Scrub.AArch64.Clear.union`).
  The proofs hold it to the code (`Proof.CmacAes.AArch64.UpdateImpl.scrub`). -/
  clear : Impl.Scrub.AArch64.Clear
  /-- The bytes of working space it needs, none or 2176: a function that calls
  it has only these in its frame (`Proof.CmacAes.AArch64.UpdateImpl.scratch_eq`). -/
  scratch : Nat
end VG.Impl.CmacAes.AArch64
