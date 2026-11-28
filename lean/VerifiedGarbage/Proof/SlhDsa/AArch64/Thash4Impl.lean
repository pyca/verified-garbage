module

public import VerifiedGarbage.Proof.SlhDsa.AArch64.Thash4Contract
public import VerifiedGarbage.Impl.SlhDsa.AArch64.Thash4
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubSide
public import VerifiedGarbage.Proof.Framework.AArch64.Depth

/-!
# SLH-DSA on AArch64: an implementation of `thash4`

What the code above `thash4` needs of an implementation of it, for outputs
of `n` bytes: the suffix of the names of the functions emitted with it (its
two-way permutation's, `X2Permutation.suffix`: `""` or `"_sha3"`), whether it
uses FEAT_SHA3 (which also chooses the single-state Keccak of the sponge
functions, `Shake.keccakOf`), its code, which is `Thash4.thash4 n sha3`, its
proof against `thash4Contract`, and what a call of it (`WP.callV`: no
frames) and the cleanup of its callers (`verifiedScrubbedClearAll`,
`verifiedScrubbedOfFill`: no instruction writes PSTATE.DIT, nothing is
called indirectly, no frames) need of its code. The functions above it
(`Impl/SlhDsa/AArch64/`) are proven once for any implementation; the
implementations are the elements of `Proof/Variants/SlhDsaThash4/AArch64.lean`.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64

open VG VG.AArch64

/-- An implementation of `thash4` for outputs of `n` bytes. -/
structure Thash4Impl (n : Nat) where
  sfx : String
  sha3 : Bool
  code : Prog isa
  code_eq : code = Impl.SlhDsa.AArch64.Thash4.thash4 n sha3
  verified : Verified AArch64.target code (thash4Contract n)
  noFrames : code.noFrames = true
  /-- What the cleanup of a function that calls it needs of its code. -/
  side : Scrub.sideAll (fun i => !i.writesDit) code = true
  depth : code.aarch64Depth = 0

end VG.Proof.SlhDsa.AArch64
