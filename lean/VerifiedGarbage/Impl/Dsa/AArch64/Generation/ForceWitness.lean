module

public import VerifiedGarbage.Impl.Bignum.AArch64

/-! The shared RSA sampler's forced branch at the candidate's byte width. -/
@[expose] public section
namespace VG.Impl.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum.AArch64

/-- x1 points to the already truncated witness. -/
def forceWitness (len : Nat) : List Instr :=
  [.ldrb .x3 .x1 0, movi .x4 127, .logic .and .x .x3 .x3 .x4, .strb .x3 .x1 0,
   .ldrb .x3 .x1 (len - 1), movi .x4 2, .logic .orr .x .x3 .x3 .x4, .strb .x3 .x1 (len - 1)]

end VG.Impl.Dsa.AArch64.Generation
