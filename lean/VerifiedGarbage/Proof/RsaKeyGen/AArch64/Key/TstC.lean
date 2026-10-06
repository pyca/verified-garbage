import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Shared

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem t1 (s : State) (E : BitVec 64) (h3 : s.gpr .x3 = E) :
    WP isa (.block [movi .x4 3, .subs .x .x3 .x3 .x4]) s fun t => (t.c = decide (3 ≤ E.toNat) ∧ t.mem = s.mem) ∧
      Keep [.x3, .x4] s t := by
  refine WP.keep [.x3, .x4] ?_ (by decide) (by decide) (by decide +kernel)
  brun [h3]

end VG.Proof.RsaKeyGen.AArch64.Key
