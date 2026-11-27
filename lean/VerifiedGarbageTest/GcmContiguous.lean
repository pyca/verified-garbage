module

import VerifiedGarbage.Spec.Gcm.Contiguous

/-! The contiguous contract agrees with the existing GCM results for both public layouts. -/

namespace VG.Test.GcmContiguous

open Spec.Gcm

variable (pb : Nat) (ctx nonce aad src dst tag desc : Addr)
  (rounds nonceLen aadLen len : BitVec pb) (m m' : Mem)

example :
    sealContiguousPost pb ctx rounds nonce nonceLen aad aadLen src src len tag m m' 0 =
      sealPost pb ctx rounds nonce nonceLen aad aadLen src len tag m m' 0 := rfl

example (one : Sig.listed pb m .u8 desc 1 = [⟨src, len.toNat⟩])
    (count : BitVec pb) (hc : count.toNat = 1) :
    sealContiguousPost pb ctx rounds nonce nonceLen aad aadLen src dst len tag m m' 0 ↔
      sealGatherPost pb ctx rounds nonce nonceLen aad aadLen desc count dst len tag m m' 0 := by
  simp [sealContiguousPost, sealGatherPost, gatheredLen, gathered, hc, one]

end VG.Test.GcmContiguous
