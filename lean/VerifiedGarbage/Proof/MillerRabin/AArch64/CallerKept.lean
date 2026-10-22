module
public import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerSave
public import VerifiedGarbage.Spec.MillerRabin

import VerifiedGarbage.Proof.MillerRabin.Keeps

/-! # Recover the caller's header and padding after the prepared round -/

@[expose] public section

namespace VG.Proof.MillerRabin.AArch64.Caller

open VG VG.Proof.Bignum VG.Impl.Bignum VG.Impl.Bignum.Public

export VG.Proof.MillerRabin (kept_header)

theorem kept_padding {B : Addr} {n w d : Nat} {m m' : Mem}
    (h : Spec.MillerRabin.Keeps Spec.MillerRabin.compact B n w m m')
    (hn : pad w + 16 ≤ 8 * n) (hd : d ≤ 8) :
    word m' B (pad w + d) = word m B (pad w + d) := by
  apply keeps_word h (by omega_arith)
  · simp only [Spec.MillerRabin.compact, List.mem_cons, List.not_mem_nil, or_false]
    rintro i (rfl | rfl | rfl | rfl | rfl) <;>
      right <;> simp only [pad, slot, hdrBytes, aOne] <;> omega_arith
  · simp only [Spec.MillerRabin.compact, List.mem_cons, List.not_mem_nil, or_false]
    rintro i (rfl | rfl | rfl | rfl | rfl)
    all_goals simp only [Spec.Rsa.Mont.arrAt, Spec.Rsa.Mont.hdrBytes, pad, slot, hdrBytes, aOne]
    all_goals omega_arith
  · left
    simp only [Spec.MillerRabin.compact, Spec.Rsa.Mont.arrAt, Spec.Rsa.Mont.hdrBytes,
      pad, slot, hdrBytes, aOne]
    omega_arith

end VG.Proof.MillerRabin.AArch64.Caller
