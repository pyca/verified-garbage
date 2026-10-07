import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Front
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Lcm
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.DPart
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Small

/-!
# An RSA key from its primes on AArch64: from the primes to `smallMask`

`front2_k`: after `p − 1` and `q − 1` (`KPrimes`), `L = lcm(p − 1, q − 1)`,
`d` and `x15` the mask of `d` too small (`KFront`).
-/

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

/-- From `KPrimes` to `KFront`: `lcmPart`, `dPart` and `smallMask`. -/
theorem front2_k {I : KIn} {s₀ s : State} (h : KPrimes I s₀ s) (L : KLens I) :
    WP isa (seqs (lcmPart ++ ([dPart] ++ smallMask))) s (KFront I s₀) := by
  have hk := h.ks
  have hZ := hk.hZ
  have hW := L.W
  have hw8 : 8 * I.pl = 64 * (I.pl / 8) := by have := L.pl8; omega
  -- `L`.
  refine wp_seqs_append (by simp [lcmPart, phi, mulTo]) (by simp) (WP.mono (lcm_k hk hW h.vPm h.vQm
    (Nat.lt_of_le_of_lt (Nat.sub_le _ _) L.P_lt) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) L.Q_lt))
    fun s₅ ⟨h₅, f₅, vL₅⟩ => ?_)
  have hokL : csL.all Rc.ok = true := by decide
  have ev₅ : word s₅.mem I.B (8 * kEv) = BitVec.ofNat 64 I.E := by
    rw [f₅.word hokL (by decide) (by decide), h.ev]
  -- `d`.
  refine wp_seqs_append (a := [dPart]) (by simp) (by simp [smallMask, constA]) ?_
  refine WP.mono (dPart_k h₅ L.E_lt ev₅ vL₅ L.L_lt) fun s₆ ⟨h₆, f₆, d₆⟩ => ?_
  obtain ⟨ok, ok₆, iff₆, dd₆⟩ := d₆
  -- `x15`.
  refine WP.mono (smallMask_k h₆ hW ok₆) fun t ⟨ht, f₇, x15₇⟩ => ?_
  have hokD : csD.all Rc.ok = true := by decide
  have hok7 : [Rc.arr aC].all Rc.ok = true := by decide
  have pres : ∀ j, j < 16 → Rc.arr j ∉ csD → Rc.arr j ∉ [Rc.arr aC] → Rc.arr j ∉ csL →
      av I t.mem j = av I s.mem j := fun j hj h1 h2 h3 => by
    rw [f₇.av hok7 hj h2 hZ, f₆.av hokD hj h1 hZ, f₅.av hokL hj h3 hZ]
  have okt : word t.mem I.B (8 * kOk) = mask ok := by rw [f₇.word hok7 (by decide) (by decide), ok₆]
  have hD : av I t.mem aDd = av I s₆.mem aDd := f₇.av hok7 (by decide) (by decide) hZ
  refine ⟨ht, ?_, ?_, ?_, ?_, ?_, ⟨ok, okt, iff₆, fun d hd => by rw [hD]; exact dd₆ d hd⟩,
    ⟨ok, okt, iff₆, by rw [x15₇, hD, hw8]⟩⟩
  · rw [pres aPa (by decide) (by decide) (by decide) (by decide), h.vP]
  · rw [pres aQa (by decide) (by decide) (by decide) (by decide), h.vQ]
  · rw [pres aPm (by decide) (by decide) (by decide) (by decide), h.vPm]
  · rw [pres aQm (by decide) (by decide) (by decide) (by decide), h.vQm]
  · rw [f₇.word hok7 (by decide) (by decide), f₆.word hokD (by decide) (by decide), ev₅]

end VG.Proof.RsaKeyGen.AArch64.Key
