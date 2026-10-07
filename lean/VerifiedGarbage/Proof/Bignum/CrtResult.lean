import VerifiedGarbage.Proof.Bignum.CrtKey
import VerifiedGarbage.Proof.Bignum.CrtHdr
import VerifiedGarbage.Proof.Bignum.CrtPRanges
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# RSA with the CRT: the result

The result for a valid key (`crtResult`, `decryptCrt_eq`) and what is
written (`crtWritten_of`); what a valid modulus and the key's lengths give
(`crt_bounds_of`) and what the mask of the checks gives (`mask_facts`); and
that `p`'s phase keeps the header's arguments (`keepsHdr_pRanges`,
`keepsHdr_x`).
-/

namespace VG.Proof.Bignum

open VG VG.Impl.Bignum

/-- A factor of an odd `N`, its cofactor below `N`: odd and above 1. -/
theorem factor_facts {P Q N : Nat} (h : P * Q = N) (hP : P < N) (hN : N % 2 = 1) : 1 < Q ∧ Q % 2 = 1 := by
  have hodd := odd_of_mul_odd (by rw [Nat.mul_comm]; exact h) hN
  refine ⟨?_, hodd⟩
  rcases Nat.lt_or_ge 1 Q with h1 | h1
  · exact h1
  · rcases (show Q = 0 ∨ Q = 1 by omega) with rfl | rfl
    · rw [Nat.mul_zero] at h; omega
    · rw [Nat.mul_one] at h; omega

/-- The CRT's result for a valid key. -/
def crtResult (P Q dp dq QI C : Nat) : Nat :=
  C ^ dq % Q + Q * ((((C ^ dp % P : Nat) : Int) - (C ^ dq % Q : Nat)) * QI % (P : Int)).toNat

theorem decryptCrt_eq {N P Q dp dq QI C : Nat} :
    Spec.Rsa.decryptCrt N P Q dp dq QI C =
      if C < N ∧ P * Q = N ∧ QI < P then some (crtResult P Q dp dq QI C) else none := by
  simp only [Spec.Rsa.decryptCrt, crtResult, VG.Proof.Bignum.powMod_eq]

theorem keepsHdr_x {o wx : Nat} (ho : 8 * 32 ≤ o) : KeepsHdr (xRange o wx) := keepsHdr_ge (by simp only [xRange]; omega)

theorem keepsHdr_pRanges (w : Nat) : ∀ r ∈ pRanges w, KeepsHdr r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact keepsHdr_gRanges w r hr
  · rw [List.mem_singleton.mp hr]
    exact keepsHdr_ge (by have := hdr_lt_slot w Public.aX (show 31 < 32 by decide); simp only; omega)

/-- What a valid modulus and the key's lengths give. -/
theorem crt_bounds_of {k pl ql : Nat} {nb pb qb : List Byte}
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true) (hk1 : 64 ≤ k)
    (hpbl : pb.length = pl) (hpl2 : pl < k) (hqbl : qb.length = ql) (hql2 : ql < k) :
    Spec.Rsa.os2ip nb % 2 = 1 ∧ 1 < Spec.Rsa.os2ip nb ∧ Spec.Rsa.os2ip pb < Spec.Rsa.os2ip nb ∧
      Spec.Rsa.os2ip qb < Spec.Rsa.os2ip nb := by
  obtain ⟨hodd, hN1, _⟩ := valid_facts hv hk1
  have h256 : 256 ^ (k - 1) ≤ Spec.Rsa.os2ip nb := by
    simp only [Spec.Rsa.modulusValid, Bool.and_eq_true, decide_eq_true_eq] at hv; exact hv.2
  refine ⟨hodd, hN1, ?_, ?_⟩
  · have := os2ip_lt pb
    rw [hpbl] at this
    exact Nat.lt_of_lt_of_le this (Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) h256)
  · have := os2ip_lt qb
    rw [hqbl] at this
    exact Nat.lt_of_lt_of_le this (Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) h256)

/-- What the mask gives: the key's checks, and primes (or 3) odd and above 1. -/
theorem mask_facts {N C P Q QI : Nat} {Mk : Bool} (hMk : Mk = keyMask (decide (C < N)) N P Q QI)
    (hodd : N % 2 = 1) (hPN : P < N) (hQN : Q < N) :
    (Mk = true → C < N ∧ P * Q = N ∧ QI < P) ∧
      (1 < (if Mk then P else 3) ∧ (if Mk then P else 3) % 2 = 1) ∧
      (1 < (if Mk then Q else 3) ∧ (if Mk then Q else 3) % 2 = 1) := by
  have hMk' : Mk = true → C < N ∧ P * Q = N ∧ QI < P := fun hm => by
    rw [hMk] at hm
    simp only [keyMask, Bool.and_eq_true, decide_eq_true_eq] at hm
    exact ⟨hm.1.1, hm.1.2, hm.2⟩
  refine ⟨hMk', ?_, ?_⟩
  · cases Mk
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact ⟨by decide, by decide⟩
    · obtain ⟨_, hpq, _⟩ := hMk' rfl
      simp only [↓reduceIte]
      exact factor_facts (by rw [Nat.mul_comm]; exact hpq) hQN hodd
  · cases Mk
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact ⟨by decide, by decide⟩
    · obtain ⟨_, hpq, _⟩ := hMk' rfl
      simp only [↓reduceIte]
      exact factor_facts hpq hPN hodd

/-- What `vg_rsa_private_crt` leaves: the result `r` and the flag `c`
returned (`ret`) of its failure or its computation. -/
theorem crtWritten_of {m : Mem} {out : Addr} {k : Nat} {ret : BitVec 64} {nb xb pb qb dpb dqb qib : List Byte}
    (hnl : nb.length = k) {r : Nat} {c : Bool}
    (hb : Spec.Rsa.bytesAt m out k = Spec.Rsa.i2osp r k) (hr : ret = BitVec.ofNat 64 c.toNat)
    (hc : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true →
      (c = true ↔ Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb ∧ Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb =
        Spec.Rsa.os2ip nb ∧ Spec.Rsa.os2ip qib < Spec.Rsa.os2ip pb) ∧
      r = if c then crtResult (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip dpb) (Spec.Rsa.os2ip dqb)
        (Spec.Rsa.os2ip qib) (Spec.Rsa.os2ip xb) else 0)
    (hf : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = false → c = false ∧ r = 0) :
    Spec.Rsa.written m out k (ret.setWidth 32) (Spec.Rsa.privateCrt nb xb pb qb dpb dqb qib) := by
  simp only [Spec.Rsa.privateCrt]
  rw [hnl, hr, setWidth_flag]
  cases hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k
  · obtain ⟨rfl, rfl⟩ := hf hv
    simp only [Bool.false_eq_true, ite_false, Spec.Rsa.written]
    exact ⟨trivial, by rw [hb, i2osp_zero']⟩
  · obtain ⟨hiff, rfl⟩ := hc hv
    simp only [ite_true, decryptCrt_eq]
    cases c <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hb
    · have hx := mt hiff.mpr (by decide)
      simp only [hx, Bool.false_eq_true, ite_false, Option.map_none, Spec.Rsa.written]
      exact ⟨trivial, by rw [hb, i2osp_zero']⟩
    · simp only [hiff.mp rfl, and_self, ite_true, Option.map_some, Spec.Rsa.written]
      exact ⟨trivial, hb⟩

end VG.Proof.Bignum
