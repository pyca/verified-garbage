module
-- separate module: the arithmetic of the result, apart from the code's proofs

public import VerifiedGarbage.Proof.Bignum.X86.PrivPre.Wrap
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.ExportEncoding
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-! # `vg_rsa_private_precompute` on x86: what `pre` holds

From what the body leaves (`PreVals`, the bytes under the mask), `pre`
holds `privatePrecompute`'s words and the result is 1 when it is `some`,
and zeros and 0 when it is `none` (`final_post`): with `p q = n` for a valid
`n`, `p` and `q` are odd and above 1, so the safe factors are the factors.
-/

@[expose] public section
namespace VG.Proof.Bignum.X86.PrivPre
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Dsa.X86 (argumentPointer)

theorem wordsAt_append (m : Mem) (p : Addr) (a b : Nat) :
    Spec.Rsa.wordsAt m p (a + b) =
      Spec.Rsa.wordsAt m p a ++ Spec.Rsa.wordsAt m (p + BitVec.ofNat 64 (8 * a)) b := by
  rw [Spec.Rsa.wordsAt, Spec.Rsa.wordsAt, Spec.Rsa.wordsAt, List.range_add, List.map_append, List.map_map]
  refine congrArg _ (List.map_congr_left fun i _ => ?_)
  simp only [Function.comp_apply]
  rw [Offset.add_add, Nat.mul_add]

/-- `w` words from the number of `8 w` bytes they hold. -/
theorem wordsAt_read {m : Mem} {p : Addr} {w x : Nat} (h : (m.read p (8 * w)).toNat = x) :
    Spec.Rsa.wordsAt m p w = Spec.Rsa.toWords x w := by
  have hx : VG.Proof.Bignum.wv m p 0 w = x := by
    rw [← VG.Proof.Bignum.read_eq_wv]; simpa only [off, BitVec.add_zero] using h
  simp only [Spec.Rsa.wordsAt, Spec.Rsa.toWords]
  refine List.map_congr_left fun i hi => ?_
  have := VG.Proof.Bignum.word_eq_ofNat m p 0 w (List.mem_range.mp hi)
  simpa only [Nat.zero_add, hx, VG.Proof.Bignum.word, off] using this

/-- `w` words from the `2 w` words of 32 bits at `p + d`. -/
theorem wordsAt_val32 {m : Mem} {p : Addr} {d w : Nat} :
    Spec.Rsa.wordsAt m (p + BitVec.ofNat 64 d) w = Spec.Rsa.toWords (val32 m p d (2 * w)) w := by
  refine wordsAt_read ?_
  rw [show 8 * w = 4 * (2 * w) by omega]
  exact VG.Proof.Bignum.read_eq_val32 m p (2 * w) d

/-- A factor of a valid modulus whose other factor is shorter than it is safe. -/
theorem safe_factor {N P Q k : Nat} (hv : Spec.Rsa.modulusValid N k = true) (hpq : P * Q = N)
    (hq : Q < 256 ^ (k - 1)) : CrtRt.safeM P = P := by
  rw [Spec.Rsa.modulusValid, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hv
  obtain ⟨⟨⟨h1, h2⟩, -⟩, h4⟩ := hv
  have odd := beq_iff_eq.mp h1
  have big := of_decide_eq_true h2
  have top := of_decide_eq_true h4
  have hm := Nat.mul_mod P Q 2
  refine CrtRt.safeM_of ?_ ?_
  · rcases Nat.lt_or_ge 1 P with h | h
    · exact h
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with rfl | rfl
      · rw [Nat.zero_mul] at hpq; subst hpq; exact absurd big (Nat.not_le.mpr (Nat.two_pow_pos 511))
      · rw [Nat.one_mul] at hpq; subst hpq; clear big; omega
  · rcases Nat.mod_two_eq_zero_or_one P with h | h
    · rw [h, Nat.zero_mul, Nat.zero_mod, hpq, odd] at hm; exact absurd hm (by decide)
    · exact h

section
variable {s : State}

/-- `p`'s and `q`'s bytes. -/
abbrev pBytes (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (argumentPointer s 4) (arg s 5).toNat
abbrev qBytes (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (argumentPointer s 6) (arg s 7).toNat

theorem final_post (A : PPABI s) {X : Nat} {m m' : Mem} (P : PreVals s X m)
    (hb : ∀ i < (arg s 1).toNat * 8, m' (argumentPointer s 0 + BitVec.ofNat 64 i) =
      m (argumentPointer s 0 + BitVec.ofNat 64 i) &&& (0 - stBit s).setWidth 8) :
    match Spec.Rsa.privatePrecompute (nBytes s) (pBytes s) (qBytes s) with
    | some ws => stBit s = 1 ∧ Spec.Rsa.wordsAt m' (argumentPointer s 0) (arg s 1).toNat = ws
    | none => stBit s = 0 ∧ Spec.Rsa.wordsAt m' (argumentPointer s 0) (arg s 1).toNat =
        List.replicate (arg s 1).toNat 0 := by
  have hl := A.preLength
  simp only [Spec.Rsa.privatePrecomputedWords, Spec.Rsa.precomputedWords] at hl
  have l := A.lengths
  simp only [Spec.Rsa.lenValid] at l
  have zeros : stBit s = 0 → Spec.Rsa.wordsAt m' (argumentPointer s 0) (arg s 1).toNat =
      List.replicate (arg s 1).toNat 0 := fun h0 =>
    wordsAt_zeros fun i hi => by rw [Nat.mul_comm] at hi; rw [hb i hi, h0]; simp
  unfold Spec.Rsa.privatePrecompute
  by_cases hpq : Spec.Rsa.os2ip (pBytes s) * Spec.Rsa.os2ip (qBytes s) = Spec.Rsa.os2ip (nBytes s)
  · have pr : prBit s = 1 := by simp only [prBit, valueAt]; rw [decide_eq_true hpq]; rfl
    have pub := P.pub
    cases hp : Spec.Rsa.publicPrecompute (nBytes s) with
    | none =>
      have h0 : stBit s = 0 := by simp [stBit, pcBit, hp]
      simp only [hpq, Option.map_none]
      exact ⟨h0, zeros h0⟩
    | some ws =>
      have h1 : stBit s = 1 := by simp only [stBit, pcBit, hp, pr]; rfl
      simp only [hpq, Option.map_some]
      refine ⟨h1, ?_⟩
      -- the mask keeps every byte
      have K : Spec.Rsa.wordsAt m' (argumentPointer s 0) (arg s 1).toNat =
          Spec.Rsa.wordsAt m (argumentPointer s 0) (arg s 1).toNat :=
        wordsAt_keep fun i hi => by
          rw [Nat.mul_comm] at hi
          rw [hb i hi, h1, show ((0 : BitVec 32) - 1).setWidth 8 = BitVec.allOnes 8 from rfl, BitVec.and_allOnes]
      rw [K]
      -- `n` valid, and the safe factors are the factors
      have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (nBytes s)) (arg s 3).toNat = true := by
        have hlen := VG.Proof.Bignum.bytesAt_length s.mem (argumentPointer s 2) (arg s 3).toNat
        cases hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (nBytes s)) (arg s 3).toNat
        · simp [Spec.Rsa.publicPrecompute, hlen, hv] at hp
        · rfl
      have qlt : Spec.Rsa.os2ip (qBytes s) < 256 ^ ((arg s 3).toNat - 1) := by
        have := VG.Proof.Bignum.os2ip_lt (qBytes s)
        rw [VG.Proof.Bignum.bytesAt_length] at this
        exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by have := A.qLength; omega))
      have plt : Spec.Rsa.os2ip (pBytes s) < 256 ^ ((arg s 3).toNat - 1) := by
        have := VG.Proof.Bignum.os2ip_lt (pBytes s)
        rw [VG.Proof.Bignum.bytesAt_length] at this
        exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by have := A.pLength; omega))
      have sp : CrtRt.safeM (valueAt s 4) = valueAt s 4 := safe_factor hv hpq qlt
      have sq : CrtRt.safeM (valueAt s 6) = valueAt s 6 := safe_factor hv (by rw [Nat.mul_comm]; exact hpq) plt
      have fb : fixB (arg s 3).toNat = 128 * Spec.Rsa.modulusWords (arg s 3).toNat := by
        simp only [fixB, CrtRt.bc, CrtRt.mw]; omega
      have xv := P.x ws hp
      have Pp := P.p (by
        rw [sp, xv, fb, Nat.mod_mod_of_dvd _ ⟨valueAt s 6, by simpa [valueAt, nBytes, pBytes, qBytes] using hpq.symm⟩])
      have Pq := P.q (by
        rw [sq, xv, fb, Nat.mod_mod_of_dvd _ ⟨valueAt s 4, by
          rw [Nat.mul_comm]; simpa [valueAt, nBytes, pBytes, qBytes] using hpq.symm⟩])
      rw [sp] at Pp
      rw [sq] at Pq
      have d1 : 8 * (2 * Spec.Rsa.modulusWords (arg s 3).toNat) = dstOff s none := by simp only [dstOff]; omega
      have d2 : 8 * (2 * Spec.Rsa.modulusWords (arg s 3).toNat + Spec.Rsa.primeWords (arg s 5).toNat) =
          dstOff s (some 5) := by simp only [dstOff]; omega
      rw [hl, wordsAt_append, wordsAt_append, pub, hp, d1, d2, wordsAt_val32, wordsAt_val32, Pp, Pq]
      simp only [Spec.Rsa.primeR2, VG.Proof.Bignum.bytesAt_length, r2Exp, valueAt]
  · have h0 : stBit s = 0 := by
      simp only [stBit, prBit, valueAt]; rw [decide_eq_false hpq]; simp
    simp only [hpq, ite_false]
    exact ⟨h0, zeros h0⟩

end
end VG.Proof.Bignum.X86.PrivPre
