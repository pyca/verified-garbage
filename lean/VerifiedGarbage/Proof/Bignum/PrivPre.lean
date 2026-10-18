module

public import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The precomputed values of an RSA private key

Target-independent: `pre` holding `privatePrecompute` of a key (`privatePreOk`)
gives `R² mod n`, `R_p mod p` and `R_q mod q` as numbers in memory
(`privatePre_vals`), and that `p q = n` for a valid modulus.
-/

@[expose] public section

namespace VG.Proof.Bignum

open VG

/-- `w` words of `pre` from word `d`, as a number, when they are those of `x`. -/
theorem wv_of_wordsAt_eq {m : Mem} {p : Addr} {L : Nat} {ws : List (BitVec 64)} (h : Spec.Rsa.wordsAt m p L = ws)
    {d w x : Nat} (hdw : d + w ≤ L) (hx : x < 2 ^ (64 * w))
    (hw : ∀ i < w, ws[d + i]? = some (BitVec.ofNat 64 (x / 2 ^ (64 * i)))) :
    wv m p (8 * d) w = x := by
  rw [← Nat.mod_eq_of_lt hx]
  refine wv_of_words fun i hi => ?_
  have e := congrArg (fun l => l[d + i]?) h
  simp only [Spec.Rsa.wordsAt, List.getElem?_map, List.getElem?_range (show d + i < L by omega),
    Option.map_some, hw i hi, Option.some.injEq] at e
  show (m.readW (p + BitVec.ofNat 64 (8 * d + 8 * i)) 64).toNat = _
  rw [show 8 * d + 8 * i = 8 * (d + i) by omega, e, BitVec.toNat_ofNat]

/-- `pre` holding `privatePrecompute` of a key with a `k`-octet modulus. -/
theorem privatePre_vals {m : Mem} {pre : Addr} {nB pB qB : List Byte} {k : Nat} (hl : nB.length = k)
    (h : Spec.Rsa.privatePrecompute nB pB qB = some (Spec.Rsa.wordsAt m pre
      (2 * ((k + 7) / 8) + Spec.Rsa.primeWords pB.length + Spec.Rsa.primeWords qB.length))) :
    Spec.Rsa.modulusValid (Spec.Rsa.os2ip nB) k = true ∧ Spec.Rsa.os2ip pB * Spec.Rsa.os2ip qB = Spec.Rsa.os2ip nB ∧
      wv m pre (8 * ((k + 7) / 8)) ((k + 7) / 8) =
        2 ^ (64 * ((k + 7) / 8)) * 2 ^ (64 * ((k + 7) / 8)) % Spec.Rsa.os2ip nB ∧
      wv m pre (8 * (2 * ((k + 7) / 8))) (Spec.Rsa.primeWords pB.length) =
        2 ^ (64 * Spec.Rsa.primeWords pB.length) % Spec.Rsa.os2ip pB ∧
      wv m pre (8 * (2 * ((k + 7) / 8) + Spec.Rsa.primeWords pB.length)) (Spec.Rsa.primeWords qB.length) =
        2 ^ (64 * Spec.Rsa.primeWords qB.length) % Spec.Rsa.os2ip qB := by
  generalize hw : (k + 7) / 8 = w at *
  generalize hwp : Spec.Rsa.primeWords pB.length = wp at *
  generalize hwq : Spec.Rsa.primeWords qB.length = wq at *
  have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nB) k = true := by
    cases hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nB) k
    · simp [Spec.Rsa.privatePrecompute, Spec.Rsa.publicPrecompute, hl, hv] at h
    · rfl
  have hpq : Spec.Rsa.os2ip pB * Spec.Rsa.os2ip qB = Spec.Rsa.os2ip nB := by
    by_contra hne
    simp [Spec.Rsa.privatePrecompute, Spec.Rsa.publicPrecompute, hl, hv, hne] at h
  simp only [Spec.Rsa.privatePrecompute, Spec.Rsa.publicPrecompute, hl, hv, ↓reduceIte, hpq, hwp, hwq,
    Spec.Rsa.modulusWords, hw, Option.some.injEq] at h
  have hN0 : 0 < Spec.Rsa.os2ip nB := by
    simp only [Spec.Rsa.modulusValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hv; omega
  have hP0 : 0 < Spec.Rsa.os2ip pB := Nat.pos_of_ne_zero fun e => by rw [e, Nat.zero_mul] at hpq; omega
  have hQ0 : 0 < Spec.Rsa.os2ip qB := Nat.pos_of_ne_zero fun e => by rw [e, Nat.mul_zero] at hpq; omega
  have hlen : ∀ {x n : Nat}, (Spec.Rsa.toWords x n).length = n := by simp [Spec.Rsa.toWords]
  have hget : ∀ {x n i : Nat}, i < n → (Spec.Rsa.toWords x n)[i]? = some (BitVec.ofNat 64 (x / 2 ^ (64 * i))) :=
    fun hi => by simp [Spec.Rsa.toWords, List.getElem?_range hi]
  have hlt : ∀ {x y n : Nat}, 0 < y → y ≤ 2 ^ (64 * n) → x % y < 2 ^ (64 * n) := fun hy hy' =>
    Nat.lt_of_lt_of_le (Nat.mod_lt _ hy) hy'
  -- A factor of `len` octets fits in `primeWords len` words.
  have hfit : ∀ {bs : List Byte}, Spec.Rsa.os2ip bs ≤ 2 ^ (64 * Spec.Rsa.primeWords bs.length) := fun {bs} => by
    have := os2ip_lt bs
    rw [pow256_eq] at this
    refine Nat.le_of_lt (Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) ?_))
    unfold Spec.Rsa.primeWords Spec.Rsa.modulusWords; omega
  have hN : Spec.Rsa.os2ip nB ≤ 2 ^ (64 * w) := by
    have := os2ip_lt nB
    rw [pow256_eq, hl] at this
    exact Nat.le_of_lt (Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega)))
  have hP := hfit (bs := pB)
  have hQ := hfit (bs := qB)
  rw [hwp] at hP
  rw [hwq] at hQ
  have hmid : ∀ (a b : List (BitVec 64)) {x n i : Nat}, i < n →
      (a ++ Spec.Rsa.toWords x n ++ b)[a.length + i]? = some (BitVec.ofNat 64 (x / 2 ^ (64 * i))) := by
    intro a b x n i hi
    rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_append_left (by rw [hlen]; exact hi), hget hi]
  refine ⟨hv, hpq, ?_, ?_, ?_⟩
  · rw [← Nat.pow_add, show 64 * w + 64 * w = 128 * w by omega]
    refine wv_of_wordsAt_eq h.symm (by omega) (hlt hN0 hN) fun i hi => ?_
    have := hmid (Spec.Rsa.toWords (Spec.Rsa.os2ip nB) w) (Spec.Rsa.toWords (2 ^ (64 * wp) % Spec.Rsa.os2ip pB) wp ++
      Spec.Rsa.toWords (2 ^ (64 * wq) % Spec.Rsa.os2ip qB) wq) (x := 2 ^ (128 * w) % Spec.Rsa.os2ip nB) hi
    rw [hlen] at this
    simpa only [List.append_assoc] using this
  · refine wv_of_wordsAt_eq h.symm (by omega) (hlt hP0 hP) fun i hi => ?_
    have := hmid (Spec.Rsa.toWords (Spec.Rsa.os2ip nB) w ++ Spec.Rsa.toWords (2 ^ (128 * w) % Spec.Rsa.os2ip nB) w)
      (Spec.Rsa.toWords (2 ^ (64 * wq) % Spec.Rsa.os2ip qB) wq) (x := 2 ^ (64 * wp) % Spec.Rsa.os2ip pB) hi
    rw [List.length_append, hlen, hlen, show w + w + i = 2 * w + i by omega] at this
    exact this
  · refine wv_of_wordsAt_eq h.symm (by omega) (hlt hQ0 hQ) fun i hi => ?_
    have := hmid (Spec.Rsa.toWords (Spec.Rsa.os2ip nB) w ++ Spec.Rsa.toWords (2 ^ (128 * w) % Spec.Rsa.os2ip nB) w ++
      Spec.Rsa.toWords (2 ^ (64 * wp) % Spec.Rsa.os2ip pB) wp) [] (x := 2 ^ (64 * wq) % Spec.Rsa.os2ip qB) hi
    rw [List.length_append, List.length_append, hlen, hlen, hlen, List.append_nil,
      show w + w + wp + i = 2 * w + wp + i by omega] at this
    exact this

end VG.Proof.Bignum
