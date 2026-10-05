import VerifiedGarbage.Proof.Bignum.Math

/-!
# RSA: octet strings, and the checked private operation from its parts

Target-independent facts about `Spec/Rsa.lean` that need no algebra:

* OS2IP and I2OSP are inverse on `k` octets (`os2ip_i2osp`, `i2osp_os2ip`),
  and the result of the CRT is below `n` (`decryptCrt_lt`).
* `privateChecked_of_crt`: the checked private operation is the unchecked
  one (`privateCrt`), followed by the public operation of its result
  (`publicOpChecked`) compared with the input: what an implementation
  computes, from the results of the functions it calls.
-/

namespace VG.Proof.Rsa

open VG.Spec.Rsa
open VG.Proof.Bignum (powMod_eq)

/-! ## Octet strings -/

theorem os2ip_snoc (l : List Byte) (b : Byte) : os2ip (l ++ [b]) = 256 * os2ip l + b.toNat := by
  simp only [os2ip, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem i2osp_succ (x k : Nat) : i2osp x (k + 1) = i2osp (x / 256) k ++ [BitVec.ofNat 8 x] := by
  simp only [i2osp, List.range_succ, List.map_append, List.map_cons, List.map_nil]
  congr 1
  · refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ']
    congr 3
    omega
  · rw [show k + 1 - 1 - k = 0 by omega, Nat.pow_zero, Nat.div_one]

/-- I2OSP then OS2IP keeps the low `k` octets. -/
theorem os2ip_i2osp (x k : Nat) : os2ip (i2osp x k) = x % 256 ^ k := by
  induction k generalizing x with
  | zero => simp [i2osp, os2ip, Nat.mod_one]
  | succ k ih =>
    rw [i2osp_succ, os2ip_snoc, ih, Nat.pow_succ', Nat.mod_mul, BitVec.toNat_ofNat]
    omega

theorem i2osp_length (x k : Nat) : (i2osp x k).length = k := by
  simp [i2osp]

/-- An integer of `k` octets is below `256^k`. -/
theorem lt_of_os2ip (bs : List Byte) : os2ip bs < 256 ^ bs.length := by
  obtain ⟨l, rfl⟩ : ∃ l, bs = l.reverse := ⟨bs.reverse, (List.reverse_reverse bs).symm⟩
  induction l with
  | nil => simp [os2ip]
  | cons b l ih =>
    rw [List.reverse_cons]
    rw [os2ip_snoc, List.length_append, List.length_singleton, Nat.pow_succ]
    have := b.isLt
    simp only [Nat.reducePow] at this
    omega

/-! ## The CRT -/

/-- `h = (m₁ - m₂) qInv mod p` of `decryptCrt`, for `p > 0`, is below `p`. -/
theorem crt_h_lt {p : Nat} (hp : 0 < p) (x : Int) : (x % (p : Int)).toNat < p := by
  have h1 := Int.emod_nonneg x (by omega : (p : Int) ≠ 0)
  have h2 := Int.emod_lt_of_pos x (by omega : (0 : Int) < p)
  omega

/-- The result of `decryptCrt` is below `n`. -/
theorem decryptCrt_lt {n p q dP dQ qInv c m : Nat}
    (h : decryptCrt n p q dP dQ qInv c = some m) : m < n := by
  simp only [decryptCrt] at h
  split at h
  · rename_i hc
    obtain ⟨hcn, hpq, -⟩ := hc
    cases h
    have hp : 0 < p := Nat.pos_of_ne_zero fun h0 => by subst h0; omega
    have hq : 0 < q := Nat.pos_of_ne_zero fun h0 => by subst h0; simp at hpq; omega
    have hm₂ : powMod c dQ q < q := by rw [powMod_eq]; exact Nat.mod_lt _ hq
    have hh := crt_h_lt hp (((powMod c dP p : Nat) - (powMod c dQ q : Nat)) * (qInv : Int))
    -- `m₂ + q h ≤ (q - 1) + q (p - 1) = p q - 1`.
    have : q * (((powMod c dP p : Nat) - (powMod c dQ q : Nat)) * (qInv : Int) %
        (p : Int)).toNat ≤ q * (p - 1) := Nat.mul_le_mul_left _ (by omega)
    have : q * (p - 1) + q = p * q := by
      rw [Nat.mul_sub_one, Nat.mul_comm q p]; have := Nat.le_mul_of_pos_left q hp; omega
    omega
  · simp at h

/-- OS2IP then I2OSP at the string's length is the string. -/
theorem i2osp_os2ip (bs : List Byte) : i2osp (os2ip bs) bs.length = bs := by
  obtain ⟨l, rfl⟩ : ∃ l, bs = l.reverse := ⟨bs.reverse, (List.reverse_reverse bs).symm⟩
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [List.reverse_cons]
    have hb := b.isLt
    rw [os2ip_snoc, List.length_append, List.length_singleton, i2osp_succ,
      show (256 * os2ip l.reverse + b.toNat) / 256 = os2ip l.reverse by omega, ih]
    congr 2
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    omega

/-- I2OSP of an integer below `256^k` is a string of `k` octets exactly when
the integer is its OS2IP. -/
theorem i2osp_eq_iff {x : Nat} {bs : List Byte} (hx : x < 256 ^ bs.length) :
    i2osp x bs.length = bs ↔ x = os2ip bs := by
  constructor
  · intro h
    rw [← h, os2ip_i2osp, Nat.mod_eq_of_lt hx]
  · rintro rfl
    exact i2osp_os2ip bs

/-! ## The checked private operation from its parts -/

/-- The checked private operation of an input of `k` octets is the private
operation, then the public operation (with BoringSSL's limits on `e`) of its
result, compared with the input: `ok` with the result if they match,
`fault` if not, and `invalid` if either refuses the key or the input. -/
theorem privateChecked_of_crt {nB eB xB pB qB dPB dQB qInvB : List Byte} (hx : xB.length = nB.length) :
    privateChecked nB eB xB pB qB dPB dQB qInvB =
      match privateCrt nB xB pB qB dPB dQB qInvB with
      | none => .invalid
      | some mB =>
        if exponentValid (os2ip eB) then
          if publicOpChecked nB eB mB = some xB then .ok mB else .fault
        else .invalid := by
  simp only [privateChecked, privateCrt, decryptChecked]
  by_cases hm : modulusValid (os2ip nB) nB.length = true
  · cases hd : decryptCrt (os2ip nB) (os2ip pB) (os2ip qB) (os2ip dPB) (os2ip dQB) (os2ip qInvB) (os2ip xB) with
    | none => simp [hm]
    | some m =>
      have hlt := decryptCrt_lt hd
      have hk := lt_of_os2ip nB
      have hn : 0 < os2ip nB := by omega
      by_cases he : exponentValid (os2ip eB) = true
      · have hpub : publicOpChecked nB eB (i2osp m nB.length) =
            some (i2osp (powMod m (os2ip eB) (os2ip nB)) nB.length) := by
          simp only [publicOpChecked, he, publicOp, hm, encrypt, os2ip_i2osp,
            Nat.mod_eq_of_lt (Nat.lt_trans hlt hk), hlt, ite_true, Option.map_some]
        have hP : powMod m (os2ip eB) (os2ip nB) < 256 ^ xB.length := by
          rw [powMod_eq, hx]; exact Nat.lt_trans (Nat.mod_lt _ hn) hk
        have hiff : i2osp (powMod m (os2ip eB) (os2ip nB)) nB.length = xB ↔
            powMod m (os2ip eB) (os2ip nB) = os2ip xB := by
          rw [← hx]; exact i2osp_eq_iff hP
        simp only [hm, he, and_self, ite_true, Option.map_some, hpub, Option.some.injEq, hiff]
        by_cases hc : powMod m (os2ip eB) (os2ip nB) = os2ip xB <;> simp [hc]
      · simp [hm, he]
  · simp [hm]

/-- A result of the private operation is for a valid modulus, and the public
operation of it succeeds for every exponent within BoringSSL's limits. -/
theorem privateCrt_some {nB xB pB qB dPB dQB qInvB y : List Byte}
    (h : privateCrt nB xB pB qB dPB dQB qInvB = some y) :
    modulusValid (os2ip nB) nB.length = true ∧
      ∀ eB, exponentValid (os2ip eB) = true → (publicOpChecked nB eB y).isSome = true := by
  simp only [privateCrt] at h
  split at h
  · rename_i hm
    obtain ⟨m, hd, rfl⟩ := Option.map_eq_some_iff.mp h
    have hlt := decryptCrt_lt hd
    refine ⟨hm, fun eB he => ?_⟩
    simp only [publicOpChecked, he, publicOp, hm, encrypt, os2ip_i2osp,
      Nat.mod_eq_of_lt (Nat.lt_trans hlt (lt_of_os2ip nB)), hlt, ite_true, Option.map_some, Option.isSome_some]
  · cases h

end VG.Proof.Rsa
