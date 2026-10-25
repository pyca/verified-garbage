module

public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Proof.Ffdh.Lead
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.PowLit
import Batteries.Tactic.Init
import VerifiedGarbage.Proof.Framework.Omega

/-!
# FFDH: the scalar of a key-generation attempt, from its octets

A key-generation attempt cuts its random octets to the bit length of the
bound (`scalarBound`: q, or `p − 1`): it scans the bound's octets for the
first nonzero one (`lead`), zeros the octets before it, and masks the octet
at it with the bits up to the top bit of the bound's octet there
(`smearN`). That is `scalarOfOctets` (`cut_eq`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.KeyScalar

open VG VG.Spec.Ffdh
open VG.Spec.Rsa (os2ip)
open VG.Spec.RsaKeyGen (bitLength)
open VG.Proof.Bignum (os2ip_cons os2ip_lt os2ip_foldl)

/-- The bits up to the top one. -/
def smearN (n : Nat) : Nat :=
  let a := n ||| n >>> 1
  let b := a ||| a >>> 2
  b ||| b >>> 4

theorem smearN_eq : ∀ n < 256, smearN n = 2 ^ bitLength n - 1 := by decide +kernel

theorem smearN_lt : ∀ n < 256, smearN n < 256 := by decide +kernel

/-- The octets `r` cut at octet `ld`: zeros before it, `r[ld]` and'ed with
`t`, the rest kept. -/
def cut (r : List Byte) (ld : Nat) (t : Byte) : List Byte :=
  List.replicate ld 0 ++ ((r.getD ld 0) &&& t) :: r.drop (ld + 1)

theorem cut_length {r : List Byte} {ld : Nat} (t : Byte) (h : ld < r.length) : (cut r ld t).length = r.length := by
  simp only [cut, List.length_append, List.length_replicate, List.length_cons, List.length_drop]; omega_arith

/-- The octets of `cut`, one by one. -/
theorem cut_get {r : List Byte} {ld : Nat} (t : Byte) (h : ld < r.length) {i : Nat} (hi : i < r.length) :
    (cut r ld t)[i]'(by rw [cut_length t h]; exact hi) =
      if i < ld then 0 else if i = ld then r[i] &&& t else r[i] := by
  simp only [cut, List.getElem_append, List.length_replicate, List.getElem_replicate]
  by_cases h1 : i < ld
  · rw [dite_eq_left h1, ite_eq_left h1]
  · rw [dite_eq_right h1, ite_eq_right h1]
    by_cases h2 : i = ld
    · subst h2
      simp only [Nat.sub_self, List.getElem_cons_zero, ite_true, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hi, Option.getD_some]
    · rw [ite_eq_right h2]
      obtain ⟨j, rfl⟩ : ∃ j, i = ld + (j + 1) := ⟨i - ld - 1, by omega_arith⟩
      simp only [Nat.add_sub_cancel_left, List.getElem_cons_succ, List.getElem_drop]
      congr 1; omega_arith

theorem os2ip_zeros (l : List Byte) : ∀ n, os2ip (List.replicate n 0 ++ l) = os2ip l
  | 0 => rfl
  | n + 1 => by
    rw [List.replicate_succ, List.cons_append, os2ip_cons, os2ip_zeros l n]
    simp

theorem os2ip_append (l₁ l₂ : List Byte) : os2ip (l₁ ++ l₂) = os2ip l₁ * 256 ^ l₂.length + os2ip l₂ := by
  unfold os2ip
  rw [List.foldl_append, os2ip_foldl]
  rfl

theorem split_mod (T c R a j : Nat) (hR : R < 2 ^ a) (hj : j ≤ 8) :
    (T * 2 ^ (a + 8) + (c * 2 ^ a + R)) % 2 ^ (a + j) = c % 2 ^ j * 2 ^ a + R := by
  have hdvd : 2 ^ (a + j) ∣ T * 2 ^ (a + 8) := Nat.dvd_mul_left_of_dvd (Nat.pow_dvd_pow 2 (by omega_arith)) T
  rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hdvd, Nat.zero_add, Nat.mod_mod, Nat.pow_add, Nat.mod_mul]
  have h1 : (c * 2 ^ a + R) % 2 ^ a = R := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hR]
  have h2 : (c * 2 ^ a + R) / 2 ^ a = c := by
    rw [Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt hR, Nat.add_zero]
  rw [h1, h2, Nat.mul_comm (2 ^ a), Nat.add_comm]

/-- The value of the cut octets. -/
theorem cut_value {r : List Byte} {n e j : Nat} (hlen : r.length = n + e) (he : 1 ≤ e) (hj : j ≤ 8)
    {t : Byte} (ht : t.toNat = 2 ^ j - 1) : os2ip (cut r n t) = os2ip r % 2 ^ (8 * (e - 1) + j) := by
  unfold cut
  have hn : n < r.length := by omega_arith
  have hr : r = r.take n ++ (r.getD n 0) :: r.drop (n + 1) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some,
      ← List.drop_eq_getElem_cons hn, List.take_append_drop]
  have hd : (r.drop (n + 1)).length = e - 1 := by rw [List.length_drop]; omega_arith
  have hlt := os2ip_lt (r.drop (n + 1))
  rw [hd] at hlt
  have ha : (256 : Nat) ^ (e - 1) = 2 ^ (8 * (e - 1)) := by
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
  have hb : (256 : Nat) ^ (e - 1 + 1) = 2 ^ (8 * (e - 1) + 8) := by
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; congr 1
  rw [os2ip_zeros, os2ip_cons, hd, BitVec.toNat_and, ht, Nat.and_two_pow_sub_one_eq_mod, ha]
  conv => rhs; rw [hr, os2ip_append, os2ip_cons, List.length_cons, hd, ha, hb]
  rw [ha] at hlt
  exact (split_mod _ _ _ _ _ hlt hj).symm

/-- The cut octets from octet `n` on. -/
theorem cut_drop (r : List Byte) (n : Nat) (t : Byte) :
    (cut r n t).drop n = ((r.getD n 0) &&& t) :: r.drop (n + 1) := by
  unfold cut
  rw [List.drop_append_of_le_length (by simp), List.drop_replicate, Nat.sub_self, List.replicate_zero,
    List.nil_append]

/-- The cut octets from octet `n` on are the number. -/
theorem os2ip_cut_drop (r : List Byte) (n : Nat) (t : Byte) : os2ip ((cut r n t).drop n) = os2ip (cut r n t) := by
  rw [cut_drop]; unfold cut; rw [os2ip_zeros]

/-- Bit lengths from bounds. -/
theorem bitLength_eq {x b : Nat} (hb : 1 ≤ b) (hlo : 2 ^ (b - 1) ≤ x) (hhi : x < 2 ^ b) : bitLength x = b := by
  have hx : x ≠ 0 := by have := Nat.one_le_two_pow (n := b - 1); omega_arith
  unfold bitLength
  rw [ite_eq_right_iff.mpr (fun h => absurd h hx)]
  have h1 : 2 ^ x.log2 ≤ x := Nat.log2_self_le hx
  have h2 : x < 2 ^ (x.log2 + 1) := Nat.lt_log2_self
  have e1 : x.log2 < b := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (Nat.lt_of_le_of_lt h1 hhi)
  have e2 : b - 1 < x.log2 + 1 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (Nat.lt_of_le_of_lt hlo h2)
  omega_arith

theorem bitLength_bounds {x : Nat} (hx : x ≠ 0) : 2 ^ (bitLength x - 1) ≤ x ∧ x < 2 ^ bitLength x := by
  unfold bitLength
  rw [ite_eq_right_iff.mpr (fun h => absurd h hx), Nat.add_sub_cancel]
  exact ⟨Nat.log2_self_le hx, Nat.lt_log2_self⟩

/-- The bit length of a number from its first nonzero octet. -/
theorem bits_lead {bs : List Byte} (hne : bs ≠ []) :
    bitLength (os2ip bs) = 8 * (bs.length - lead bs - 1) + bitLength (bs[lead bs]'(lead_lt hne)).toNat := by
  have hL := lead_lt hne
  have hd : bs.drop (lead bs) = bs[lead bs] :: bs.drop (lead bs + 1) := List.drop_eq_getElem_cons hL
  have hv : os2ip bs = (bs[lead bs]).toNat * 256 ^ (bs.length - lead bs - 1) + os2ip (bs.drop (lead bs + 1)) := by
    rw [← os2ip_drop_lead, hd, os2ip_cons, List.length_drop]; congr 2
  have hR := os2ip_lt (bs.drop (lead bs + 1))
  rw [List.length_drop, show bs.length - (lead bs + 1) = bs.length - lead bs - 1 by omega_arith] at hR
  by_cases hc : (bs[lead bs]).toNat = 0
  · -- Then the octet is the last, and the number zero.
    have hl : ¬ lead bs + 1 < bs.length := fun h => lead_nonzero hne h (BitVec.eq_of_toNat_eq (by simpa using hc))
    have ha : bs.length - lead bs - 1 = 0 := by omega_arith
    rw [ha] at hv hR ⊢
    rw [hv, hc, show os2ip (bs.drop (lead bs + 1)) = 0 by simp at hR; omega_arith]
    rfl
  generalize bs.length - lead bs - 1 = a at hv hR ⊢
  generalize os2ip (bs.drop (lead bs + 1)) = R at hv hR
  · have hb := bitLength_bounds hc
    have h256 := (bs[lead bs]).isLt
    have hcb : bitLength (bs[lead bs]).toNat ≤ 8 := by
      by_contra hh
      have : 2 ^ 8 ≤ 2 ^ (bitLength (bs[lead bs]).toNat - 1) := Nat.pow_le_pow_right (by decide) (by omega_arith)
      omega_arith
    have hb1 : 1 ≤ bitLength (bs[lead bs]).toNat := by
      by_contra hh
      have : bitLength (bs[lead bs]).toNat = 0 := by omega_arith
      rw [this] at hb; simp at hb; omega_arith
    rw [VG.Proof.Bignum.pow256_eq] at hv hR
    rw [hv]
    refine bitLength_eq (by omega_arith) ?_ ?_
    · rw [show 8 * a + bitLength (bs[lead bs]).toNat - 1 = (bitLength (bs[lead bs]).toNat - 1) + 8 * a by omega_arith,
        Nat.pow_add]
      exact Nat.le_trans (Nat.mul_le_mul_right _ hb.1) (Nat.le_add_right _ _)
    · rw [Nat.add_comm (8 * a), Nat.pow_add]
      have : ((bs[lead bs]).toNat + 1) * 2 ^ (8 * a) ≤ 2 ^ bitLength (bs[lead bs]).toNat * 2 ^ (8 * a) :=
        Nat.mul_le_mul_right _ hb.2
      rw [Nat.add_mul, Nat.one_mul] at this
      omega_arith

/-- An odd number above 1 and its predecessor have the same bit length. -/
theorem bitLength_pred_odd {p : Nat} (hodd : p % 2 = 1) (h1 : 1 < p) : bitLength (p - 1) = bitLength p := by
  have hb := bitLength_bounds (show p ≠ 0 by omega_arith)
  have hb2 : 2 ≤ bitLength p := by
    by_contra hh
    have : 2 ^ bitLength p ≤ 2 ^ 1 := Nat.pow_le_pow_right (by decide) (by omega_arith)
    omega_arith
  have hne : p ≠ 2 ^ (bitLength p - 1) := by
    intro he
    have : 2 ^ (bitLength p - 1) % 2 = 0 := by
      rw [show bitLength p - 1 = (bitLength p - 2) + 1 by omega_arith, Nat.pow_succ, Nat.mul_mod_left]
    omega_arith
  exact bitLength_eq (by omega_arith) (by omega_arith) (by omega_arith)

/-- The octets of the bound the code scans: q's, or p's. -/
def bnd (k : Nat) (dom : List Byte) : List Byte :=
  if dom.length = 3 * k then (dom.drop (2 * k)).take k else dom.take k

theorem bnd_length {k : Nat} {dom : List Byte} (hd : dom.length = 2 * k ∨ dom.length = 3 * k) :
    (bnd k dom).length = k := by
  unfold bnd; split <;> simp <;> omega_arith

/-- The bound's bit length, from its octets. -/
theorem bound_bits {k : Nat} {dom : List Byte} (hk : 1 ≤ k) (hd : dom.length = 2 * k ∨ dom.length = 3 * k)
    (hp : dom.length ≠ 3 * k → os2ip (dom.take k) % 2 = 1 ∧ 1 < os2ip (dom.take k)) :
    bitLength (scalarBound (domainOf k dom)) = 8 * (k - lead (bnd k dom) - 1) +
      bitLength ((bnd k dom)[lead (bnd k dom)]'(lead_lt (by
        intro he; have := bnd_length hd; rw [he] at this; simp at this; omega_arith))).toNat := by
  have hl := bnd_length hd
  have hne : bnd k dom ≠ [] := by intro he; rw [he] at hl; simp at hl; omega_arith
  have e := bits_lead hne
  rw [hl] at e
  rw [← e]
  unfold scalarBound domainOf bnd
  by_cases h3 : dom.length = 3 * k
  · simp only [h3, ite_true, Option.getD_some]
  · simp only [h3, ite_false, Option.getD_none]
    exact bitLength_pred_odd (hp h3).1 (hp h3).2

/-- The cut octets of `rand` are the scalar of the attempt. -/
theorem cut_eq {k : Nat} {dom rb : List Byte} (hk : 1 ≤ k) (hd : dom.length = 2 * k ∨ dom.length = 3 * k)
    (hp : dom.length ≠ 3 * k → os2ip (dom.take k) % 2 = 1 ∧ 1 < os2ip (dom.take k)) (hrb : rb.length = k)
    {t : Byte} (ht : t.toNat = 2 ^ bitLength ((bnd k dom)[lead (bnd k dom)]'(lead_lt (by
        intro he; have := bnd_length hd; rw [he] at this; simp at this; omega_arith))).toNat - 1) :
    os2ip (cut rb (lead (bnd k dom)) t) = scalarOfOctets (domainOf k dom) rb := by
  have hl := bnd_length hd
  have hne : bnd k dom ≠ [] := by intro he; rw [he] at hl; simp at hl; omega_arith
  have hL := lead_lt hne
  rw [hl] at hL
  have h8 : bitLength ((bnd k dom)[lead (bnd k dom)]'(lead_lt hne)).toNat ≤ 8 := by
    by_cases hc : ((bnd k dom)[lead (bnd k dom)]'(lead_lt hne)).toNat = 0
    · rw [hc]; decide
    · have hb := bitLength_bounds hc
      have := ((bnd k dom)[lead (bnd k dom)]'(lead_lt hne)).isLt
      by_contra hh
      have : 2 ^ 8 ≤ 2 ^ (bitLength ((bnd k dom)[lead (bnd k dom)]'(lead_lt hne)).toNat - 1) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      omega_arith
  unfold scalarOfOctets
  rw [bound_bits hk hd hp]
  exact cut_value (n := lead (bnd k dom)) (e := k - lead (bnd k dom)) (by omega_arith) (by omega_arith) h8 ht

/-- `keyStatus` for valid parameters. -/
theorem keyStatus_eq {a : Parameters} (hv : parametersValid a = true) (x : Nat) :
    keyStatus a x = if privateValid a x = false then 2 else
      if publicValid ⟨a, a.g ^ x % a.p⟩ = true then 1 else 3 := by
  unfold keyStatus privateFrom publicFrom
  by_cases h1 : privateValid a x = false
  · simp [h1]
  · have h1' : privateValid a x = true := by simpa using h1
    by_cases h2 : publicValid ⟨a, a.g ^ x % a.p⟩ = true <;>
      simp [h1', h2, hv, VG.Proof.Bignum.powMod_eq]

end VG.Proof.Ffdh.KeyScalar
