import VerifiedGarbage.Proof.Mgf1.Basic
import VerifiedGarbage.Proof.RsaPss.CtPad

/-!
# MGF1, a byte at a time

Byte `p` of `MGF1(seed, n)` is byte `p mod hLen` of the digest of
`seed ‖ I2OSP(⌊p / hLen⌋, 4)` (`mgf1_getD`): what the implementations
compute, a counter at a time.
-/

namespace VG.Proof.RsaPss

open VG.Spec
open Spec.Mgf1 (Hash mgf1)
open Proof.Mgf1 (Valid)

theorem ifp {α : Sort _} {p : Prop} [Decidable p] (h : p) (a b : α) : (if p then a else b) = a :=
  ite_eq_left_of_eq_true a b (eq_true h)

theorem ifn {α : Sort _} {p : Prop} [Decidable p] (h : ¬ p) (a b : α) : (if p then a else b) = b :=
  ite_eq_right_of_eq_false a b (eq_false h)

theorem i2osp_len (x k : Nat) : (Rsa.i2osp x k).length = k := by simp [Rsa.i2osp]

/-- Byte `p` of the concatenation of `m` lists of `k` bytes. -/
theorem flatMap_getD {k : Nat} (hk : 0 < k) (f : Nat → List Byte) (hf : ∀ c, (f c).length = k) :
    ∀ m p, ((List.range m).flatMap f).getD p 0 = if p / k < m then (f (p / k)).getD (p % k) 0 else 0
  | 0, p => by simp [List.getD_eq_getElem?_getD]
  | m + 1, p => by
    rw [List.range_succ, List.flatMap_append, getD_app, flatMap_getD hk f hf m p]
    have hl : ((List.range m).flatMap f).length = k * m := by
      induction m with
      | zero => simp
      | succ m ih => rw [List.range_succ, List.flatMap_append, List.length_append, ih]; simp [hf, Nat.mul_succ]
    rw [hl]
    by_cases h : p < k * m
    · have : p / k < m := (Nat.div_lt_iff_lt_mul hk).mpr (by rw [Nat.mul_comm]; exact h)
      rw [ifp h, ifp this, ifp (by omega)]
    · rw [ifn h]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      by_cases h' : p < k * (m + 1)
      · have h'' : p < k * m + k := by rw [Nat.mul_succ] at h'; exact h'
        have e : p / k = m :=
          Nat.div_eq_of_lt_le (by rw [Nat.mul_comm]; omega) (by rw [Nat.succ_mul, Nat.mul_comm]; omega)
        rw [ifp (by omega), e, show p - k * m = p % k by rw [Nat.mod_eq_sub_mul_div, e]]
      · have : ¬ p / k < m + 1 := fun h'' => h' (by
          have := (Nat.div_lt_iff_lt_mul hk).mp h''; rw [Nat.mul_comm]; exact this)
        have h3 : k * m + k ≤ p := by rw [Nat.mul_succ] at h'; omega
        rw [ifn this, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hf]; omega)]
        rfl

/-- Byte `p` of an MGF1 mask. -/
theorem mgf1_getD {G : Hash} (hG : Valid G) (seed : List Byte) {n p : Nat} (hp : p < n) :
    (mgf1 G seed n).getD p 0 = (G.hash (seed ++ Rsa.i2osp (p / G.len) 4)).getD (p % G.len) 0 := by
  have hk := hG.1
  unfold mgf1
  rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hp, ← List.getD_eq_getElem?_getD,
    flatMap_getD hk _ (fun c => hG.2 _), ifp]
  exact (Nat.div_lt_iff_lt_mul hk).mpr (by
    have := Nat.lt_div_mul_add (a := n + G.len - 1) (b := G.len) hk
    have := Nat.div_add_mod (n + G.len - 1) G.len
    have := Nat.mod_lt (n + G.len - 1) hk
    rw [Nat.mul_comm] at *; omega)

end VG.Proof.RsaPss
