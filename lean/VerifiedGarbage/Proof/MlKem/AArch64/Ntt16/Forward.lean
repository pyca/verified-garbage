module

public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Trace
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Arith
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lit
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lit
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Trace

/-!
# The NTT: its values, and its code

`fw F l` is the coefficients after `l` layers, of which the code computes exactly these halfwords
(`code_run`), whatever the order it computes them in. They represent the coefficients of the NTT
(`rep_fw`), within bounds that keep every sum in range.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Ntt16.Forward

open VG VG.AArch64 VG.Impl.MlKem.AArch64.Ntt16 VG.Impl.MlKem.AArch64.Ntt16.Forward VG.Proof.MlKem.AArch64.Ntt16
open VG.Spec.MlKem (Poly Zq)

/-- Coefficient `i` after the first `l` layers, of the coefficients `F`. -/
def fw (F : Nat → BitVec 16) : Nat → Nat → BitVec 16
  | 0, i => F i
  | l + 1, i =>
    if i % (2 * (128 >>> l)) < 128 >>> l then
      fw F l i + red (fw F l (i + 128 >>> l)) (zB (2 ^ l + i / (2 * (128 >>> l)))) (tB (2 ^ l + i / (2 * (128 >>> l))))
    else
      fw F l (i - 128 >>> l) - red (fw F l i) (zB (2 ^ l + i / (2 * (128 >>> l)))) (tB (2 ^ l + i / (2 * (128 >>> l))))

/-- Value `256 l + i`: coefficient `i` after `l` layers, or its least residue at the end, for `l = 8`. -/
def value (F : Nat → BitVec 16) (n : Nat) : BitVec 16 :=
  if n / 256 ≤ 7 then fw F (n / 256) (n % 256) else canon (fw F 7 (n % 256))

/-- The values `u` and `v` are the inputs of a butterfly. -/
def pairOk (u v : Nat) : Bool :=
  let l := u / 256
  let i := u % 256
  Nat.blt l 7 && Nat.beq v (u + 128 >>> l) && Nat.blt (i % (2 * (128 >>> l))) (128 >>> l)

/-- `z` and `t` are the multiplier of the butterfly of `u`. -/
def mulOk (u z t : Nat) : Bool :=
  let l := u / 256
  let k := 2 ^ l + u % 256 / (2 * (128 >>> l))
  Nat.beq z (cen (Impl.MlKem.AArch64.Ntt16.zeta k)) && Nat.beq t (quo (Impl.MlKem.AArch64.Ntt16.zeta k))

/-- A butterfly. -/
def bfly (us vs zs ts : List Nat) : Bool := all3 (fun u v _ => pairOk u v) 8 us vs vs && all3 mulOk 8 us zs ts

def dir : Dir where
  add a b := match a, b with
    | .coef us, .prod vs zs ts => if bfly us vs zs ts then some (.coef (next 256 us)) else none
    | _, _ => none
  sub a b := match a, b with
    | .coef us, .prod vs zs ts => if bfly us vs zs ts then some (.coef (next 256 vs)) else none
    | _, _ => none
  prod ns zs ts := some (.prod ns zs ts)
  canon ns := if all3 (fun n _ _ => Nat.beq (n / 256) 7) 8 ns ns ns then some (.coef (next 256 ns)) else none

/-! ## The values -/

/-- What the lower output of a butterfly of layer `l` is. -/
theorem lower_facts {l i : Nat} (hl : l < 7) (hi : i % (2 * (128 >>> l)) < 128 >>> l) (h : i < 256) :
    i + 128 >>> l < 256 ∧ ¬ (i + 128 >>> l) % (2 * (128 >>> l)) < 128 >>> l ∧
      (i + 128 >>> l) / (2 * (128 >>> l)) = i / (2 * (128 >>> l)) ∧ 2 ^ l + i / (2 * (128 >>> l)) < 128 := by
  match l, hl with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ =>
    simp only [Nat.reduceShiftRight, Nat.reduceMul, Nat.reducePow] at hi ⊢
    refine ⟨?_, ?_, ?_, ?_⟩ <;> omega_using [hi, h]
  | _ + 7, h => exact absurd h (by omega_using [])

theorem pairOk_spec {u v : Nat} (h : pairOk u v = true) :
    u / 256 < 7 ∧ u % 256 % (2 * (128 >>> (u / 256))) < 128 >>> (u / 256) ∧ v / 256 = u / 256 ∧
      v % 256 = u % 256 + 128 >>> (u / 256) := by
  simp only [pairOk, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have h2 := Nat.eq_of_beq_eq_true h2
  have := (lower_facts h1 h3 (Nat.mod_lt _ (by decide))).1
  generalize 128 >>> (u / 256) = d at *
  refine ⟨h1, h3, ?_, ?_⟩ <;> omega_using [h2, this]

theorem bfly_value {us vs zs ts : List Nat} (h : bfly us vs zs ts = true) (F : Nat → BitVec 16) {e : Nat} (he : e < 8) :
    value F (us.getD e 0 + 256) = value F (us.getD e 0) + red (value F (vs.getD e 0)) (cst zs e) (cst ts e) ∧
      value F (vs.getD e 0 + 256) = value F (us.getD e 0) - red (value F (vs.getD e 0)) (cst zs e) (cst ts e) := by
  simp only [bfly, Bool.and_eq_true] at h
  have hm := all3_get h.2 e he
  have hp := pairOk_spec (all3_get h.1 e he)
  simp only [mulOk, Bool.and_eq_true] at hm
  simp only [cst, Nat.eq_of_beq_eq_true hm.1, Nat.eq_of_beq_eq_true hm.2]
  clear hm h
  generalize us.getD e 0 = u at *
  generalize vs.getD e 0 = v at *
  obtain ⟨h1, h2, h3, h4⟩ := hp
  obtain ⟨f1, f2, f3, f4⟩ := lower_facts h1 h2 (Nat.mod_lt _ (by decide))
  simp only [value, show (u + 256) / 256 = u / 256 + 1 by omega_using [], show (u + 256) % 256 = u % 256 by omega_using [],
    show (v + 256) / 256 = u / 256 + 1 by omega_using [h3], show (v + 256) % 256 = v % 256 by omega_using [], h3, h4]
  simp only [show u / 256 + 1 ≤ 7 by omega_using [h1], show u / 256 ≤ 7 by omega_using [h1], ↓reduceIte]
  constructor
  · rw [fw, ite_eq_left h2, zB, tB]
  · rw [fw, ite_eq_right f2, f3, Nat.add_sub_cancel, zB, tB]

theorem dir_sound (F : Nat → BitVec 16) : dir.Sound (value F) where
  add := by
    intro a b c h e he
    simp only [dir] at h
    split at h
    · split at h
      · rename_i us vs zs ts hb
        cases h
        have hl := (all3_length (Bool.and_eq_true _ _ ▸ hb : _ ∧ _).1).1
        simp only [Val.lane]
        rw [getD_next (by omega_using [hl, he]), (bfly_value hb F he).1]
      · cases h
    · cases h
  sub := by
    intro a b c h e he
    simp only [dir] at h
    split at h
    · split at h
      · rename_i us vs zs ts hb
        cases h
        have hl := (all3_length (Bool.and_eq_true _ _ ▸ hb : _ ∧ _).1).2
        simp only [Val.lane]
        rw [getD_next (by omega_using [hl, he]), (bfly_value hb F he).2]
      · cases h
    · cases h
  prod := by
    intro ns zs ts c h e he
    simp only [dir] at h
    cases h
    rfl
  canon := by
    intro ns c h e he
    simp only [dir] at h
    split at h
    · rename_i hb
      cases h
      have hl := (all3_length hb).1
      have hn := Nat.eq_of_beq_eq_true (all3_get hb e he)
      simp only [Val.lane]
      rw [getD_next (by omega_using [hl, he])]
      generalize ns.getD e 0 = n at hn
      simp only [value, show (n + 256) / 256 = 8 by omega_using [hn], show (n + 256) % 256 = n % 256 by omega_using [], hn,
        Nat.reduceLeDiff, ↓reduceIte, canon]
    · cases h

/-! ## The code -/

/-- The state before the code. -/
def start : St := ⟨List.replicate 32 none, (List.range 32).map fun i => (List.range 8).map fun e => 8 * i + e⟩

/-- The polynomial after it. -/
def final : List (List Nat) := (List.range 32).map fun i => (List.range 8).map fun e => 2048 + 8 * i + e

theorem code_run : ((run dir fwdRows.lit body start).map fun a => decide (a.mem = final)) = some true := by
  lit_decide

/-! ## What the values represent -/

/-- The coefficients after `l` layers represent those of the NTT, and are at most `3328 (l + 1)`. -/
theorem rep_fw {F : Nat → BitVec 16} {P : Poly} (hF : ∀ i < 256, (F i).toNat = (P[i]!).val) :
    ∀ l ≤ 7, ∀ i < 256, Rep (fw F l i) (nttL l P)[i]! (-(3328 * (l + 1))) (3328 * (l + 1))
  | 0, _, i, hi => by
    have h := hF i hi
    have hl := val_lt_int (P[i]!)
    have := BitVec.toInt_eq_toNat_cond (F i)
    rw [ite_eq_left (by omega_using [h, hl])] at this
    refine ⟨?_, ?_, ?_⟩ <;> simp only [fw, nttL_zero] <;> omega_using [this, h, hl]
  | l + 1, hl, i, hi => by
    have ih := rep_fw hF l (by omega_using [hl])
    have hl' : l < 7 := by omega_using [hl]
    have hlen : 0 < 128 >>> l ∧ 2 * (128 >>> l) * (128 / (128 >>> l)) = 256 ∧ 128 / (128 >>> l) = 2 ^ l := by
      match l, hl' with
      | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ => decide
      | _ + 7, h => exact absurd h (by omega_using [])
    have hb : (3328 * ((l : Int) + 1)) + 3328 < 32768 := by omega_using [hl']
    rw [nttL_succ P hl', nttLayer_get _ hlen.1 hlen.2.1 hi, hlen.2.2, fw]
    by_cases c : i % (2 * (128 >>> l)) < 128 >>> l
    · rw [ite_eq_left c, ite_eq_left c]
      obtain ⟨f1, _, _, f4⟩ := lower_facts hl' c hi
      exact ((ih i hi).add (rep_red (ih _ f1).mod (isMul f4)) (by omega_using [hb]) hb).mono (by push_cast; omega_using []) (by push_cast; omega_using [])
    · rw [ite_eq_right c, ite_eq_right c]
      have f : i - 128 >>> l < 256 ∧ 2 ^ l + i / (2 * (128 >>> l)) < 128 := by
        match l, hl' with
        | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ =>
          simp only [Nat.reduceShiftRight, Nat.reduceMul, Nat.reducePow]
          constructor <;> omega_using [hi]
        | _ + 7, h => exact absurd h (by omega_using [])
      exact ((ih _ f.1).sub (rep_red (ih i hi).mod (isMul f.2)) (by omega_using [hb]) (by omega_using [hb])).mono (by push_cast; omega_using []) (by push_cast; omega_using [])

/-- The values that the code leaves are the coefficients of the NTT. -/
theorem value_final {F : Nat → BitVec 16} {P : Poly} (hF : ∀ i < 256, (F i).toNat = (P[i]!).val) {i : Nat}
    (hi : i < 256) : (value F (2048 + i)).toNat = ((Spec.MlKem.ntt P)[i]!).val := by
  rw [value, ite_eq_right (by omega_using [hi]), show (2048 + i) % 256 = i by omega_using [hi], ntt_eq_nttL]
  exact canon_toNat (rep_fw hF 7 (by decide) i hi) (by decide) (by decide)

end VG.Proof.MlKem.AArch64.Ntt16.Forward
