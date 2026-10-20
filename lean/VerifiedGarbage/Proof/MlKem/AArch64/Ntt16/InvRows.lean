module

public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Rows
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Gs
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Taint

/-!
# ML-KEM's 16-bit inverse NTT on AArch64: the butterflies on rows

Pass 2 of the inverse keeps the eight rows of a chunk in `v0`–`v7`: row `r`
holds coefficients `32r + 8c + e` after `lay[r]` layers of `NTT⁻¹`, less
than `bnd[r]` in absolute value (`RowsI`). An inverse butterfly on rows `a`
and `b` advances both by a layer (`rowsI_gs`) when the pair is one of the
layer's (`okPairI`, checked by `decide`); `gsRows` (`rowsI_gsRows`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Ntt16

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem VG.Spec.MlKem
open Impl.MlKem.AArch64.Ntt16

/-- Rows `r < n` of chunk `c` after `lay[r]` layers of `NTT⁻¹`, less than `bnd[r]`. -/
def RowsI (P : Poly) (c : Nat) (lay bnd : List Nat) (n : Nat) (s : State) : Prop :=
  ∀ r < n, Rep (s.v (row r)) (fun e => (nttInvL (lay.getD r 0) P)[32 * r + 8 * c + e]!) (bnd.getD r 0)

/-- The pair of rows `a`, `b` is one of the inverse butterflies of the layer after `lay[a]`,
with the zeta `K`. -/
def okPairI (lay bnd : List Nat) (a b K : Nat) : Bool :=
  let j := lay.getD a 0
  let len := 2 <<< j
  a < 8 && b < 8 && a < lay.length && b < lay.length && a < bnd.length && b < bnd.length &&
    a != b && lay.getD b 0 == j && j < 7 && K < 128 && bnd.getD a 0 + bnd.getD b 0 ≤ 32768 &&
    (List.range 32).all fun t =>
      decide ((32 * a + t) % (2 * len) < len) && 32 * a + t + len == 32 * b + t &&
      256 / len - 1 - (32 * a + t) / (2 * len) == K && !decide ((32 * b + t) % (2 * len) < len) &&
      (32 * b + t) / (2 * len) == (32 * a + t) / (2 * len) && 32 * b + t < 256

/-- `lay` and `bnd` after the inverse butterflies on rows `a` and `b`. -/
def layStepI (lay : List Nat) (a b : Nat) : List Nat :=
  (lay.set a (lay.getD a 0 + 1)).set b (lay.getD a 0 + 1)

def bndStepI (bnd : List Nat) (a b : Nat) : List Nat :=
  (bnd.set a (bnd.getD a 0 + bnd.getD b 0)).set b 3329

theorem getD_set2 {l : List Nat} {a b : Nat} (ha : a < l.length) (hb : b < l.length)
    (x y : Nat) (r : Nat) :
    ((l.set a x).set b y).getD r 0 = if r = b then y else if r = a then x else l.getD r 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set, List.length_set]
  by_cases h1 : b = r
  · subst h1; simp [hb]
  · by_cases h2 : a = r
    · subst h2; simp [ha, h1, Ne.symm h1]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

theorem rowsI_gs {P : Poly} {c : Nat} (hc : c < 4) {lay bnd : List Nat} {a b K : Nat}
    (hok : okPairI lay bnd a b K = true) (h : RowsI P c lay bnd 8 s)
    (hz : Cst (s.v .v22) fun _ => Impl.MlKem.AArch64.Ntt16.zeta K)
    (ht : Cst (s.v .v23) fun _ => tw (Impl.MlKem.AArch64.Ntt16.zeta K))
    (hq : Cst (s.v .v31) fun _ => 3329)
    (k : ∀ s', VChg bfRegs s s' → RowsI P c (layStepI lay a b) (bndStepI bnd a b) 8 s' →
      WP isa (.block rest) s' Q) :
    WP isa (.block (gs (row a) (row b) .v22 .v23 ++ rest)) s Q := by
  simp only [okPairI, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq,
    List.all_eq_true, List.mem_range, Bool.not_eq_true', decide_eq_false_iff_not, and_assoc] at hok
  obtain ⟨ha, hb, hal, hbl, hal', hbl', hab, hjb, hj, hK, hB, ht32⟩ := hok
  generalize hJ : lay.getD a 0 = j at hjb hj ht32
  have na := row_ne ha
  have nb := row_ne hb
  have hrab : row a ≠ row b := fun e => hab (row_inj a ha b hb e)
  have hx := h a ha
  have hy := h b hb
  rw [hJ] at hx
  rw [hjb] at hy
  refine gs_ok hrab na.2.1 nb.2.1 (Ne.symm na.2.2.1) (by decide) (Ne.symm na.2.2.2.1)
    (Ne.symm nb.2.2.2.1) (by decide) (Ne.symm na.2.2.2.2.1) (Ne.symm nb.2.2.2.2.1) hx hy hz ht hq
    (fun _ _ => zeta_lt hK) hB fun s' hc' hx' hy' => k s' (hc'.mono fun r hr => ?_) fun r hr => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · exact row_mem ha
    · exact row_mem hb
    · decide
    · exact row_mem hb
  · rw [layStepI, bndStepI, getD_set2 hal hbl, getD_set2 hal' hbl', hJ]
    by_cases e2 : r = b
    · subst e2
      rw [ite_eq_left rfl, ite_eq_left rfl]
      refine hy'.congr fun e he => ?_
      obtain ⟨c1, c2, c3, c4, c5, c6⟩ := ht32 (8 * c + e) (by omega)
      simp only [← Nat.add_assoc] at c1 c2 c3 c4 c5 c6
      rw [nttInvL_succ_get P hj (by omega), ite_eq_right c4, c5, c3, ← ofNat_zeta hK,
        show 32 * r + 8 * c + e - (2 <<< j) = 32 * a + 8 * c + e by omega]
    · rw [ite_eq_right e2, ite_eq_right e2]
      by_cases e1 : r = a
      · subst e1
        rw [ite_eq_left rfl, ite_eq_left rfl]
        refine hx'.congr fun e he => ?_
        obtain ⟨c1, c2, -, -, -, -⟩ := ht32 (8 * c + e) (by omega)
        simp only [← Nat.add_assoc] at c1 c2
        rw [nttInvL_succ_get P hj (by omega), ite_eq_left c1, c2]
      · rw [ite_eq_right e1, ite_eq_right e1, hc'.get _ ?_]
        · exact h r hr
        · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          have nr := row_ne hr
          exact ⟨nr.2.1, fun e => e1 (row_inj r hr a ha e), fun e => e2 (row_inj r hr b hb e), nr.2.1,
            fun e => e2 (row_inj r hr b hb e)⟩

/-- Pairs of rows for inverse butterflies with the zeta `K`, and the rows' layers and bounds
after them. -/
def okPairsI (lay bnd : List Nat) (K : Nat) : List (Nat × Nat) → Bool
  | [] => true
  | (a, b) :: ps => okPairI lay bnd a b K && okPairsI (layStepI lay a b) (bndStepI bnd a b) K ps

def layAfterI (lay bnd : List Nat) : List (Nat × Nat) → List Nat × List Nat
  | [] => (lay, bnd)
  | (a, b) :: ps => layAfterI (layStepI lay a b) (bndStepI bnd a b) ps

theorem rowsI_gss {P : Poly} {c : Nat} (hc : c < 4) {K : Nat} (ps : List (Nat × Nat)) :
    ∀ (lay bnd : List Nat) (s : State), okPairsI lay bnd K ps = true → RowsI P c lay bnd 8 s →
    (Cst (s.v .v22) fun _ => Impl.MlKem.AArch64.Ntt16.zeta K) →
    (Cst (s.v .v23) fun _ => tw (Impl.MlKem.AArch64.Ntt16.zeta K)) →
    (Cst (s.v .v31) fun _ => 3329) →
    (∀ s', VChg bfRegs s s' → RowsI P c (layAfterI lay bnd ps).1 (layAfterI lay bnd ps).2 8 s' →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((ps.flatMap fun p => gs (row p.1) (row p.2) .v22 .v23) ++ rest)) s Q := by
  induction ps with
  | nil => intro lay bnd s _ h _ _ _ k; exact k s (VChg.refl _ _) h
  | cons p ps ih =>
    intro lay bnd s hok h hz ht hq k
    obtain ⟨a, b⟩ := p
    simp only [okPairsI, Bool.and_eq_true] at hok
    rw [List.flatMap_cons, List.append_assoc]
    refine rowsI_gs hc hok.1 h hz ht hq fun s₁ c₁ h₁ => ?_
    refine ih _ _ s₁ hok.2 h₁ (by rw [c₁.get .v22]; exact hz) (by rw [c₁.get .v23]; exact ht)
      (by rw [c₁.get .v31]; exact hq) fun s₂ c₂ h₂ => k s₂ ((c₁.trans c₂).mono fun r hr => ?_) h₂
    simp only [List.mem_append] at hr
    exact hr.elim id id

/-- `gsRows k ps`: the pairs `ps` with lane `k` of `v18` and `v19`. -/
theorem rowsI_gsRows {P : Poly} {c : Nat} (hc : c < 4) {K k : Nat} (hk : k < 8) (ps : List (Nat × Nat))
    {lay bnd lay' bnd' : List Nat} (hok : okPairsI lay bnd K ps = true)
    (hlay : layAfterI lay bnd ps = (lay', bnd')) (h : RowsI P c lay bnd 8 s)
    (hz : vhalf (s.v .v18) k = BitVec.ofNat 16 (Impl.MlKem.AArch64.Ntt16.zeta K))
    (ht : vhalf (s.v .v19) k = BitVec.ofNat 16 (tw (Impl.MlKem.AArch64.Ntt16.zeta K)))
    (hq : Cst (s.v .v31) fun _ => 3329)
    (kk : ∀ s', VChg (.v22 :: .v23 :: bfRegs) s s' → RowsI P c lay' bnd' 8 s' →
      WP isa (.block rest) s' Q) :
    WP isa (.block (gsRows k ps ++ rest)) s Q := by
  simp only [gsRows, List.cons_append, List.nil_append]
  refine wp_vop (eval_dupE hk) fun s₁ h₁ => wp_vop (eval_dupE hk) fun s₂ h₂ => ?_
  refine rowsI_gss hc ps lay bnd s₂ hok (fun r hr => ?_) (fun e he => ?_) (fun e he => ?_)
    (fun e he => ?_) fun s₃ c₃ h₃ => kk s₃ ((h₁.chg.trans h₂.chg).trans c₃ |>.mono) (by
      rw [hlay] at h₃; exact h₃)
  · have nr := row_ne hr
    rw [h₂.get _ nr.2.2.2.1, h₁.get _ nr.2.2.1]; exact h r hr
  · rw [h₂.get .v22, h₁.v, vhalf_ofVHalves _ he, hz]
  · rw [h₂.v, vhalf_ofVHalves _ he, h₁.get .v19, ht]
  · rw [h₂.get .v31, h₁.get .v31]; exact hq e he

end

end VG.Proof.MlKem.AArch64.Ntt16
