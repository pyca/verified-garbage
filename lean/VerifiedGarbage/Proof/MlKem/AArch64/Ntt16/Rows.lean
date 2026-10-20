module

public import VerifiedGarbage.Proof.MlKem.NttLayer
import VerifiedGarbage.Proof.MlKem.AArch64.Barrett
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Vec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Taint

/-!
# ML-KEM's 16-bit NTT on AArch64: the butterflies on rows

Pass 1 of the 16-bit NTT keeps eight rows of a chunk in `v0`–`v7`, row `r`
holding the coefficients `32r + 8c + e` of chunk `c` after the first
`lay[r]` layers (`Rows`). A butterfly on rows `a` and `b` advances both by a
layer (`rows_bf`) when the pair is one of that layer (`okPair`, which
`decide` checks for the pairs of the code); `bfRows` is a list of them with
one zeta (`rows_bfRows`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Ntt16

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem VG.Spec.MlKem
open Impl.MlKem.AArch64.Ntt16

/-! ## Zetas -/

theorem ofNat_zeta {k : Nat} (hk : k < 128) : ofNat (Impl.MlKem.AArch64.Ntt16.zeta k) = VG.Proof.MlKem.zeta k := by
  rw [VG.Proof.MlKem.zeta_eq hk, Impl.MlKem.AArch64.Ntt16.zeta, zetaTable_eq]

theorem zeta_lt {k : Nat} (hk : k < 128) : Impl.MlKem.AArch64.Ntt16.zeta k < 3329 := by
  have := zetaTable_lt k hk
  exact this

/-! ## Rows -/

theorem row_inj : ∀ r < 8, ∀ a < 8, row r = row a → r = a := by decide

/-- Rows `r < n` of chunk `c` after `lay[r]` layers of `NTT`. -/
def Rows (P : Poly) (c : Nat) (lay : List Nat) (n : Nat) (s : State) : Prop :=
  ∀ r < n, Rep (s.v (row r)) (fun e => (nttL (lay.getD r 0) P)[32 * r + 8 * c + e]!)
    ((lay.getD r 0 + 1) * 3329)

/-- The pair of rows `a`, `b` is one of the butterflies of the layer after `lay[a]`, with
the zeta `K`. -/
def okPair (lay : List Nat) (a b K : Nat) : Bool :=
  let j := lay.getD a 0
  let len := 128 >>> j
  a < 8 && b < 8 && a < lay.length && b < lay.length && a != b && lay.getD b 0 == j && j < 7 &&
    K < 128 && (List.range 32).all fun t =>
      decide ((32 * a + t) % (2 * len) < len) && 32 * a + t + len == 32 * b + t &&
      128 / len + (32 * a + t) / (2 * len) == K && !decide ((32 * b + t) % (2 * len) < len) &&
      (32 * b + t) / (2 * len) == (32 * a + t) / (2 * len) && 32 * b + t < 256

/-- `lay` after the butterflies on rows `a` and `b`. -/
def layStep (lay : List Nat) (a b : Nat) : List Nat :=
  (lay.set a (lay.getD a 0 + 1)).set b (lay.getD a 0 + 1)

theorem getD_layStep {lay : List Nat} {a b : Nat} (ha : a < lay.length) (hb : b < lay.length) (r : Nat) :
    (layStep lay a b).getD r 0 = if r = a ∨ r = b then lay.getD a 0 + 1 else lay.getD r 0 := by
  simp only [layStep, List.getD_eq_getElem?_getD, List.getElem?_set, List.length_set]
  by_cases h1 : b = r
  · subst h1; simp [hb]
  · by_cases h2 : a = r
    · subst h2; simp [ha, h1]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

theorem length_layStep (lay : List Nat) (a b : Nat) : (layStep lay a b).length = lay.length := by
  simp [layStep]

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

/-- The rows' registers are none of the scratch registers. -/
theorem row_ne {r : Nat} (hr : r < 8) :
    row r ≠ .v16 ∧ row r ≠ .v17 ∧ row r ≠ .v22 ∧ row r ≠ .v23 ∧ row r ≠ .v31 ∧ row r ≠ .v18 ∧
      row r ≠ .v19 ∧ row r ≠ .v20 ∧ row r ≠ .v21 ∧ row r ≠ .v29 ∧ row r ≠ .v30 := by
  match r, hr with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => decide

/-- The registers pass 1 changes. -/
abbrev p1Regs : List VReg := [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v20, .v21, .v22, .v23]

/-- The registers butterflies on rows change. -/
abbrev bfRegs : List VReg := [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17]

theorem row_mem {r : Nat} (hr : r < 8) : row r ∈ bfRegs := by
  match r, hr with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => decide

/-- The butterflies on rows `a` and `b`. -/
theorem rows_bf {P : Poly} {c : Nat} (hc : c < 4) {lay : List Nat} {a b K : Nat}
    (hok : okPair lay a b K = true) (h : Rows P c lay 8 s)
    (hz : Cst (s.v .v22) fun _ => Impl.MlKem.AArch64.Ntt16.zeta K)
    (ht : Cst (s.v .v23) fun _ => tw (Impl.MlKem.AArch64.Ntt16.zeta K))
    (hq : Cst (s.v .v31) fun _ => 3329)
    (k : ∀ s', VChg bfRegs s s' → Rows P c (layStep lay a b) 8 s' → WP isa (.block rest) s' Q) :
    WP isa (.block (bf (row a) (row b) .v22 .v23 ++ rest)) s Q := by
  simp only [okPair, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq,
    List.all_eq_true, List.mem_range, Bool.not_eq_true', decide_eq_false_iff_not, and_assoc] at hok
  obtain ⟨ha, hb, hal, hbl, hab, hjb, hj, hK, ht32⟩ := hok
  generalize hJ : lay.getD a 0 = j at hjb hj ht32
  have na := row_ne ha
  have nb := row_ne hb
  have hrab : row a ≠ row b := fun e => hab (row_inj a ha b hb e)
  have hZ : ∀ e < 8, Impl.MlKem.AArch64.Ntt16.zeta K < 3329 := fun _ _ => zeta_lt hK
  have hx := h a ha
  have hy := h b hb
  rw [hJ] at hx
  rw [hjb] at hy
  have hB1 : (j + 1) * 3329 + 3329 ≤ 32768 := by omega_using [hj]
  have hB2 : (j + 1) * 3329 ≤ 32768 := by omega_using [hj]
  refine bf_ok hrab na.1 na.2.1 nb.1 (by decide) hx hy hz ht hq hZ hB1 hB2 fun s' hc' hx' hy' => k s' (hc'.mono fun r hr => ?_) fun r hr => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · exact row_mem hb
    · exact row_mem ha
  · rw [getD_layStep hal hbl, hJ]
    by_cases e1 : r = a
    · subst e1
      rw [ite_eq_left (Or.inl rfl), show (j + 1 + 1) * 3329 = (j + 1) * 3329 + 3329 by
        rw [Nat.succ_mul]]
      refine hx'.congr fun e he => ?_
      obtain ⟨c1, c2, c3, -, -, c6⟩ := ht32 (8 * c + e) (by omega)
      simp only [← Nat.add_assoc] at c1 c2 c3 c6
      rw [nttL_succ_get P hj (by omega), ite_eq_left c1, c3, ← ofNat_zeta hK, c2]
    · by_cases e2 : r = b
      · subst e2
        rw [ite_eq_left (Or.inr rfl), show (j + 1 + 1) * 3329 = (j + 1) * 3329 + 3329 by
          rw [Nat.succ_mul]]
        refine hy'.congr fun e he => ?_
        obtain ⟨c1, c2, c3, c4, c5, c6⟩ := ht32 (8 * c + e) (by omega)
        simp only [← Nat.add_assoc] at c1 c2 c3 c4 c5 c6
        rw [nttL_succ_get P hj (by omega), ite_eq_right c4, c5, c3, ← ofNat_zeta hK,
          show 32 * r + 8 * c + e - (128 >>> j) = 32 * a + 8 * c + e by omega]
      · rw [ite_eq_right (by omega), hc'.get _ ?_]
        · exact h r hr
        · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          have nr := row_ne hr
          exact ⟨nr.1, nr.2.1, nr.1, fun e => e2 (row_inj r hr b hb e),
            fun e => e1 (row_inj r hr a ha e)⟩

/-- Pairs of rows, each one of the butterflies of the layer after `lay`, with the zeta `K`. -/
def okPairs (lay : List Nat) (K : Nat) : List (Nat × Nat) → Bool
  | [] => true
  | (a, b) :: ps => okPair lay a b K && okPairs (layStep lay a b) K ps

/-- `lay` after the butterflies on the pairs `ps`. -/
def layAfter (lay : List Nat) : List (Nat × Nat) → List Nat
  | [] => lay
  | (a, b) :: ps => layAfter (layStep lay a b) ps

theorem rows_bfs {P : Poly} {c : Nat} (hc : c < 4) {K : Nat} (ps : List (Nat × Nat)) :
    ∀ (lay : List Nat) (s : State), okPairs lay K ps = true → Rows P c lay 8 s →
    (Cst (s.v .v22) fun _ => Impl.MlKem.AArch64.Ntt16.zeta K) →
    (Cst (s.v .v23) fun _ => tw (Impl.MlKem.AArch64.Ntt16.zeta K)) →
    (Cst (s.v .v31) fun _ => 3329) →
    (∀ s', VChg bfRegs s s' → Rows P c (layAfter lay ps) 8 s' → WP isa (.block rest) s' Q) →
    WP isa (.block ((ps.flatMap fun p => bf (row p.1) (row p.2) .v22 .v23) ++ rest)) s Q := by
  induction ps with
  | nil => intro lay s _ h _ _ _ k; exact k s (VChg.refl _ _) h
  | cons p ps ih =>
    intro lay s hok h hz ht hq k
    obtain ⟨a, b⟩ := p
    simp only [okPairs, Bool.and_eq_true] at hok
    rw [List.flatMap_cons, List.append_assoc]
    refine rows_bf hc hok.1 h hz ht hq fun s₁ c₁ h₁ => ?_
    have g22 : s₁.v .v22 = s.v .v22 := c₁.get .v22
    have g23 : s₁.v .v23 = s.v .v23 := c₁.get .v23
    have g31 : s₁.v .v31 = s.v .v31 := c₁.get .v31
    refine ih _ s₁ hok.2 h₁ (by rw [g22]; exact hz) (by rw [g23]; exact ht) (by rw [g31]; exact hq)
      fun s₂ c₂ h₂ => k s₂ ((c₁.trans c₂).mono fun r hr => ?_) h₂
    simp only [List.mem_append] at hr
    exact hr.elim id id

theorem eval_dupE {s : State} {d n : VReg} {k : Nat} (hk : k < 8) :
    VOp.eval s (.dupE .h8 d n k) = some (d, ofVHalves fun _ => vhalf (s.v n) k) := by
  simp only [VOp.eval, VArr.esize, show k < 128 / 16 from hk, ite_true, VArr.map2]
  rfl

/-- `bfRows k ps`: the pairs `ps` with lane `k` of `v18` and `v19`. -/
theorem rows_bfRows {P : Poly} {c : Nat} (hc : c < 4) {K k : Nat} (hk : k < 8) (ps : List (Nat × Nat))
    {lay lay' : List Nat} (hok : okPairs lay K ps = true) (hlay : layAfter lay ps = lay')
    (h : Rows P c lay 8 s)
    (hz : vhalf (s.v .v18) k = BitVec.ofNat 16 (Impl.MlKem.AArch64.Ntt16.zeta K))
    (ht : vhalf (s.v .v19) k = BitVec.ofNat 16 (tw (Impl.MlKem.AArch64.Ntt16.zeta K)))
    (hq : Cst (s.v .v31) fun _ => 3329)
    (kk : ∀ s', VChg (.v22 :: .v23 :: bfRegs) s s' → Rows P c lay' 8 s' →
      WP isa (.block rest) s' Q) :
    WP isa (.block (bfRows k ps ++ rest)) s Q := by
  simp only [bfRows, List.cons_append, List.nil_append]
  refine wp_vop (eval_dupE hk) fun s₁ h₁ => wp_vop (eval_dupE hk) fun s₂ h₂ => ?_
  refine rows_bfs hc ps lay s₂ hok (fun r hr => ?_) (fun e he => ?_) (fun e he => ?_) (fun e he => ?_)
    fun s₃ c₃ h₃ => kk s₃ ((h₁.chg.trans h₂.chg).trans c₃ |>.mono) (hlay ▸ h₃)
  · have nr := row_ne hr
    rw [h₂.get _ nr.2.2.2.1, h₁.get _ nr.2.2.1]; exact h r hr
  · rw [h₂.get .v22, h₁.v, vhalf_ofVHalves _ he, hz]
  · rw [h₂.v, vhalf_ofVHalves _ he, h₁.get .v19, ht]
  · rw [h₂.get .v31, h₁.get .v31]; exact hq e he

end

end VG.Proof.MlKem.AArch64.Ntt16
