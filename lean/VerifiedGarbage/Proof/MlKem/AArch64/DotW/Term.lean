module

public import VerifiedGarbage.Proof.MlKem.AArch64.DotW.Lane

/-!
# ML-KEM's fused dot product of polynomials stored with 16 bits, on AArch64: a term

`termW fg` (the pointers of `dot`, its loads, `gatherW` and `accumulateW`)
adds the products of the eight pairs of 16 coefficients of `F` and `G` to
the sums of pairs `0 … 3` (`v21`–`v23`, as `dot`) and `4 … 7` (`v25`–`v27`):
`fullTermW_ok`.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.DotW

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem
open VG.Proof.MlKem.AArch64.Dot

def gatherW : List Instr :=
  [.vop (.perm .uzp1 .h8 .v6 .v0 .v1), .vop (.perm .uzp2 .h8 .v7 .v0 .v1),
   .vop (.perm .uzp1 .h8 .v19 .v4 .v5), .vop (.perm .uzp2 .h8 .v20 .v4 .v5)]

def accumulateW : List Instr :=
  [.vop (.umlalH false .v21 .v6 .v19), .vop (.umlalH true .v25 .v6 .v19),
   .vop (.umlalH false .v22 .v7 .v20), .vop (.umlalH true .v26 .v7 .v20),
   .vop (.umlalH false .v23 .v6 .v20), .vop (.umlalH true .v27 .v6 .v20),
   .vop (.umlalH false .v23 .v7 .v19), .vop (.umlalH true .v27 .v7 .v19)]

theorem termW_partition (fg : Nat × Nat) :
    Impl.MlKem.AArch64.DotW.termW fg = pointers fg ++ (loads ++ gatherW ++ accumulateW) := by
  simp only [Impl.MlKem.AArch64.DotW.termW, pointers, loads, gatherW, accumulateW,
    List.append_assoc, List.cons_append, List.nil_append]

/-- The sums of pairs `0 … 3` (`lo`, as `dot`'s `Accum`) and `4 … 7` (`hi`). -/
def AccumW (s : State) (lo hi : Nat → Sums) : Prop :=
  Accum s lo ∧ Lanes (s.v .v25) (fun e => (hi e).even) ∧
    Lanes (s.v .v26) (fun e => (hi e).odd) ∧ Lanes (s.v .v27) (fun e => (hi e).cross)

section
variable {rest : List Instr} {Q : State → Prop}

theorem gatherW_ok {s : State} {F G : Nat → Nat}
    (f0 : HLanes (s.v .v0) F) (f1 : HLanes (s.v .v1) (fun e => F (8 + e)))
    (g0 : HLanes (s.v .v4) G) (g1 : HLanes (s.v .v5) (fun e => G (8 + e)))
    (k : ∀ s', VChg [.v6, .v7, .v19, .v20] s s' →
      HLanes (s'.v .v6) (fun e => F (2 * e)) → HLanes (s'.v .v7) (fun e => F (2 * e + 1)) →
      HLanes (s'.v .v19) (fun e => G (2 * e)) → HLanes (s'.v .v20) (fun e => G (2 * e + 1)) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (gatherW ++ rest)) s Q := by
  simp only [gatherW, List.cons_append, List.nil_append]
  refine wp_vop (d := .v6) rfl fun s₁ h₁ => wp_vop (d := .v7) rfl fun s₂ h₂ =>
    wp_vop (d := .v19) rfl fun s₃ h₃ => wp_vop (d := .v20) rfl fun s₄ h₄ => ?_
  refine k s₄ (((h₁.chg.trans h₂.chg).trans h₃.chg).trans h₄.chg).mono ?_ ?_ ?_ ?_
  · rw [h₄.get .v6, h₃.get .v6, h₂.get .v6, h₁.v]; exact (gatherW_lanes f0 f1).1
  · rw [h₄.get .v7, h₃.get .v7, h₂.v, h₁.get .v0, h₁.get .v1]
    exact (gatherW_lanes f0 f1).2
  · rw [h₄.get .v19, h₃.v, h₂.get .v4, h₂.get .v5, h₁.get .v4, h₁.get .v5]
    exact (gatherW_lanes g0 g1).1
  · rw [h₄.v, h₃.get .v4, h₃.get .v5, h₂.get .v4, h₂.get .v5, h₁.get .v4, h₁.get .v5]
    exact (gatherW_lanes g0 g1).2

theorem accumulateW_ok {s : State} {lo hi : Nat → Sums} {FE FO GE GO : Nat → Nat}
    (ha : AccumW s lo hi)
    (hfe : HLanes (s.v .v6) FE) (hfo : HLanes (s.v .v7) FO)
    (hge : HLanes (s.v .v19) GE) (hgo : HLanes (s.v .v20) GO)
    (blo : ∀ e < 4, ((lo e).next (FE e) (FO e) (GE e) (GO e)).even < 2 ^ 32 ∧
      ((lo e).next (FE e) (FO e) (GE e) (GO e)).odd < 2 ^ 32 ∧
      ((lo e).next (FE e) (FO e) (GE e) (GO e)).cross < 2 ^ 32)
    (bhi : ∀ e < 4, ((hi e).next (FE (4 + e)) (FO (4 + e)) (GE (4 + e)) (GO (4 + e))).even < 2 ^ 32 ∧
      ((hi e).next (FE (4 + e)) (FO (4 + e)) (GE (4 + e)) (GO (4 + e))).odd < 2 ^ 32 ∧
      ((hi e).next (FE (4 + e)) (FO (4 + e)) (GE (4 + e)) (GO (4 + e))).cross < 2 ^ 32)
    (k : ∀ s', VChg [.v21, .v25, .v22, .v26, .v23, .v27] s s' →
      AccumW s' (fun e => (lo e).next (FE e) (FO e) (GE e) (GO e))
        (fun e => (hi e).next (FE (4 + e)) (FO (4 + e)) (GE (4 + e)) (GO (4 + e))) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (accumulateW ++ rest)) s Q := by
  obtain ⟨⟨a21, a22, a23⟩, a25, a26, a27⟩ := ha
  simp only [accumulateW, List.cons_append, List.nil_append]
  simp only [Sums.next] at blo bhi
  refine umlal_ok (hi := false) a21 hfe hge (fun e he => by simpa using (blo e he).1) fun s₁ c₁ l₁ => ?_
  refine umlal_ok (hi := true) (by rw [c₁.get .v25]; exact a25) (by rw [c₁.get .v6]; exact hfe)
    (by rw [c₁.get .v19]; exact hge) (fun e he => by simpa [Nat.add_comm] using (bhi e he).1)
    fun s₂ c₂ l₂ => ?_
  refine umlal_ok (hi := false) (by rw [c₂.get .v22, c₁.get .v22]; exact a22)
    (by rw [c₂.get .v7, c₁.get .v7]; exact hfo) (by rw [c₂.get .v20, c₁.get .v20]; exact hgo)
    (fun e he => by simpa using (blo e he).2.1) fun s₃ c₃ l₃ => ?_
  refine umlal_ok (hi := true) (by rw [c₃.get .v26, c₂.get .v26, c₁.get .v26]; exact a26)
    (by rw [c₃.get .v7, c₂.get .v7, c₁.get .v7]; exact hfo)
    (by rw [c₃.get .v20, c₂.get .v20, c₁.get .v20]; exact hgo)
    (fun e he => by simpa [Nat.add_comm] using (bhi e he).2.1) fun s₄ c₄ l₄ => ?_
  have C₄ := ((c₁.trans c₂).trans c₃).trans c₄
  refine umlal_ok (hi := false) (by rw [C₄.get .v23]; exact a23)
    (by rw [C₄.get .v6]; exact hfe) (by rw [C₄.get .v20]; exact hgo)
    (fun e he => by have := (blo e he).2.2; simp only [Nat.zero_add, Bool.false_eq_true, ite_false]; omega)
    fun s₅ c₅ l₅ => ?_
  refine umlal_ok (hi := true) (by rw [c₅.get .v27, C₄.get .v27]; exact a27)
    (by rw [c₅.get .v6, C₄.get .v6]; exact hfe) (by rw [c₅.get .v20, C₄.get .v20]; exact hgo)
    (fun e he => by have := (bhi e he).2.2; simp only [ite_true, Nat.add_comm 4 e] at this ⊢; omega)
    fun s₆ c₆ l₆ => ?_
  have C₆ := (C₄.trans c₅).trans c₆
  refine umlal_ok (hi := false) (by rw [c₆.get .v23]; exact l₅)
    (by rw [C₆.get .v7]; exact hfo) (by rw [C₆.get .v19]; exact hge)
    (fun e he => by have := (blo e he).2.2; simp only [Nat.zero_add, Bool.false_eq_true, ite_false]; omega)
    fun s₇ c₇ l₇ => ?_
  refine umlal_ok (hi := true) (by rw [c₇.get .v27]; exact l₆)
    (by rw [c₇.get .v7, C₆.get .v7]; exact hfo) (by rw [c₇.get .v19, C₆.get .v19]; exact hge)
    (fun e he => by have := (bhi e he).2.2; simp only [ite_true, Nat.add_comm 4 e] at this ⊢; omega)
    fun s₈ c₈ l₈ => ?_
  have C₈ := (C₆.trans c₇).trans c₈
  refine k s₈ C₈.mono ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [c₈.get .v21, c₇.get .v21, c₆.get .v21, c₅.get .v21, c₄.get .v21, c₃.get .v21, c₂.get .v21]
    exact l₁.congr fun e he => by simp [Sums.next]
  · rw [c₈.get .v22, c₇.get .v22, c₆.get .v22, c₅.get .v22, c₄.get .v22]
    exact l₃.congr fun e he => by simp [Sums.next]
  · rw [c₈.get .v23]
    exact l₇.congr fun e he => by simp [Sums.next]
  · rw [c₈.get .v25, c₇.get .v25, c₆.get .v25, c₅.get .v25, c₄.get .v25, c₃.get .v25]
    exact l₂.congr fun e he => by simp [Sums.next, Nat.add_comm]
  · rw [c₈.get .v26, c₇.get .v26, c₆.get .v26, c₅.get .v26]
    exact l₄.congr fun e he => by simp [Sums.next, Nat.add_comm]
  · exact l₈.congr fun e he => by simp [Sums.next, Nat.add_comm]

end

end VG.Proof.MlKem.AArch64.DotW
