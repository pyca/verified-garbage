module

public import VerifiedGarbage.Proof.MlKem.AArch64.DotW.Lane
public import VerifiedGarbage.Impl.MlKem.AArch64.DotW
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Gather
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Step
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Rc4.AArch64.Vec

/-!
# ML-KEM's fused dot product of polynomials stored with 16 bits, on AArch64: a term

`termW bf bg fg` (pointers to `bf` and `bg` plus the offsets `fg`, the loads of `dot`, `gatherW` and `accumulateW`)
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

/-- `x1` and `x2` to the coefficients of a term: `bf` and `bg` plus its offsets, plus `x12`. -/
def pointersW (bf bg : Reg) (fg : Nat × Nat) : List Instr :=
  Impl.MlKem.AArch64.ptrTo .x1 bf fg.1 ++ Impl.MlKem.AArch64.ptrTo .x2 bg fg.2 ++ [.add .x .x1 .x1 .x12, .add .x .x2 .x2 .x12]

theorem not_mem_x12 {r : Reg} (h : r ∉ clob) : r ∉ [Reg.x1, .x2] := fun e => h (by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at e
  rcases e with rfl | rfl <;> decide)

theorem pointersW_ok {s : State} {bf bg : Reg} {fg : Nat × Nat} (hbf : bf ∉ clob) (hbg : bg ∉ clob)
    (hf : fg.1 < 65536) (hg : fg.2 < 65536) :
    WP isa (.block (pointersW bf bg fg)) s fun s' =>
      Only [.x1, .x2] s s' ∧ s'.v = s.v ∧
      s'.gpr .x1 = s.gpr bf + BitVec.ofNat 64 fg.1 + s.gpr .x12 ∧
      s'.gpr .x2 = s.gpr bg + BitVec.ofNat 64 fg.2 + s.gpr .x12 := by
  have n1 : ∀ r, r ∉ clob → r ≠ .x1 := fun r h e => h (by rw [e]; decide)
  have n2 : ∀ r, r ∉ clob → r ≠ .x2 := fun r h e => h (by rw [e]; decide)
  refine WP.mono (WP.keepV (Q := fun s' => Only [.x1, .x2] s s' ∧
    s'.gpr .x1 = s.gpr bf + BitVec.ofNat 64 fg.1 + s.gpr .x12 ∧
    s'.gpr .x2 = s.gpr bg + BitVec.ofNat 64 fg.2 + s.gpr .x12) ?_ ?_) ?_
  · simp only [pointersW, Impl.MlKem.AArch64.ptrTo]
    split <;> split <;> rfl
  · simp only [pointersW, List.append_assoc]
    refine wp_ptrTo (n1 bf hbf).symm hf fun s₁ h₁ e₁ => wp_ptrTo (n2 bg hbg).symm hg fun s₂ h₂ e₂ =>
      wp_add fun s₃ h₃ e₃ => wp_add fun s₄ h₄ e₄ => wp_nil ?_
    refine ⟨(((h₁.trans h₂).trans h₃).trans h₄).mono, ?_, ?_⟩
    · rw [h₄.get .x1, e₃, h₂.get .x1, e₁, h₂.get .x12, h₁.get .x12]
    · rw [e₄, h₃.get .x2, e₂, h₁.get bg (by simpa using n1 bg hbg), h₃.get .x12, h₂.get .x12,
        h₁.get .x12]
  · intro s' h
    exact ⟨h.1.1, h.2, h.1.2⟩

theorem termW_partition (bf bg : Reg) (fg : Nat × Nat) :
    Impl.MlKem.AArch64.DotW.termW bf bg fg = pointersW bf bg fg ++ (loads ++ gatherW ++ accumulateW) := by
  simp only [Impl.MlKem.AArch64.DotW.termW, pointersW, loads, gatherW, accumulateW,
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

namespace VG.Proof.MlKem.AArch64.DotW

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem
open VG.Proof.MlKem.AArch64.Dot

/-- What a term needs: sixteen coefficients of each polynomial, at `bf` (or `bg`) plus its
offset plus `x12`, base registers the loop keeps. -/
structure TermInputW (s : State) (bf bg : Reg) (fg : Nat × Nat) (F G : Nat → Nat) : Prop where
  baseF : bf ∉ clob
  baseG : bg ∉ clob
  offF : fg.1 < 65536
  offG : fg.2 < 65536
  boundF : ∀ e < 16, F e < 3329
  boundG : ∀ e < 16, G e < 3329
  valueF : ∀ e < 16, (coeffAtW 16 s.mem (s.gpr bf + BitVec.ofNat 64 fg.1 + s.gpr .x12) e).toNat = F e
  valueG : ∀ e < 16, (coeffAtW 16 s.mem (s.gpr bg + BitVec.ofNat 64 fg.2 + s.gpr .x12) e).toNat = G e
  readF : ∀ i < 2, InRegions (s.rd ++ s.wr)
    (s.gpr bf + BitVec.ofNat 64 fg.1 + s.gpr .x12 + BitVec.ofNat 64 (16 * i)) 16
  readG : ∀ i < 2, InRegions (s.rd ++ s.wr)
    (s.gpr bg + BitVec.ofNat 64 fg.2 + s.gpr .x12 + BitVec.ofNat 64 (16 * i)) 16

theorem TermInputW.keep {s s' : State} {bf bg : Reg} {fg : Nat × Nat} {F G : Nat → Nat}
    (h : TermInputW s bf bg fg F G) (hk : Only [.x1, .x2] s s') : TermInputW s' bf bg fg F G := by
  refine ⟨h.baseF, h.baseG, h.offF, h.offG, h.boundF, h.boundG, ?_, ?_, ?_, ?_⟩
  · rw [hk.mem, hk.get bf (not_mem_x12 h.baseF), hk.get .x12]; exact h.valueF
  · rw [hk.mem, hk.get bg (not_mem_x12 h.baseG), hk.get .x12]; exact h.valueG
  · rw [hk.rd, hk.wr, hk.get bf (not_mem_x12 h.baseF), hk.get .x12]; exact h.readF
  · rw [hk.rd, hk.wr, hk.get bg (not_mem_x12 h.baseG), hk.get .x12]; exact h.readG

/-- The coefficients `8 … 15`. -/
abbrev upper (F : Nat → Nat) : Nat → Nat := fun i => F (8 + i)

theorem fullTermW_ok {s : State} {bf bg : Reg} {fg : Nat × Nat} {lo hi : Nat → Sums} {F G : Nat → Nat}
    {n : Nat} (h : TermInputW s bf bg fg F G) (hc : VConsts s) (ha : AccumW s lo hi)
    (hlo : ∀ e < 4, (lo e).Bounded n) (hhi : ∀ e < 4, (hi e).Bounded n) (hn : n < 4) :
    WP isa (.block (Impl.MlKem.AArch64.DotW.termW bf bg fg)) s fun s' =>
      Only [.x1, .x2] s s' ∧ VConsts s' ∧
        AccumW s' (advance lo F G) (advance hi (upper F) (upper G)) := by
  rw [termW_partition, WP.block_append_iff]
  refine WP.mono (pointersW_ok h.baseF h.baseG h.offF h.offG) fun s₁ ⟨h₁, v₁, e₁, e₂⟩ => ?_
  have hc₁ : VConsts s₁ := ⟨by rw [v₁]; exact hc.q, by rw [v₁]; exact hc.m⟩
  have ha₁ : AccumW s₁ lo hi := by simpa only [AccumW, Accum, v₁] using ha
  have nlo : ∀ e < 4, (advance lo F G e).Bounded (n + 1) := fun e he =>
    (hlo e he).next (h.boundF _ (by omega)) (h.boundF _ (by omega)) (h.boundG _ (by omega))
      (h.boundG _ (by omega))
  have nhi : ∀ e < 4, (advance hi (upper F) (upper G) e).Bounded (n + 1) := fun e he =>
    (hhi e he).next (h.boundF _ (by omega)) (h.boundF _ (by omega)) (h.boundG _ (by omega))
      (h.boundG _ (by omega))
  rw [List.append_assoc, ← List.append_nil accumulateW]
  refine loads_ok (fun i hi => by rw [h₁.rd, h₁.wr, e₁]; exact h.readF i hi)
    (fun i hi => by rw [h₁.rd, h₁.wr, e₂]; exact h.readG i hi) fun s₂ c₂ l0 l1 l4 l5 => ?_
  have f0 : HLanes (s₂.v .v0) F := by
    rw [l0, e₁, h₁.mem, ← BitVec.add_zero (s.gpr bf + BitVec.ofNat 64 fg.1 + s.gpr .x12),
      show (0#64 : BitVec 64) = BitVec.ofNat 64 (2 * 0) from rfl]
    exact hlanes_coeffs _ _ 0 fun e he => by rw [Nat.zero_add]; exact h.valueF e (by omega)
  have f1 : HLanes (s₂.v .v1) (upper F) := by
    rw [l1, e₁, h₁.mem, show BitVec.ofNat 64 16 = BitVec.ofNat 64 (2 * 8) from rfl]
    exact hlanes_coeffs _ _ 8 fun e he => h.valueF (8 + e) (by omega)
  have g0 : HLanes (s₂.v .v4) G := by
    rw [l4, e₂, h₁.mem, ← BitVec.add_zero (s.gpr bg + BitVec.ofNat 64 fg.2 + s.gpr .x12),
      show (0#64 : BitVec 64) = BitVec.ofNat 64 (2 * 0) from rfl]
    exact hlanes_coeffs _ _ 0 fun e he => by rw [Nat.zero_add]; exact h.valueG e (by omega)
  have g1 : HLanes (s₂.v .v5) (upper G) := by
    rw [l5, e₂, h₁.mem, show BitVec.ofNat 64 16 = BitVec.ofNat 64 (2 * 8) from rfl]
    exact hlanes_coeffs _ _ 8 fun e he => h.valueG (8 + e) (by omega)
  refine gatherW_ok f0 f1 g0 g1 fun s₃ c₃ fe fo ge go => ?_
  have ha₃ : AccumW s₃ lo hi := by
    obtain ⟨⟨a1, a2, a3⟩, a5, a6, a7⟩ := ha₁
    exact ⟨⟨by rw [c₃.get .v21, c₂.get .v21]; exact a1, by rw [c₃.get .v22, c₂.get .v22]; exact a2,
      by rw [c₃.get .v23, c₂.get .v23]; exact a3⟩, by rw [c₃.get .v25, c₂.get .v25]; exact a5,
      by rw [c₃.get .v26, c₂.get .v26]; exact a6, by rw [c₃.get .v27, c₂.get .v27]; exact a7⟩
  have wl : ∀ e < 4, ∀ {x : Sums}, x.Bounded (n + 1) → x.even < 2 ^ 32 ∧ x.odd < 2 ^ 32 ∧ x.cross < 2 ^ 32 :=
    fun e _ x hx => by
      have := hx.noWrap (by omega)
      exact ⟨by omega, by omega, by omega⟩
  refine accumulateW_ok ha₃ fe fo ge go (fun e he => wl e he (nlo e he))
    (fun e he => wl e he (by
      have := nhi e he
      simp only [advance, upper] at this
      rw [show 8 + 2 * e = 2 * (4 + e) by omega, show 8 + (2 * e + 1) = 2 * (4 + e) + 1 by omega] at this
      exact this)) fun s₄ c₄ a₄ => wp_nil ?_
  have eqhi : (fun e => (hi e).next (F (2 * (4 + e))) (F (2 * (4 + e) + 1)) (G (2 * (4 + e)))
      (G (2 * (4 + e) + 1))) = advance hi (upper F) (upper G) := by
    funext e
    simp only [advance, upper]
    rw [show 8 + 2 * e = 2 * (4 + e) by omega, show 8 + (2 * e + 1) = 2 * (4 + e) + 1 by omega]
  rw [eqhi] at a₄
  have C := (c₂.trans c₃).trans c₄
  refine ⟨?_, hc₁.chg C, a₄⟩
  exact ⟨fun r hr => by rw [C.gpr]; exact h₁.gpr r hr, C.mem.trans h₁.mem, C.rd.trans h₁.rd,
    C.wr.trans h₁.wr, C.sp.trans h₁.sp, fun r hr => by rw [C.v r (by revert r hr; decide +kernel)]; exact h₁.vcs r hr⟩

end VG.Proof.MlKem.AArch64.DotW
