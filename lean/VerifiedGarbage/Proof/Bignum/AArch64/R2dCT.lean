module

public import VerifiedGarbage.Proof.Bignum.AArch64.R2dFast
public import VerifiedGarbage.Proof.Bignum.AArch64.R2dStep
import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dFast
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dStep
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# `R² mod m` by long division on AArch64 is constant time

Every loop count, branch and address of `fast` depends on the working
space's layout alone (`r2dFast_ct`): each step's loads of the bases from the
header, then the rest checked by the taint analysis from those bases
(`r2dStep_ct`), and `steps`' count `w` (`steps_ct`).
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.Bignum.AArch64 VG.Impl.Bignum.AArch64.R2Div
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-! ## A step -/

/-- `Good` after code that changes no memory and not `x0`. -/
theorem Good.keep {s t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hm : t.mem = s.mem) {rs : List Reg} (k : Keep rs s t) (h0 : .x0 ∉ rs) : Good t B Z w minv :=
  ⟨hg.scr.congr k.wr, (k.gpr .x0 h0).trans hg.x0, hm ▸ hg.hdr⟩

theorem GoodL.keep {L : Lay} {s t : State} (hg : GoodL L s) (hm : t.mem = s.mem) {rs : List Reg}
    (k : Keep rs s t) (h0 : .x0 ∉ rs) : GoodL L t :=
  ⟨hg.1.keep hm k h0, hg.2⟩


/-- `quot` runs, changing no memory. -/
theorem quot_runs {t : State} {B : Addr} {Z w : Nat} (hs : Scr t B Z)
    (h11 : t.gpr .x11 = off B (slot w aR2)) (h9 : t.gpr .x9 = off B (slot w aN))
    (h12 : t.gpr .x12 = BitVec.ofNat 64 w) (h6 : t.gpr .x6 = off B (slot w aTmp)) (hw : 2 ≤ w)
    (hw' : w < 2 ^ 31) (hZ : slot w 8 ≤ Z) :
    WP isa (.block quot) t fun t' =>
      t'.mem = t.mem ∧ Keep [.x1, .x2, .x3, .x4, .x5, .x13, .x14, .x15, .x16, .x17] t t' := by
  have hn := hs.nowrap
  have sl : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  have lN := sl aN (by decide)
  have lX := sl aR2 (by decide)
  have lT := sl aTmp (by decide)
  have e1 : slot w aR2 + 8 * (w - 1) - 8 = slot w aR2 + 8 * (w - 2) := by omega_arith
  refine WP.keep [.x1, .x2, .x3, .x4, .x5, .x13, .x14, .x15, .x16, .x17] (Q := fun t' => t'.mem = t.mem) ?_
    (by decide) (by decide) (by decide +kernel)
  brun [h11, h9, h12, h6, r2d_exec_tst, r2d_exec_cselc, CondCode.holds, shl3_sub8 (show 1 ≤ w by omega_arith)
    (show w < 2 ^ 61 by omega_arith), off_add, off_sub8 B (show 8 ≤ slot w aR2 + 8 * (w - 1) by omega_arith), e1,
    hs.ld (show slot w aN + 8 * (w - 1) + 8 ≤ Z by omega_arith), hs.ld (show slot w aR2 + 8 * (w - 1) + 8 ≤ Z by omega_arith),
    hs.ld (show slot w aR2 + 8 * (w - 2) + 8 ≤ Z by omega_arith), hs.ld (show slot w aTmp + 8 ≤ Z by omega_arith), quot,
    quotHead, quotMG]

/-- The working space and its header, for some `-m⁻¹`, with `w ≥ 2`. -/
def R2dGoodS (L : Ws) (s : State) : Prop :=
  ∃ mi, (Good s L.B L.Z L.w mi ∧ slot L.w 8 ≤ L.Z) ∧ 2 ≤ L.w ∧ L.w < 2 ^ 31

theorem pins_r2dGood {α : Type} {Φ : α → State → Prop} (f : α → Ws) (h : ∀ a s, Φ a s → R2dGoodS (f a) s) :
    Pins Φ [.x0] := by
  intro a s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  obtain ⟨_, g₁, _⟩ := h a s₁ h₁
  obtain ⟨_, g₂, _⟩ := h a s₂ h₂
  rw [g₁.1.x0, g₂.1.x0]

/-- After `bases`. -/
def R2dStepR (L : Ws) (s : State) : Prop := R2dGoodS L s ∧ StepRegs s L.B L.w

theorem pins_r2dStepR : Pins R2dStepR [.x8, .x9, .x11, .x6, .x12, .x7] := by
  intro L s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₁.2.x8, h₂.2.x8]
  · rw [h₁.2.x9, h₂.2.x9]
  · rw [h₁.2.x11, h₂.2.x11]
  · rw [h₁.2.x6, h₂.2.x6]
  · rw [h₁.2.x12, h₂.2.x12]
  · rw [h₁.2.x7, h₂.2.x7]

theorem r2dBases_ok {L : Ws} {t : State} (h : R2dGoodS L t) : WP isa (.block R2Div.bases) t (R2dStepR L) := by
  obtain ⟨mi, hg, hw, hw'⟩ := h
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off L.B (8 * i)) 8 := fun i hi =>
    hg.1.scr.ld (by have := hdr_lt_slot L.w 8 hi; have := hg.2; omega_arith)
  refine WP.mono (WP.keep [.x6, .x7, .x8, .x9, .x11, .x12] (Q := fun t' => (t'.gpr .x8 = off L.B (slot L.w aAcc) ∧
      t'.gpr .x9 = off L.B (slot L.w aN) ∧ t'.gpr .x11 = off L.B (slot L.w aR2) ∧
      t'.gpr .x6 = off L.B (slot L.w aTmp) ∧ t'.gpr .x12 = BitVec.ofNat 64 L.w ∧ t'.gpr .x7 = 0) ∧ t'.mem = t.mem)
    (by
      brun [R2Div.bases, hg.1.x0, hdr_enc (show sArr aAcc < 32 by decide), hdr_enc (show sArr aN < 32 by decide),
        hdr_enc (show sArr aR2 < 32 by decide), hdr_enc (show sArr aTmp < 32 by decide),
        hdr_enc (show sW < 32 by decide), hl (sArr aAcc) (by decide), hl (sArr aN) (by decide),
        hl (sArr aR2) (by decide), hl (sArr aTmp) (by decide), hl sW (by decide),
        hg.1.hdr.harr aAcc (by decide), hg.1.hdr.harr aN (by decide), hg.1.hdr.harr aR2 (by decide),
        hg.1.hdr.harr aTmp (by decide), hg.1.hdr.hw])
    (by decide) (by decide) (by decide +kernel)) fun t' ⟨⟨⟨a, b, c, d, e, f⟩, hm⟩, k⟩ =>
      ⟨⟨mi, ⟨hg.1.keep hm k (by decide), hg.2⟩, hw, hw'⟩, ⟨a, b, c, d, e, f⟩⟩

theorem quot_stepR {L : Ws} {t : State} (h : R2dStepR L t) : WP isa (.block quot) t (R2dStepR L) := by
  obtain ⟨⟨mi, hg, hw, hw'⟩, hr⟩ := h
  exact WP.mono (quot_runs hg.1.scr hr.x11 hr.x9 hr.x12 hr.x6 hw hw' hg.2) fun t' ⟨hm, k⟩ =>
    ⟨⟨mi, ⟨hg.1.keep hm k (by decide), hg.2⟩, hw, hw'⟩, hr.keep k⟩

theorem r2dStep_eq : step = .seq (.block (R2Div.bases ++ quot))
    (.seq zeroAcc (.seq mulAddRow (.seq subPass (.seq addBack (.seq addBack copyBack))))) := rfl

/-- A step leaks the same in runs with the same working space. -/
theorem r2dStep_ct : RelCT isa (Two R2dGoodS) step fun _ _ => True := by
  rw [r2dStep_eq]
  refine RelCT.seq (RelCT.block_append (RelCT.seq
    (two_piece (Ψ := R2dStepR) [.x0] (pins_r2dGood id fun _ _ h => h) (by taint_decide)
      fun _ _ h => r2dBases_ok h)
    (two_piece (Ψ := R2dStepR) _ pins_r2dStepR (by taint_decide) fun _ _ h => quot_stepR h)))
    (two_taint _ pins_r2dStepR (by taint_decide))

/-! ## The steps -/

/-- `steps`' precondition: `w` steps of `x < m`, with `v` for `m`'s top word. -/
def R2dSPre (L : Ws) (s : State) : Prop :=
  R2dGoodS L s ∧ s.gpr .x13 = BitVec.ofNat 64 L.w ∧ 2 ^ 63 ≤ (word s.mem L.B (slot L.w aN + 8 * (L.w - 1))).toNat ∧
    (word s.mem L.B (slot L.w aTmp)).toNat =
      (2 ^ 128 - 1) / (word s.mem L.B (slot L.w aN + 8 * (L.w - 1))).toNat - 2 ^ 64 ∧
    wv s.mem L.B (slot L.w aR2) L.w < wv s.mem L.B (slot L.w aN) L.w

/-- After `j` of `steps`' `w` steps. -/
def R2dSAt (L : Ws) (j : Nat) (t : State) : Prop :=
  ∃ (σ : State) (mi : BitVec 64) (M D X0 : Nat), R2dStepsInv σ L.B L.Z L.w mi M D X0 L.w j t ∧ slot L.w 8 ≤ L.Z ∧ 2 ≤ L.w ∧
    L.w < 2 ^ 31 ∧ 2 ^ 63 ≤ D ∧ 0 < M

theorem R2dSAt.goodS {L : Ws} {j : Nat} {t : State} (h : R2dSAt L j t) : R2dGoodS L t :=
  let ⟨_, mi, _, _, _, hI, hZ, hw, hw', _⟩ := h; ⟨mi, ⟨hI.g, hZ⟩, hw, hw'⟩

theorem r2dSteps_eq : steps =
    .seq (.block [sth .x13 sCnt]) (.loop (.seq step (.block (dblCount sCnt))) (.nonzero .x .x13)) := rfl

/-- `steps` leaks the same in runs with the same working space. -/
theorem steps_ct : RelCT isa (Two R2dSPre) steps fun _ _ => True := by
  rw [r2dSteps_eq]
  refine RelCT.seq (two_piece (Ψ := fun L s => 0 < L.w ∧ R2dSAt L 0 s) [.x0]
    (pins_r2dGood id fun _ _ h => h.1) (by taint_decide) ?_) ?_
  · rintro L s ⟨⟨mi, hg, hw, hw'⟩, h13, hd, hv, hX⟩
    exact WP.mono (r2dStepsStart_ok hg.1 hg.2 h13 rfl rfl hv hX) fun t hI =>
      ⟨by omega_arith, s, mi, _, _, _, hI, hg.2, hw, hw', hd, Nat.lt_of_le_of_lt (Nat.zero_le _) hX⟩
  refine (two_loop (Φ := R2dSAt) (Ψ := fun _ _ => True) (fun L => L.w) ?_ ?_).mono (fun _ _ h => h)
    fun _ _ _ => trivial
  · refine RelCT.seq (two_post (Ψ := fun (q : Ws × Nat) s => R2dGoodS q.1 s)
      (two_map (·.1) (fun _ _ h => h.2.goodS) r2dStep_ct) ?_)
      (two_taint _ (pins_r2dGood (·.1) fun _ _ h => h) (by taint_decide))
    rintro ⟨L, j⟩ s ⟨hj, σ, mi, M, D, X0, hI, hZ, hw, hw', hd, hM0⟩
    exact WP.mono (r2dStep_ok hI.g hZ hw hw' hI.n hI.top hd hI.v (by rw [hI.x]; exact Nat.mod_lt _ hM0))
      fun t ⟨g, _, _, _⟩ => ⟨mi, ⟨g, hZ⟩, hw, hw'⟩
  · rintro L j s hj ⟨σ, mi, M, D, X0, hI, hZ, hw, hw', hd, hM0⟩
    exact WP.mono (stepsIter_ok hZ hw hw' hd hM0 hw' hj hI)
      fun t ⟨hI', hz⟩ => ⟨eval_count hj hz, fun _ => ⟨σ, mi, M, D, X0, hI', hZ, hw, hw', hd, hM0⟩,
        fun _ => trivial⟩

/-! ## `fast` -/

/-- `fast`'s precondition: `m` odd with its top bit set. -/
def R2dFPre (L : Ws) (s : State) : Prop :=
  R2dGoodS L s ∧ wv s.mem L.B (slot L.w aN) L.w % 2 = 1 ∧
    2 ^ 63 ≤ (word s.mem L.B (slot L.w aN + 8 * (L.w - 1))).toNat

/-- `R2dFPre` after code that changes only array `j ≠ aN` and not `x0`. -/
theorem R2dFPre.arr {L : Ws} {s t : State} (h : R2dFPre L s) {rs : List Reg} (k : Keep rs s t) (h0 : .x0 ∉ rs)
    {j : Nat} (hj : j < 8) (hjN : j ≠ aN) (ha : Arrays L.B L.w [j] s.mem t.mem) : R2dFPre L t := by
  obtain ⟨⟨mi, hg, hw, hw'⟩, hodd, hd⟩ := h
  have hn := hg.1.scr.nowrap
  have lN := Nat.le_trans (slot_le (w := L.w) (show aN < 8 by decide)) hg.2
  have sp := slot_sep (w := L.w) hjN
  have sep : ∀ d k, d + 8 * k ≤ slot L.w aN + 8 * (L.w + 2) → slot L.w aN ≤ d →
      ∀ j' ∈ [j], d + 8 * k ≤ slot L.w j' ∨ slot L.w j' + 8 * (L.w + 2) ≤ d := by
    intro d k h1 h2 j' hj'
    rw [List.mem_singleton] at hj'; subst hj'; omega_arith
  refine ⟨⟨mi, ⟨⟨hg.1.scr.congr k.wr, (k.gpr .x0 h0).trans hg.1.x0, ha.hdr hg.1.hdr⟩, hg.2⟩, hw, hw'⟩, ?_, ?_⟩
  · rw [ha.wv_eq (sep _ _ (by omega_arith) (Nat.le_refl _)) (by omega_arith)]; exact hodd
  · rw [ha.word_eq (sep _ 1 (by omega_arith) (by omega_arith)) (by omega_arith)]; exact hd

/-- `R - m < m` and `m < R`, for `m` odd with its top bit set. -/
theorem fast_lt {m : Mem} {B : Addr} {w : Nat} (hw : 1 ≤ w) (hodd : wv m B (slot w aN) w % 2 = 1)
    (hd : 2 ^ 63 ≤ (word m B (slot w aN + 8 * (w - 1))).toNat) :
    2 ^ (64 * w) - wv m B (slot w aN) w < wv m B (slot w aN) w ∧ wv m B (slot w aN) w < 2 ^ (64 * w) := by
  have hMB := wv_lt m B (slot w aN) w
  have hMw := wv_split1 m B (slot w aN) hw
  generalize wv m B (slot w aN) w = M at *
  have hP : 2 ^ (64 * w) = 2 ^ (64 * (w - 1)) * 2 ^ 63 * 2 := by
    rw [Nat.mul_assoc, ← Nat.pow_succ, ← Nat.pow_add]; congr 1; omega_arith
  have hlo : 2 ^ (64 * (w - 1)) * 2 ^ 63 ≤ M := by
    rw [hMw, Nat.mul_comm (2 ^ (64 * (w - 1)))]
    exact Nat.le_trans (Nat.mul_le_mul_right _ hd) (Nat.le_add_right _ _)
  have h2 : 2 ^ (64 * (w - 1)) * 2 ^ 63 % 2 = 0 := by
    rw [Nat.mul_mod, show 2 ^ 63 % 2 = 0 from rfl, Nat.mul_zero, Nat.zero_mod]
  have : M ≠ 2 ^ (64 * (w - 1)) * 2 ^ 63 := fun h => by rw [h] at hodd; omega_arith
  omega_arith

/-- After `fast`'s loads. -/
def R2dF0 (L : Ws) (s : State) : Prop :=
  R2dFPre L s ∧ s.gpr .x11 = off L.B (slot L.w aR2) ∧ s.gpr .x9 = off L.B (slot L.w aN) ∧
    s.gpr .x6 = off L.B (slot L.w aTmp) ∧ s.gpr .x12 = BitVec.ofNat 64 L.w ∧ s.gpr .x7 = 0

/-- After `neg`: `x = R - m`. -/
def R2dF1 (L : Ws) (s : State) : Prop :=
  R2dFPre L s ∧ s.gpr .x9 = off L.B (slot L.w aN) ∧ s.gpr .x6 = off L.B (slot L.w aTmp) ∧
    s.gpr .x12 = BitVec.ofNat 64 L.w ∧ s.gpr .x7 = 0 ∧
    wv s.mem L.B (slot L.w aR2) L.w = 2 ^ (64 * L.w) - wv s.mem L.B (slot L.w aN) L.w

/-- After `recip`: `v`. -/
def R2dF2 (L : Ws) (s : State) : Prop :=
  R2dFPre L s ∧ wv s.mem L.B (slot L.w aR2) L.w = 2 ^ (64 * L.w) - wv s.mem L.B (slot L.w aN) L.w ∧
    (word s.mem L.B (slot L.w aTmp)).toNat =
      (2 ^ 128 - 1) / (word s.mem L.B (slot L.w aN + 8 * (L.w - 1))).toNat - 2 ^ 64

theorem pins_R2dF0 : Pins R2dF0 [.x11, .x9, .x6, .x12, .x7] := by
  intro L s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [h₁.2.1, h₂.2.1]
  · rw [h₁.2.2.1, h₂.2.2.1]
  · rw [h₁.2.2.2.1, h₂.2.2.2.1]
  · rw [h₁.2.2.2.2.1, h₂.2.2.2.2.1]
  · rw [h₁.2.2.2.2.2, h₂.2.2.2.2.2]

theorem pins_R2dF1 : Pins R2dF1 [.x9, .x6, .x12, .x7] := by
  intro L s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h₁.2.1, h₂.2.1]
  · rw [h₁.2.2.1, h₂.2.2.1]
  · rw [h₁.2.2.2.1, h₂.2.2.2.1]
  · rw [h₁.2.2.2.2.1, h₂.2.2.2.2.1]

theorem fastLoads_ok {L : Ws} {s : State} (h : R2dFPre L s) :
    WP isa (.block [ldh .x11 (sArr aR2), ldh .x9 (sArr aN), ldh .x6 (sArr aTmp), ldh .x12 sW, movi .x7 0]) s
      (R2dF0 L) := by
  obtain ⟨_, hg, -⟩ := h.1
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off L.B (8 * i)) 8 := fun i hi =>
    hg.1.scr.ld (by have := hdr_lt_slot L.w 8 hi; have := hg.2; omega_arith)
  refine WP.mono (WP.keep [.x6, .x7, .x9, .x11, .x12] (Q := fun t => (t.gpr .x11 = off L.B (slot L.w aR2) ∧
      t.gpr .x9 = off L.B (slot L.w aN) ∧ t.gpr .x6 = off L.B (slot L.w aTmp) ∧
      t.gpr .x12 = BitVec.ofNat 64 L.w ∧ t.gpr .x7 = 0) ∧ t.mem = s.mem)
    (by brun [hg.1.x0, hdr_enc (show sArr aN < 32 by decide), hdr_enc (show sArr aR2 < 32 by decide),
        hdr_enc (show sArr aTmp < 32 by decide), hdr_enc (show sW < 32 by decide), hl (sArr aN) (by decide),
        hl (sArr aR2) (by decide), hl (sArr aTmp) (by decide), hl sW (by decide), hg.1.hdr.harr aN (by decide),
        hg.1.hdr.harr aR2 (by decide), hg.1.hdr.harr aTmp (by decide), hg.1.hdr.hw])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨r, hm⟩, k⟩ => ⟨?_, r⟩
  exact h.arr k (by decide) (j := aR2) (by decide) (by decide) (by rw [hm]; exact fun _ _ => rfl)

theorem fastNeg_ok {L : Ws} {s : State} (h : R2dF0 L s) : WP isa neg s (R2dF1 L) := by
  obtain ⟨hf, h11, h9, h6, h12, h7⟩ := h
  obtain ⟨_, hg, hw, hw'⟩ := hf.1
  have hn := hg.1.scr.nowrap
  have sl : ∀ j < 8, slot L.w j + 8 * (L.w + 2) ≤ L.Z := fun j hj => Nat.le_trans (slot_le hj) hg.2
  have lN := sl aN (by decide)
  have lX := sl aR2 (by decide)
  have sXN := slot_sep (w := L.w) (show aR2 ≠ aN by decide)
  obtain ⟨hlt, hMB⟩ := fast_lt (show 1 ≤ L.w by omega_arith) hf.2.1 hf.2.2
  refine WP.mono (r2dNeg_ok hg.1.scr h11 h9 h12 h7 (by omega_arith) hw' (by omega_arith) (by omega_arith) (by omega_arith))
    fun t ⟨b, hv, o, k⟩ => ?_
  have ha : Arrays L.B L.w [aR2] s.mem t.mem :=
    Arrays.of_outside (List.mem_singleton_self _) o (Nat.le_refl _) (by omega_arith)
  have hf' := hf.arr k (by decide) (j := aR2) (by decide) (by decide) ha
  have hN : wv t.mem L.B (slot L.w aN) L.w = wv s.mem L.B (slot L.w aN) L.w := o.wv (by omega_arith) (by omega_arith)
  refine ⟨hf', (k.gpr .x9 (by decide)).trans h9, (k.gpr .x6 (by decide)).trans h6,
    (k.gpr .x12 (by decide)).trans h12, (k.gpr .x7 (by decide)).trans h7, ?_⟩
  rw [hN]
  cases b
  · simp only [Bool.toNat_false, Nat.mul_zero] at hv; omega_arith
  · simp only [Bool.toNat_true, Nat.mul_one] at hv; omega_arith

theorem fastRecip_ok {L : Ws} {s : State} (h : R2dF1 L s) : WP isa recip s (R2dF2 L) := by
  obtain ⟨hf, h9, h6, h12, h7, hx⟩ := h
  obtain ⟨_, hg, hw, hw'⟩ := hf.1
  have hn := hg.1.scr.nowrap
  have sl : ∀ j < 8, slot L.w j + 8 * (L.w + 2) ≤ L.Z := fun j hj => Nat.le_trans (slot_le hj) hg.2
  have lN := sl aN (by decide)
  have lT := sl aTmp (by decide)
  have lX := sl aR2 (by decide)
  have sTN := slot_sep (w := L.w) (show aTmp ≠ aN by decide)
  have sTX := slot_sep (w := L.w) (show aTmp ≠ aR2 by decide)
  refine WP.mono (r2dRecip_ok hg.1.scr h9 h12 h6 h7 (by omega_arith) hw' (by omega_arith) (by omega_arith)
    hf.2.2) fun t ⟨hv, o, k⟩ => ?_
  have ha : Arrays L.B L.w [aTmp] s.mem t.mem :=
    Arrays.of_outside (List.mem_singleton_self _) o (Nat.le_refl _) (by omega_arith)
  have hf' := hf.arr k (by decide) (j := aTmp) (by decide) (by decide) ha
  have hN : wv t.mem L.B (slot L.w aN) L.w = wv s.mem L.B (slot L.w aN) L.w := o.wv (by omega_arith) (by omega_arith)
  have hX : wv t.mem L.B (slot L.w aR2) L.w = wv s.mem L.B (slot L.w aR2) L.w := o.wv (by omega_arith) (by omega_arith)
  have hD : word t.mem L.B (slot L.w aN + 8 * (L.w - 1)) = word s.mem L.B (slot L.w aN + 8 * (L.w - 1)) :=
    o.word (by omega_arith) (by omega_arith)
  exact ⟨hf', by rw [hN, hX, hx], by rw [hD]; exact hv⟩

theorem fastCount_ok {L : Ws} {s : State} (h : R2dF2 L s) : WP isa (.block [ldh .x13 sW]) s (R2dSPre L) := by
  obtain ⟨hf, hx, hv⟩ := h
  obtain ⟨mi, hg, hw, hw'⟩ := hf.1
  have hsW : 8 * sW + 8 ≤ L.Z := by
    have := hdr_lt_slot L.w 8 (show sW < 32 by decide); have := hg.2; omega_arith
  refine WP.mono (WP.keep [.x13] (Q := fun t => t.gpr .x13 = BitVec.ofNat 64 L.w ∧ t.mem = s.mem)
    (by brun [hg.1.x0, hdr_enc (show sW < 32 by decide), hg.1.scr.ld hsW, hg.1.hdr.hw])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h13, hm⟩, k⟩ => ?_
  obtain ⟨hlt, -⟩ := fast_lt (show 1 ≤ L.w by omega_arith) hf.2.1 hf.2.2
  refine ⟨⟨mi, ⟨hg.1.keep hm k (by decide), hg.2⟩, hw, hw'⟩, h13, by rw [hm]; exact hf.2.2, by rw [hm]; exact hv, ?_⟩
  rw [hm, hx]; exact hlt

theorem r2dFast_eq : fast = .seq (.block [ldh .x11 (sArr aR2), ldh .x9 (sArr aN), ldh .x6 (sArr aTmp), ldh .x12 sW,
    movi .x7 0]) (.seq neg (.seq recip (.seq (.block [ldh .x13 sW]) steps))) := rfl

/-- `fast` leaks the same in runs with the same working space. -/
theorem r2dFast_ct : RelCT isa (Two R2dFPre) fast fun _ _ => True := by
  rw [r2dFast_eq]
  refine RelCT.seq (two_piece (Ψ := R2dF0) [.x0] (pins_r2dGood id fun _ _ h => h.1)
    (by taint_decide) fun _ _ h => fastLoads_ok h) ?_
  refine RelCT.seq (two_piece (Ψ := R2dF1) _ pins_R2dF0 (by taint_decide) fun _ _ h => fastNeg_ok h) ?_
  refine RelCT.seq (two_piece (Ψ := R2dF2) _ pins_R2dF1 (by taint_decide) fun _ _ h => fastRecip_ok h) ?_
  refine RelCT.seq (two_piece (Ψ := R2dSPre) [.x0] (pins_r2dGood id fun _ _ h => h.1.1)
    (by taint_decide) fun _ _ h => fastCount_ok h) steps_ct

end VG.Proof.Bignum.AArch64
