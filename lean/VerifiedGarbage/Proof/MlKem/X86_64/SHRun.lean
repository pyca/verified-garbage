module

public import VerifiedGarbage.Proof.MlKem.X86_64.SHAbs
public import VerifiedGarbage.Proof.MlKem.X86_64.S4Run
import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
import all Init.Data.Nat.Bitwise.Basic
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# ML-KEM on x86-64: `Sample4.sampleH`, the runs of the loop on three seeds

After the squeezes and the sponge's state stored back, the code runs
`vg_mlkem_sample_ntt4_avx2`'s loops (`S4Run.lean`) on the first three seeds
(`Q1`, `Q2`, `Done3`), keeping the sponge's state (`HS`): if one of them has
fewer than 256 coefficients after 168 iterations, the two more squeezes
permute all four states, the fourth no longer the sponge's.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.SH

variable {w16 : Bool}

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Proof.MlKem.X86_64.S4
open VG.Spec.MlKem
open VG.Spec.Sha3 (stateAt)
open VG.Proof.MlKem (xofByte sampleAfter sampleAfter_full sampleNTT_eq)
open VG.Proof.Sha3 (iterF)

/-- The sponge's state is `Hf`. -/
def HS (σ : State) (Hf : Spec.Sha3.State) (m : Mem) : Prop := stateAt m (hsA σ) = Hf

abbrev hsR (σ : State) : Region := ⟨hsA σ, 200⟩

theorem HS.frame {σ : State} {Hf : Spec.Sha3.State} {m m' : Mem} (h : HS σ Hf m) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (hsR σ).Disjoint r) : HS σ Hf m' := by
  unfold HS
  rw [VG.Proof.Sha3.stateAt_congr fun i hi => hf.bytes (R := hsR σ) hd (show 200 ≤ 2 ^ 64 by decide) hi]
  exact h

theorem low_hs (σ : State) : (lowR σ).Disjoint (hsR σ) :=
  Offset.base_disjoint (scr σ) (by simp only [oSave, oHS]; omega) (by simp only [oHS]; omega)

theorem cnt_hs (σ : State) : (cntR σ).Disjoint (hsR σ) :=
  Offset.disjoint (scr σ) (.inl (by simp only [oCnt, oHS]; omega)) (by simp only [oCnt]; omega)
    (by simp only [oHS]; omega)

theorem tab_hs (σ : State) : (tabR σ).Disjoint (hsR σ) :=
  Offset.disjoint (scr σ) (.inl (by simp only [oTab, oHS]; omega)) (by simp only [oTab]; omega)
    (by simp only [oHS]; omega)

theorem poly_hs {σ : State} (hp : PreW w16 σ) {K : Nat} (hK : K < 4) : (cRegion w16 (poly4W w16 (aP σ) K)).Disjoint (hsR σ) :=
  (scr_poly hp hK (a := oHS) (n := 200) (by simp only [oHS]; omega)).symm

/-- After the first 168 iterations on the seeds before `K`. -/
structure Q1 (w16 : Bool) (σ : State) (Y Hf : Spec.Sha3.State) (K : Nat) (s : State) : Prop where
  sq : SqY w16 σ Y 0 3 s
  tab : TabOK σ s.mem
  j : ∀ k < K, s.mem.readW (at' σ (oCnt + 8 * k)) 64 = BitVec.ofNat 64 (Lt σ k 168).length
  st : ∀ k < K, Stored w16 s.mem (poly4W w16 (aP σ) k) (Lt σ k 168)
  hs : HS σ Hf s.mem

/-- After the 112 more iterations on the seeds before `K`. -/
structure Q2 (w16 : Bool) (σ : State) (Y Hf : Spec.Sha3.State) (K : Nat) (s : State) : Prop where
  sq : SqY w16 σ (iterF 2 Y) 3 2 s
  tab : TabOK σ s.mem
  j : ∀ k < 3, s.mem.readW (at' σ (oCnt + 8 * k)) 64 =
    BitVec.ofNat 64 (Lt σ k (if k < K then 280 else 168)).length
  st : ∀ k < 3, Stored w16 s.mem (poly4W w16 (aP σ) k) (Lt σ k (if k < K then 280 else 168))
  hs : HS σ Hf s.mem

/-- The coefficients of each of the three seeds after 280 iterations, and whether they are 256. -/
structure Done3 (w16 : Bool) (σ : State) (Hf : Spec.Sha3.State) (s : State) : Prop where
  env : EnvW w16 σ s
  r14 : s.gpr .r14 = BitVec.ofNat 64 (okN σ 3)
  st : ∀ k < 3, Stored w16 s.mem (poly4W w16 (aP σ) k) (Lt σ k 280)
  hs : HS σ Hf s.mem

/-- Whether each of the three seeds has 256 coefficients after `t` iterations. -/
def allFull3 (σ : State) (t : Nat) : Bool := (List.range 3).all fun k => (Lt σ k t).length == 256

theorem okN_full3 (σ : State) : okN σ 3 = if allFull3 σ 280 then 1 else 0 := by
  have e : ((List.range 3).all fun k => (sampleNTT minIterations (B σ k)).isSome) = allFull3 σ 280 := by
    simp only [allFull3, isSome_iff]
  unfold okN
  rw [e]

section
variable {σ : State} (hp : PreW w16 σ)
include hp

/-! ## The first runs -/

/-- The table, after the squeezes, which it keeps. -/
theorem tabY_ok {Y Hf : Spec.Sha3.State} {s : State} (h : SqY w16 σ Y 0 3 s) (hs : HS σ Hf s.mem) :
    WP isa (.block tabBuild) s (Q1 w16 σ Y Hf 0) := by
  refine WP.mono (tab_ok hp h.env) fun s' h' => ⟨h.apart (by decide) h'.frame (fun r hr => ?_) (fun r hr => ?_)
    (fun r hr => ?_) h'.keep.2.1 h'.keep.2.2 fun r hr => h'.keep.gpr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
    h'.tab, fun _ hk => absurd hk (by omega), fun _ hk => absurd hk (by omega),
    hs.frame h'.frame fun r hr => by rw [List.mem_singleton.mp hr]; exact (tab_hs σ).symm⟩ <;>
    simp only [List.mem_singleton] at hr <;> subst hr
  · exact Offset.base_disjoint _ (by simp only [oSave, oTab]; omega) (by simp only [oTab]; omega)
  · exact Offset.disjoint _ (.inl (by simp only [oSave, oTab]; omega)) (by simp only [oSave]; omega)
      (by simp only [oTab]; omega)
  · exact ⟨scrR σ, by simp, sub_scr (by simp only [oTab]; omega)⟩

omit hp in
theorem lbY1 {Y Hf : Spec.Sha3.State} {K : Nat} (hK : K < 3) {s : State} (h : Q1 w16 σ Y Hf K s) : LBW w16 σ s K 0 s :=
  ⟨h.sq.env, rfl, h.tab, fun p hp' _ => by simpa using h.sq.buf K hK p (by omega), Frame.refl _ _⟩

/-- The count of seed `K` kept, after its first 168 iterations. -/
theorem run1EndY_ok {Y Hf : Spec.Sha3.State} {K : Nat} (hK : K < 3) {s s₂ : State} (h : Q1 w16 σ Y Hf K s)
    (h₂ : LAtW w16 σ s K 0 168 s₂) :
    WP isa (.block [.store (at_ .rbx (oCnt + 8 * K)) .rdi]) s₂ (Q1 w16 σ Y Hf (K + 1)) := by
  refine WP.mono (keepCnt_ok hp (by omega) h₂) fun s₃ ⟨hm, k⟩ => ?_
  have hf₃ : Frame [cntR σ] s₂.mem s₃.mem := by rw [hm]; exact cnt_write (by omega) _
  have g₂ := env_regs h.sq.env h₂.lb.env h₂.lb.r14
  have g₃ : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15, .r14], s₃.gpr r = s₂.gpr r := fun r _ => k.gpr (by simp)
  have hL : ∀ k t, (Lt σ k t).length ≤ 256 := fun k t => Lt_le σ k t
  refine ⟨(h.sq.apart (by decide) h₂.lb.fr (fun r hr => by rw [List.mem_singleton.mp hr]; exact low_poly hp (by omega))
      (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact scr_poly hp (by omega) (a := oSave) (n := 40) (by simp only [oSave]; omega)) (sub_polyR (by omega))
      (h₂.lb.env.rd.trans h.sq.env.rd.symm) (h₂.lb.env.wr.trans h.sq.env.wr.symm) g₂).apart (by decide) hf₃
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact low_cnt) (fun r hr => by rw [List.mem_singleton.mp hr]; exact sv_cnt)
      sub_cntR k.2.1 k.2.2 g₃,
    tab_frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact tab_cnt) hf₃ h₂.lb.tab, fun k hk => ?_, fun k hk => ?_,
    (h.hs.frame h₂.lb.fr fun r hr => by rw [List.mem_singleton.mp hr]; exact (poly_hs hp (by omega)).symm).frame hf₃
      fun r hr => by rw [List.mem_singleton.mp hr]; exact (cnt_hs σ).symm⟩
  · rw [hm]
    by_cases e : k = K
    · subst e; rw [Mem.readW_writeW_self64]
    · rw [rd64_off (by simp only [oCnt]; omega) (by simp only [oCnt]; omega) (by omega),
        cnt_poly hp (by omega) h₂.lb.fr (by omega), h.j k (by omega)]
  · refine st_cnt hp (by omega) hf₃ ?_ (hL _ _)
    by_cases e : k = K
    · subst e; exact h₂.stored
    · exact st_poly (by omega) (by omega) e h₂.lb.fr (h.st k (by omega)) (hL _ _)

/-- The first 168 iterations on seed `K`, and its count kept. -/
theorem run1Y_ok {Y Hf : Spec.Sha3.State} {K : Nat} (hK : K < 3) {s : State} (h : Q1 w16 σ Y Hf K s) :
    WP isa (run1 K w16) s (Q1 w16 σ Y Hf (K + 1)) := by
  unfold run1
  exact WP.seq (WP.mono (setup_ok hp (by omega) (lbY1 hK h)) fun s₁ ⟨h₁, h10⟩ =>
    WP.seq (WP.mono (loop_ok hp (by omega) (N := 21) (by decide) (by decide) (by decide) h₁ h10) fun _ h₂ =>
      run1EndY_ok hp hK h h₂))

/-! ## The check -/

/-- After the counts' check. -/
structure Checked3 (w16 : Bool) (σ : State) (Y Hf : Spec.Sha3.State) (s : State) : Prop where
  prior : ∃ s₀, Q1 w16 σ Y Hf 3 s₀ ∧ s.mem = s₀.mem ∧ Keep [.rax, .r14] s₀ s
  r14 : s.gpr .r14 = if allFull3 σ 168 then 1 else 0
  zf : s.zf = some (!allFull3 σ 168)

theorem cntFlags3_ok {t : Nat} {s : State} (env : EnvW w16 σ s)
    (j : ∀ k < 3, s.mem.readW (at' σ (oCnt + 8 * k)) 64 = BitVec.ofNat 64 (Lt σ k t).length) :
    WP isa (.block cntFlags3) s fun s' =>
      (s'.gpr .r14 = (if allFull3 σ t then 1 else 0) ∧ s'.mem = s.mem) ∧ Keep [.rax, .r14] s s' := by
  have hin : ∀ k < 3, InRegions (s.rd ++ s.wr) (scr σ + BitVec.ofNat 64 (oCnt + 8 * k)) 8 :=
    fun k hk => in_scr' hp env.rd env.wr (by simp only [oCnt]; omega)
  have h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
  have j0 := j 0 (by decide); have j1 := j 1 (by decide); have j2 := j 2 (by decide)
  simp only [oCnt, Nat.reduceMul, Nat.reduceAdd] at h0 h1 h2 j0 j1 j2
  refine WP.keep _ ?_ (writesOnly_of (by decide))
  change WP isa (.block ([.mov32 .r14 (.imm 1),
    .mov .rax (.mem (at_ .rbx 4424)), .shift .shr .rax 8, .alu32 .and .r14 (.reg .rax),
    .mov .rax (.mem (at_ .rbx 4432)), .shift .shr .rax 8, .alu32 .and .r14 (.reg .rax),
    .mov .rax (.mem (at_ .rbx 4440)), .shift .shr .rax 8, .alu32 .and .r14 (.reg .rax)])) s _
  xrun [env.rbx, h0, h1, h2, j0, j1, j2]
  simp only [cnt_bit (Lt_le σ _ _)]
  unfold allFull3
  simp only [List.range_succ, List.range_zero, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.true_and]
  cases (Lt σ 0 t).length == 256 <;> cases (Lt σ 1 t).length == 256 <;> cases (Lt σ 2 t).length == 256 <;> rfl

/-- The counts' check, after the first runs. -/
theorem check3_ok {Y Hf : Spec.Sha3.State} {s : State} (h : Q1 w16 σ Y Hf 3 s) :
    WP isa (.block (cntFlags3 ++ ([.alu32 .cmp .r14 (.imm 0)] : List Instr))) s (Checked3 w16 σ Y Hf) := by
  apply WP.block_append
  refine WP.mono (cntFlags3_ok hp h.sq.env h.j) fun s₁ ⟨⟨hr, hm⟩, hk⟩ => ?_
  refine WP.mono (WP.keep [.r14] (Q := fun s₂ => s₂.mem = s₁.mem ∧ s₂.gpr .r14 = s₁.gpr .r14 ∧
    s₂.zf = some ((s₁.gpr .r14).setWidth 32 == 0)) (by xrun; simp) (by decide))
    fun s₂ ⟨⟨hm', hr', hz⟩, hk'⟩ => ?_
  refine ⟨⟨s, h, hm'.trans hm, (hk.trans hk').mono (by simp)⟩, hr'.trans hr, ?_⟩
  rw [hz, hr]; cases allFull3 σ 168 <;> rfl

omit hp in
/-- Each of the three seeds has 256 coefficients after the first runs. -/
theorem Done3.of_full {Y Hf : Spec.Sha3.State} {s : State} (h : Checked3 w16 σ Y Hf s) (hf : allFull3 σ 168 = true) :
    Done3 w16 σ Hf s := by
  obtain ⟨s₀, h₀, hm, hk⟩ := h.prior
  have hfull : ∀ k < 3, (Lt σ k 168).length = 256 := by
    simpa only [allFull3, List.all_eq_true, List.mem_range, beq_iff_eq] using hf
  have he : ∀ k < 3, Lt σ k 280 = Lt σ k 168 := fun k hk =>
    sampleAfter_full (by rw [n_eq]; exact hfull k hk) 280 (by decide)
  refine ⟨h₀.sq.env.keep hm hk (by simp), ?_, fun k hk' => ?_, by unfold HS; rw [hm]; exact h₀.hs⟩
  · have hf' : allFull3 σ 280 = true := by
      simp only [allFull3, List.all_eq_true, List.mem_range, beq_iff_eq] at hf ⊢
      intro k hk; rw [he k hk]; exact hf k hk
    rw [h.r14, okN_full3, hf, hf']; rfl
  · rw [hm, he k hk']; exact h₀.st k hk'

/-! ## The second runs -/

/-- Before the two more squeezes: the counts and coefficients of the first runs. -/
structure M3 (w16 : Bool) (σ : State) (Y Hf : Spec.Sha3.State) (s : State) : Prop where
  sq : SqY w16 σ Y 3 0 s
  tab : TabOK σ s.mem
  j : ∀ k < 3, s.mem.readW (at' σ (oCnt + 8 * k)) 64 = BitVec.ofNat 64 (Lt σ k 168).length
  st : ∀ k < 3, Stored w16 s.mem (poly4W w16 (aP σ) k) (Lt σ k 168)
  hs : HS σ Hf s.mem

omit hp in
/-- `r14 ← 1`, after the check. -/
theorem reset3_ok {Y Hf : Spec.Sha3.State} {s : State} (h : Checked3 w16 σ Y Hf s) :
    WP isa (.block [.mov32 .r14 (.imm 1)]) s (M3 w16 σ Y Hf) := by
  obtain ⟨s₀, h₀, hm₀, hk₀⟩ := h.prior
  refine WP.mono (WP.keep [.r14] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .r14 = 1)
    (by xrun) (by decide)) fun s₁ ⟨⟨hm, hr⟩, hk⟩ => ?_
  have hm₁ : s₁.mem = s₀.mem := hm.trans hm₀
  have hk₁ : Keep [.rax, .r14] s₀ s₁ := (hk₀.trans hk).mono (by simp)
  exact ⟨⟨h₀.sq.env.keep hm₁ hk₁ (by simp), hr, by rw [hm₁]; exact h₀.sq.rc, by rw [hm₁]; exact h₀.sq.lanes,
    fun _ _ p hp' => absurd hp' (by omega)⟩, by rw [hm₁]; exact h₀.tab, by rw [hm₁]; exact h₀.j,
    by rw [hm₁]; exact h₀.st, by unfold HS; rw [hm₁]; exact h₀.hs⟩

/-- The two more squeezes. -/
theorem sqM3_ok {fast : Bool} {Y Hf : Spec.Sha3.State} {s : State} (h : M3 w16 σ Y Hf s) :
    WP isa (squeezes 0 2 fast) s (Q2 w16 σ Y Hf 0) := by
  refine WP.mono (sqYs_ok (fast := fast) hp (by decide) (by decide) h.sq) fun s₂ ⟨q₂, hf⟩ =>
    ⟨q₂, tab_frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact low_tab.symm) hf h.tab,
      fun k hk => ?_, fun k hk => ?_, h.hs.frame hf fun r hr => by rw [List.mem_singleton.mp hr]; exact (low_hs σ).symm⟩
  · rw [ite_eq_right (by omega), hf.readW (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact (Offset.base_disjoint (scr σ) (k := oSave) (e := oCnt + 8 * k) (n := 8) (by simp only [oSave, oCnt]; omega)
        (by simp only [oCnt]; omega)).symm) (by decide), h.j k hk]
  · rw [ite_eq_right (by omega)]
    exact stored_apart hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact (low_poly hp (by omega)).symm)
      (Lt_le σ k _) (h.st k hk)

omit hp in
theorem lbY2 {Y Hf : Spec.Sha3.State} {K : Nat} (hK : K < 3) {s : State} (h : Q2 w16 σ Y Hf K s) : LBW w16 σ s K 168 s :=
  ⟨h.sq.env, rfl, h.tab, fun p hp' hb => by
    rw [h.sq.buf K hK p (by omega)], Frame.refl _ _⟩

/-- The count of seed `K` kept, after its 112 more iterations. -/
theorem run2EndY_ok {Y Hf : Spec.Sha3.State} {K : Nat} (hK : K < 3) {s s₂ : State} (h : Q2 w16 σ Y Hf K s)
    (h₂ : LAtW w16 σ s K 168 112 s₂) :
    WP isa (.block [.store (at_ .rbx (oCnt + 8 * K)) .rdi]) s₂ (Q2 w16 σ Y Hf (K + 1)) := by
  refine WP.mono (keepCnt_ok hp (by omega) h₂) fun s₃ ⟨hm, k⟩ => ?_
  have hf₃ : Frame [cntR σ] s₂.mem s₃.mem := by rw [hm]; exact cnt_write (by omega) _
  have g₂ := env_regs h.sq.env h₂.lb.env h₂.lb.r14
  have g₃ : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15, .r14], s₃.gpr r = s₂.gpr r := fun r _ => k.gpr (by simp)
  have hL : ∀ k t, (Lt σ k t).length ≤ 256 := fun k t => Lt_le σ k t
  refine ⟨(h.sq.apart (by decide) h₂.lb.fr (fun r hr => by rw [List.mem_singleton.mp hr]; exact low_poly hp (by omega))
      (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact scr_poly hp (by omega) (a := oSave) (n := 40) (by simp only [oSave]; omega)) (sub_polyR (by omega))
      (h₂.lb.env.rd.trans h.sq.env.rd.symm) (h₂.lb.env.wr.trans h.sq.env.wr.symm) g₂).apart (by decide) hf₃
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact low_cnt) (fun r hr => by rw [List.mem_singleton.mp hr]; exact sv_cnt)
      sub_cntR k.2.1 k.2.2 g₃,
    tab_frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact tab_cnt) hf₃ h₂.lb.tab, fun k hk => ?_, fun k hk => ?_,
    (h.hs.frame h₂.lb.fr fun r hr => by rw [List.mem_singleton.mp hr]; exact (poly_hs hp (by omega)).symm).frame hf₃
      fun r hr => by rw [List.mem_singleton.mp hr]; exact (cnt_hs σ).symm⟩
  · rw [hm]
    by_cases e : k = K
    · subst e; rw [Mem.readW_writeW_self64, ite_eq_left (by omega)]
    · rw [rd64_off (by simp only [oCnt]; omega) (by simp only [oCnt]; omega) (by omega),
        cnt_poly hp (by omega) h₂.lb.fr (by omega), h.j k hk]
      by_cases hk' : k < K
      · rw [ite_eq_left hk', ite_eq_left (by omega)]
      · rw [ite_eq_right hk', ite_eq_right (by omega)]
  · refine st_cnt hp (by omega) hf₃ ?_ (hL _ _)
    by_cases e : k = K
    · subst e; rw [ite_eq_left (by omega)]; exact h₂.stored
    · have := st_poly (by omega) (by omega) e h₂.lb.fr (h.st k hk) (hL _ _)
      by_cases hk' : k < K
      · rw [ite_eq_left hk'] at this; rwa [ite_eq_left (by omega)]
      · rw [ite_eq_right hk'] at this; rwa [ite_eq_right (by omega)]

/-- 112 more iterations on seed `K`, and its count kept. -/
theorem run2Y_ok {Y Hf : Spec.Sha3.State} {K : Nat} (hK : K < 3) {s : State} (h : Q2 w16 σ Y Hf K s) :
    WP isa (run2 K w16) s (Q2 w16 σ Y Hf (K + 1)) := by
  have hj : s.mem.readW (at' σ (oCnt + 8 * K)) 64 = BitVec.ofNat 64 (Lt σ K 168).length := by
    rw [h.j K hK, ite_eq_right (by omega)]
  have hst : Stored w16 s.mem (poly4W w16 (aP σ) K) (Lt σ K 168) := by
    have := h.st K hK; rwa [ite_eq_right (by omega)] at this
  unfold run2
  exact WP.seq (WP.mono (contSetup_ok hp (by omega) (lbY2 hK h) hj hst) fun s₁ ⟨h₁, h10⟩ =>
    WP.seq (WP.mono (loop_ok hp (by omega) (N := 14) (by decide) (by decide) (by decide) h₁ h10) fun _ h₂ =>
      run2EndY_ok hp hK h h₂))

/-- The counts' AND, after the second runs. -/
theorem last3_ok {Y Hf : Spec.Sha3.State} {s : State} (h : Q2 w16 σ Y Hf 3 s) : WP isa (.block cntFlags3) s (Done3 w16 σ Hf) := by
  have hj : ∀ k < 3, s.mem.readW (at' σ (oCnt + 8 * k)) 64 = BitVec.ofNat 64 (Lt σ k 280).length :=
    fun k hk => by simpa only [ite_eq_left hk] using h.j k hk
  refine WP.mono (cntFlags3_ok hp h.sq.env hj) fun s' ⟨⟨hr, hm⟩, hk⟩ =>
    ⟨h.sq.env.keep hm hk (by simp), by rw [hr, okN_full3]; split <;> rfl, fun k hk' => ?_,
      by unfold HS; rw [hm]; exact h.hs⟩
  rw [hm]; simpa only [ite_eq_left hk'] using h.st k hk'

/-- The two more squeezes and the second runs, after the check. -/
theorem more3_ok {fast : Bool} {Y Hf : Spec.Sha3.State} {s : State} (h : Checked3 w16 σ Y Hf s) :
    WP isa (more3 fast w16) s (Done3 w16 σ Hf) := by
  unfold more3
  exact WP.seq (WP.mono (reset3_ok h) fun _ m => WP.seq (WP.mono (sqM3_ok hp m) fun _ q₀ =>
    WP.seq (WP.mono (run2Y_ok hp (by decide) q₀) fun _ q₁ =>
    WP.seq (WP.mono (run2Y_ok hp (by decide) q₁) fun _ q₂ =>
      WP.seq (WP.mono (run2Y_ok hp (by decide) q₂) fun _ q₃ => last3_ok hp q₃)))))

/-- The branch on the check. -/
theorem branch3_ok {fast : Bool} {Y Hf : Spec.Sha3.State} {s : State} (h : Checked3 w16 σ Y Hf s) :
    WP isa (.ite .e (more3 fast w16) (.block [])) s (Done3 w16 σ Hf) := by
  cases hf : allFull3 σ 168 with
  | false =>
    have hz : s.zf = some true := by rw [h.zf, hf]; rfl
    exact WP.ite true hz (fun _ => more3_ok hp h) (fun hb => absurd hb (by decide))
  | true =>
    have hz : s.zf = some false := by rw [h.zf, hf]; rfl
    exact WP.ite false hz (fun hb => absurd hb (by decide)) (fun _ => WP.block_nil (Done3.of_full h hf))

end

end VG.Proof.MlKem.X86_64.SH
