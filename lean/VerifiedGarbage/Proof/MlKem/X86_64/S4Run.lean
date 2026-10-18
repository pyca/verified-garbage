module

public import VerifiedGarbage.Proof.MlKem.X86_64.S4Loop
public import VerifiedGarbage.Proof.MlKem.X86_64.S4Tab
import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt4_avx2`, the runs of the loop

After the squeezes and the table (`P1W w16 σ 0`), the first 168 iterations on
each seed's buffer keep its count of coefficients (`run1_ok`, `P1`). If one
of them has fewer than 256 (`check_ok`), the code squeezes two more blocks of
each seed to its buffer, the states being kept by the runs (`more_ok`), and
runs 112 more iterations on each, from its count (`run2_ok`, `P2`): the 280
iterations of `SampleNTT`'s loop bounded by `minIterations` (`Done`). A seed
that already has 256 keeps them (`DoneW.of_full`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.S4

variable {w16 : Bool}

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Spec.MlKem
open VG.Proof.MlKem (xofByte sampleAfter sampleAfter_full sampleNTT_eq)
open VG.Proof.Sha3 (iterF)

/-- Where the counts of the seeds are kept. -/
abbrev cntR (σ : State) : Region := ⟨at' σ oCnt, 32⟩

/-- After the first 168 iterations on the seeds before `K`. -/
structure P1W (w16 : Bool) (σ : State) (K : Nat) (s : State) : Prop where
  sq : SqTW w16 σ 0 3 s
  tab : TabOK σ s.mem
  j : ∀ k < K, s.mem.readW (at' σ (oCnt + 8 * k)) 64 = BitVec.ofNat 64 (Lt σ k 168).length
  st : ∀ k < K, Stored w16 s.mem (poly4W w16 (aP σ) k) (Lt σ k 168)

/-- After the 112 more iterations on the seeds before `K`. -/
structure P2W (w16 : Bool) (σ : State) (K : Nat) (s : State) : Prop where
  sq : SqTW w16 σ 3 2 s
  tab : TabOK σ s.mem
  j : ∀ k < 4, s.mem.readW (at' σ (oCnt + 8 * k)) 64 =
    BitVec.ofNat 64 (Lt σ k (if k < K then 280 else 168)).length
  st : ∀ k < 4, Stored w16 s.mem (poly4W w16 (aP σ) k) (Lt σ k (if k < K then 280 else 168))

/-- The coefficients of each seed after 280 iterations, and whether they are 256. -/
structure DoneW (w16 : Bool) (σ s : State) : Prop where
  env : EnvW w16 σ s
  r14 : s.gpr .r14 = BitVec.ofNat 64 (okN σ 4)
  st : ∀ k < 4, Stored w16 s.mem (poly4W w16 (aP σ) k) (Lt σ k 280)

/-- Whether every seed has 256 coefficients after `t` iterations. -/
def allFull (σ : State) (t : Nat) : Bool := (List.range 4).all fun k => (Lt σ k t).length == 256

theorem Lt_le (σ : State) (k t : Nat) : (Lt σ k t).length ≤ 256 :=
  VG.Proof.MlKem.sampleAfter_length_le (a := []) (by simp) _ t

/-- `SampleNTT` bounded by `minIterations`, from the coefficients after 280 iterations. -/
theorem isSome_iff (σ : State) (k : Nat) :
    (sampleNTT minIterations (B σ k)).isSome = ((Lt σ k 280).length == 256) := by
  rw [sampleNTT_eq, show minIterations = 280 from rfl]
  by_cases h : (Lt σ k 280).length = 256
  · rw [ite_eq_left (by rw [n_eq]; exact h), h]; rfl
  · rw [ite_eq_right (by rw [n_eq]; exact h)]
    simp only [Option.isSome_none, Bool.false_eq, beq_eq_false_iff_ne, ne_eq]
    exact h

theorem okN_full (σ : State) : okN σ 4 = if allFull σ 280 then 1 else 0 := by
  have e : ((List.range 4).all fun k => (sampleNTT minIterations (B σ k)).isSome) = allFull σ 280 := by
    simp only [allFull, isSome_iff]
  unfold okN
  rw [e]

/-- The polynomial of seed `k`, from its coefficients after 280 iterations. -/
theorem polyIs_of {σ : State} {m : Mem} {k : Nat} (h : Stored w16 m (poly4W w16 (aP σ) k) (Lt σ k 280)) :
    ∀ f, sampleNTT minIterations (B σ k) = some f → PolyIsW (cw w16) m (poly4W w16 (aP σ) k) f := by
  intro f e
  rw [sampleNTT_eq, show minIterations = 280 from rfl] at e
  by_cases hf : (Lt σ k 280).length = 256
  · rw [ite_eq_left (by rw [n_eq]; exact hf)] at e
    rw [← Option.some.inj e]
    exact SampleNtt.stored_polyAt h hf
  · rw [ite_eq_right (by rw [n_eq]; exact hf)] at e
    exact absurd e (Option.some_ne_none f).symm

/-- The state before the epilogue. -/
theorem DoneW.pc {σ s : State} (h : DoneW w16 σ s) : PCW w16 (fun _ => True) σ 4 s :=
  ⟨h.env, trivial, h.r14, fun k hk f e => polyIs_of (h.st k hk) f e⟩

/-- Whether a count is 256, from its bit 8. -/
theorem cnt_bit {n : Nat} (hn : n ≤ 256) :
    (BitVec.ofNat 64 n >>> 8).setWidth 32 = if n == 256 then 1 else 0 := by
  by_cases e : n = 256
  · subst e; decide
  · rw [ite_eq_right (by simpa using e)]
    apply BitVec.eq_of_toNat_eq
    have h0 : (0 : BitVec 32).toNat = 0 := rfl
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [h0]
    omega

section
variable {σ : State} (hp : PreW w16 σ)
include hp

/-! ## The regions -/

omit hp in
theorem low_cnt : (lowR σ).Disjoint (cntR σ) :=
  Offset.base_disjoint (scr σ) (by simp only [oSave, oCnt]; omega) (by simp only [oCnt]; omega)

omit hp in
theorem sv_cnt : (⟨at' σ oSave, 40⟩ : Region).Disjoint (cntR σ) :=
  Offset.disjoint (scr σ) (.inl (by simp only [oSave, oCnt]; omega)) (by simp only [oSave]; omega)
    (by simp only [oCnt]; omega)

omit hp in
theorem tab_cnt : (tabR σ).Disjoint (cntR σ) :=
  Offset.disjoint (scr σ) (.inr (by simp only [oTab, oCnt]; omega)) (by simp only [oTab]; omega)
    (by simp only [oCnt]; omega)

omit hp in
theorem low_tab : (lowR σ).Disjoint (tabR σ) :=
  Offset.base_disjoint (scr σ) (by simp only [oSave, oTab]; omega) (by simp only [oTab]; omega)

theorem low_poly {K : Nat} (hK : K < 4) : (lowR σ).Disjoint (cRegion w16 (poly4W w16 (aP σ) K)) :=
  Region.Disjoint.sub_right (Region.Disjoint.sub_left hp.a_scr.symm (Region.sub_prefix (by simp only [oSave]; omega)))
    (sub_poly hK)

omit hp in
theorem sub_polyR {K : Nat} (hK : K < 4) : ∀ r ∈ [cRegion w16 (poly4W w16 (aP σ) K)], ∃ R ∈ [aR w16 σ, scrR σ, stkR σ], Region.Sub r R :=
  fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨aR w16 σ, by simp, sub_poly hK⟩

omit hp in
theorem sub_cntR : ∀ r ∈ [cntR σ], ∃ R ∈ [aR w16 σ, scrR σ, stkR σ], Region.Sub r R :=
  fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨scrR σ, by simp, sub_scr (by simp only [oCnt]; omega)⟩

omit hp in
theorem cnt_write {k : Nat} (hk : k < 4) {m : Mem} (v : BitVec 64) :
    Frame [cntR σ] m (m.writeW (at' σ (oCnt + 8 * k)) v) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) v
    (Offset.contains (scr σ) (by omega) (by omega) (by simp only [oCnt]; omega))

/-- A count, apart from writes to a polynomial. -/
theorem cnt_poly {K : Nat} (hK : K < 4) {m m' : Mem} (hf : Frame [cRegion w16 (poly4W w16 (aP σ) K)] m m') {k : Nat} (hk : k < 4) :
    m'.readW (at' σ (oCnt + 8 * k)) 64 = m.readW (at' σ (oCnt + 8 * k)) 64 := by
  have hd := scr_poly hp hK (a := oCnt + 8 * k) (n := 8) (by simp only [oCnt]; omega)
  exact hf.readW (Region.contains_self _ _) (by simpa using hd) (by decide)

omit hp in
/-- A stored polynomial, apart from writes to another one. -/
theorem st_poly {K k : Nat} (hK : K < 4) (hk : k < 4) (hne : k ≠ K) {m m' : Mem}
    (hf : Frame [cRegion w16 (poly4W w16 (aP σ) K)] m m') {L : List Zq} (h : Stored w16 m (poly4W w16 (aP σ) k) L) (hL : L.length ≤ 256) :
    Stored w16 m' (poly4W w16 (aP σ) k) L :=
  stored_apart hf (fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint (aP σ) (d := pBytes w16 * k) (n := 256 * (cw w16 / 8)) (e := pBytes w16 * K)
      (k := 256 * (cw w16 / 8)) (by wd_omega) (by wd_omega) (by wd_omega)) hL h

/-- A stored polynomial, apart from writes to the counts. -/
theorem st_cnt {k : Nat} (hk : k < 4) {m m' : Mem} (hf : Frame [cntR σ] m m') {L : List Zq}
    (h : Stored w16 m (poly4W w16 (aP σ) k) L) (hL : L.length ≤ 256) : Stored w16 m' (poly4W w16 (aP σ) k) L :=
  stored_apart hf (fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact (scr_poly hp hk (a := oCnt) (n := 32) (by simp only [oCnt]; omega)).symm) hL h

/-- The end of a run on seed `K`: its count kept. -/
theorem keepCnt_ok {s₀ : State} {K b t : Nat} (hK : K < 4) {s : State} (h : LAtW w16 σ s₀ K b t s) :
    WP isa (.block [.store (at_ .rbx (oCnt + 8 * K)) .rdi]) s fun s' =>
      s'.mem = s.mem.writeW (at' σ (oCnt + 8 * K)) (BitVec.ofNat 64 (Lt σ K (b + t)).length) ∧ Keep [] s s' := by
  have hin : InRegions s.wr (scr σ + BitVec.ofNat 64 (oCnt + 8 * K)) 8 :=
    in_scr hp h.lb.env.wr (by simp only [oCnt]; omega)
  exact WP.keep [] (Q := fun s' => s'.mem = s.mem.writeW (at' σ (oCnt + 8 * K)) (BitVec.ofNat 64 (Lt σ K (b + t)).length))
    (by xrun [h.lb.env.rbx, hin, h.rdi]) rfl

omit hp in
/-- The registers `Env` fixes, and `r14`. -/
theorem env_regs {s₀ s : State} (e₀ : EnvW w16 σ s₀) (e : EnvW w16 σ s) (h14 : s.gpr .r14 = s₀.gpr .r14) :
    ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15, .r14], s.gpr r = s₀.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [e.rbx, e₀.rbx]
  · rw [e.r12, e₀.r12]
  · rw [e.r13, e₀.r13]
  · rw [e.rsp, e₀.rsp]
  · rw [e.r15, e₀.r15]
  · exact h14

/-! ## The first runs -/

/-- The table, after the squeezes. -/
theorem p1_zero_ok {s : State} (h : SqTW w16 σ 0 3 s) : WP isa (.block tabBuild) s (P1W w16 σ 0) :=
  WP.mono (tabT_ok hp h) fun _ ⟨h', ht⟩ => ⟨h', ht, fun _ hk => absurd hk (by omega), fun _ hk => absurd hk (by omega)⟩

omit hp in
theorem lb1 {K : Nat} (hK : K < 4) {s : State} (h : P1W w16 σ K s) : LBW w16 σ s K 0 s :=
  ⟨h.sq.env, rfl, h.tab, fun p hp' _ => by simpa using h.sq.buf K hK p (by omega), Frame.refl _ _⟩

/-- The count of seed `K` kept, after its first 168 iterations. -/
theorem run1End_ok {K : Nat} (hK : K < 4) {s s₂ : State} (h : P1W w16 σ K s) (h₂ : LAtW w16 σ s K 0 168 s₂) :
    WP isa (.block [.store (at_ .rbx (oCnt + 8 * K)) .rdi]) s₂ (P1W w16 σ (K + 1)) := by
  refine WP.mono (keepCnt_ok hp hK h₂) fun s₃ ⟨hm, k⟩ => ?_
  have hf₃ : Frame [cntR σ] s₂.mem s₃.mem := by rw [hm]; exact cnt_write hK _
  have g₂ := env_regs h.sq.env h₂.lb.env h₂.lb.r14
  have g₃ : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15, .r14], s₃.gpr r = s₂.gpr r := fun r _ => k.gpr (by simp)
  have hL : ∀ k t, (Lt σ k t).length ≤ 256 := fun k t => Lt_le σ k t
  refine ⟨(h.sq.apart (by decide) h₂.lb.fr (fun r hr => by rw [List.mem_singleton.mp hr]; exact low_poly hp hK)
      (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact scr_poly hp hK (a := oSave) (n := 40) (by simp only [oSave]; omega)) (sub_polyR hK)
      (h₂.lb.env.rd.trans h.sq.env.rd.symm) (h₂.lb.env.wr.trans h.sq.env.wr.symm) g₂).apart (by decide) hf₃
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact low_cnt) (fun r hr => by rw [List.mem_singleton.mp hr]; exact sv_cnt)
      sub_cntR k.2.1 k.2.2 g₃,
    tab_frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact tab_cnt) hf₃ h₂.lb.tab, fun k hk => ?_, fun k hk => ?_⟩
  · rw [hm]
    by_cases e : k = K
    · subst e; rw [Mem.readW_writeW_self64]
    · rw [rd64_off (by simp only [oCnt]; omega) (by simp only [oCnt]; omega) (by omega), cnt_poly hp hK h₂.lb.fr (by omega),
        h.j k (by omega)]
  · refine st_cnt hp (by omega) hf₃ ?_ (hL _ _)
    by_cases e : k = K
    · subst e; exact h₂.stored
    · exact st_poly hK (by omega) e h₂.lb.fr (h.st k (by omega)) (hL _ _)

/-- The first 168 iterations on seed `K`, and its count kept. -/
theorem run1_ok {K : Nat} (hK : K < 4) {s : State} (h : P1W w16 σ K s) : WP isa (run1 K w16) s (P1W w16 σ (K + 1)) := by
  unfold run1
  exact WP.seq (WP.mono (setup_ok hp hK (lb1 hK h)) fun s₁ ⟨h₁, h10⟩ =>
    WP.seq (WP.mono (loop_ok hp hK (N := 21) (by decide) (by decide) (by decide) h₁ h10) fun _ h₂ =>
      run1End_ok hp hK h h₂))

/-! ## The check -/

/-- After the counts' check. -/
structure CheckedW (w16 : Bool) (σ s : State) : Prop where
  prior : ∃ s₀, P1W w16 σ 4 s₀ ∧ s.mem = s₀.mem ∧ Keep [.rax, .r14] s₀ s
  r14 : s.gpr .r14 = if allFull σ 168 then 1 else 0
  zf : s.zf = some (!allFull σ 168)

theorem cntFlags_ok {t : Nat} {s : State} (env : EnvW w16 σ s)
    (j : ∀ k < 4, s.mem.readW (at' σ (oCnt + 8 * k)) 64 = BitVec.ofNat 64 (Lt σ k t).length) :
    WP isa (.block cntFlags) s fun s' =>
      (s'.gpr .r14 = (if allFull σ t then 1 else 0) ∧ s'.mem = s.mem) ∧ Keep [.rax, .r14] s s' := by
  have hin : ∀ k < 4, InRegions (s.rd ++ s.wr) (scr σ + BitVec.ofNat 64 (oCnt + 8 * k)) 8 :=
    fun k hk => in_scr' hp env.rd env.wr (by simp only [oCnt]; omega)
  have h0 := hin 0 (by decide); have h1 := hin 1 (by decide)
  have h2 := hin 2 (by decide); have h3 := hin 3 (by decide)
  have j0 := j 0 (by decide); have j1 := j 1 (by decide)
  have j2 := j 2 (by decide); have j3 := j 3 (by decide)
  simp only [oCnt, Nat.reduceMul, Nat.reduceAdd] at h0 h1 h2 h3 j0 j1 j2 j3
  refine WP.keep _ ?_ (writesOnly_of (by decide))
  change WP isa (.block ([.mov32 .r14 (.imm 1),
    .mov .rax (.mem (at_ .rbx 4424)), .shift .shr .rax 8, .alu32 .and .r14 (.reg .rax),
    .mov .rax (.mem (at_ .rbx 4432)), .shift .shr .rax 8, .alu32 .and .r14 (.reg .rax),
    .mov .rax (.mem (at_ .rbx 4440)), .shift .shr .rax 8, .alu32 .and .r14 (.reg .rax),
    .mov .rax (.mem (at_ .rbx 4448)), .shift .shr .rax 8, .alu32 .and .r14 (.reg .rax)])) s _
  xrun [env.rbx, h0, h1, h2, h3, j0, j1, j2, j3]
  simp only [cnt_bit (Lt_le σ _ _)]
  unfold allFull
  simp only [List.range_succ, List.range_zero, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.true_and]
  cases (Lt σ 0 t).length == 256 <;> cases (Lt σ 1 t).length == 256 <;>
    cases (Lt σ 2 t).length == 256 <;> cases (Lt σ 3 t).length == 256 <;> rfl

/-- The counts' check, after the first runs. -/
theorem check_ok {s : State} (h : P1W w16 σ 4 s) :
    WP isa (.block (cntFlags ++ ([.alu32 .cmp .r14 (.imm 0)] : List Instr))) s (CheckedW w16 σ) := by
  apply WP.block_append
  refine WP.mono (cntFlags_ok hp h.sq.env h.j) fun s₁ ⟨⟨hr, hm⟩, hk⟩ => ?_
  refine WP.mono (WP.keep [.r14] (Q := fun s₂ => s₂.mem = s₁.mem ∧ s₂.gpr .r14 = s₁.gpr .r14 ∧
    s₂.zf = some ((s₁.gpr .r14).setWidth 32 == 0)) (by xrun; simp) (by decide))
    fun s₂ ⟨⟨hm', hr', hz⟩, hk'⟩ => ?_
  refine ⟨⟨s, h, hm'.trans hm, (hk.trans hk').mono (by simp)⟩, hr'.trans hr, ?_⟩
  rw [hz, hr]; cases allFull σ 168 <;> rfl

omit hp in
/-- Every seed has 256 coefficients after the first runs. -/
theorem DoneW.of_full {s : State} (h : CheckedW w16 σ s) (hf : allFull σ 168 = true) : DoneW w16 σ s := by
  obtain ⟨s₀, h₀, hm, hk⟩ := h.prior
  have hfull : ∀ k < 4, (Lt σ k 168).length = 256 := by
    simpa only [allFull, List.all_eq_true, List.mem_range, beq_iff_eq] using hf
  have he : ∀ k < 4, Lt σ k 280 = Lt σ k 168 := fun k hk =>
    sampleAfter_full (by rw [n_eq]; exact hfull k hk) 280 (by decide)
  refine ⟨h₀.sq.env.keep hm hk (by simp), ?_, fun k hk' => ?_⟩
  · have hf' : allFull σ 280 = true := by
      simp only [allFull, List.all_eq_true, List.mem_range, beq_iff_eq] at hf ⊢
      intro k hk; rw [he k hk]; exact hf k hk
    rw [h.r14, okN_full, hf, hf']; rfl
  · rw [hm, he k hk']; exact h₀.st k hk'

/-! ## The second runs -/

/-- Before the two more squeezes: the counts and coefficients of the first runs. -/
structure M2W (w16 : Bool) (σ : State) (s : State) : Prop where
  sq : SqTW w16 σ 3 0 s
  tab : TabOK σ s.mem
  j : ∀ k < 4, s.mem.readW (at' σ (oCnt + 8 * k)) 64 = BitVec.ofNat 64 (Lt σ k 168).length
  st : ∀ k < 4, Stored w16 s.mem (poly4W w16 (aP σ) k) (Lt σ k 168)

omit hp in
/-- `r14 ← 1`, after the check. -/
theorem reset_ok {s : State} (h : CheckedW w16 σ s) : WP isa (.block [.mov32 .r14 (.imm 1)]) s (M2W w16 σ) := by
  obtain ⟨s₀, h₀, hm₀, hk₀⟩ := h.prior
  refine WP.mono (WP.keep [.r14] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .r14 = 1)
    (by xrun) (by decide)) fun s₁ ⟨⟨hm, hr⟩, hk⟩ => ?_
  have hm₁ : s₁.mem = s₀.mem := hm.trans hm₀
  have hk₁ : Keep [.rax, .r14] s₀ s₁ := (hk₀.trans hk).mono (by simp)
  exact ⟨⟨h₀.sq.env.keep hm₁ hk₁ (by simp), hr, by rw [hm₁]; exact h₀.sq.rc, by rw [hm₁]; exact h₀.sq.lanes,
    fun _ _ p hp' => absurd hp' (by omega)⟩, by rw [hm₁]; exact h₀.tab, by rw [hm₁]; exact h₀.j,
    by rw [hm₁]; exact h₀.st⟩

/-- The two more squeezes. -/
theorem sqM_ok {fast : Bool} {s : State} (h : M2W w16 σ s) : WP isa (squeezes 0 2 fast) s (P2W w16 σ 0) := by
  refine WP.mono (sqTs_ok (fast := fast) hp (by decide) (by decide) h.sq) fun s₂ ⟨q₂, hf⟩ =>
    ⟨q₂, tab_frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact low_tab.symm) hf h.tab,
      fun k hk => ?_, fun k hk => ?_⟩
  · rw [ite_eq_right (by omega), hf.readW (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact (Offset.base_disjoint (scr σ) (k := oSave) (e := oCnt + 8 * k) (n := 8) (by simp only [oSave, oCnt]; omega)
        (by simp only [oCnt]; omega)).symm) (by decide), h.j k hk]
  · rw [ite_eq_right (by omega)]
    exact stored_apart hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact (low_poly hp hk).symm)
      (Lt_le σ k _) (h.st k hk)

omit hp in
theorem lb2 {K : Nat} (hK : K < 4) {s : State} (h : P2W w16 σ K s) : LBW w16 σ s K 168 s :=
  ⟨h.sq.env, rfl, h.tab, fun p hp' hb => by
    rw [h.sq.buf K hK p (by omega)], Frame.refl _ _⟩

/-- The count of seed `K` kept, after its 112 more iterations. -/
theorem run2End_ok {K : Nat} (hK : K < 4) {s s₂ : State} (h : P2W w16 σ K s) (h₂ : LAtW w16 σ s K 168 112 s₂) :
    WP isa (.block [.store (at_ .rbx (oCnt + 8 * K)) .rdi]) s₂ (P2W w16 σ (K + 1)) := by
  refine WP.mono (keepCnt_ok hp hK h₂) fun s₃ ⟨hm, k⟩ => ?_
  have hf₃ : Frame [cntR σ] s₂.mem s₃.mem := by rw [hm]; exact cnt_write hK _
  have g₂ := env_regs h.sq.env h₂.lb.env h₂.lb.r14
  have g₃ : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15, .r14], s₃.gpr r = s₂.gpr r := fun r _ => k.gpr (by simp)
  have hL : ∀ k t, (Lt σ k t).length ≤ 256 := fun k t => Lt_le σ k t
  refine ⟨(h.sq.apart (by decide) h₂.lb.fr (fun r hr => by rw [List.mem_singleton.mp hr]; exact low_poly hp hK)
      (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact scr_poly hp hK (a := oSave) (n := 40) (by simp only [oSave]; omega)) (sub_polyR hK)
      (h₂.lb.env.rd.trans h.sq.env.rd.symm) (h₂.lb.env.wr.trans h.sq.env.wr.symm) g₂).apart (by decide) hf₃
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact low_cnt) (fun r hr => by rw [List.mem_singleton.mp hr]; exact sv_cnt)
      sub_cntR k.2.1 k.2.2 g₃,
    tab_frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact tab_cnt) hf₃ h₂.lb.tab, fun k hk => ?_, fun k hk => ?_⟩
  · rw [hm]
    by_cases e : k = K
    · subst e; rw [Mem.readW_writeW_self64, ite_eq_left (by omega)]
    · rw [rd64_off (by simp only [oCnt]; omega) (by simp only [oCnt]; omega) (by omega), cnt_poly hp hK h₂.lb.fr hk,
        h.j k hk]
      by_cases hk' : k < K
      · rw [ite_eq_left hk', ite_eq_left (by omega)]
      · rw [ite_eq_right hk', ite_eq_right (by omega)]
  · refine st_cnt hp hk hf₃ ?_ (hL _ _)
    by_cases e : k = K
    · subst e; rw [ite_eq_left (by omega)]; exact h₂.stored
    · have := st_poly hK hk e h₂.lb.fr (h.st k hk) (hL _ _)
      by_cases hk' : k < K
      · rw [ite_eq_left hk'] at this; rwa [ite_eq_left (by omega)]
      · rw [ite_eq_right hk'] at this; rwa [ite_eq_right (by omega)]

/-- 112 more iterations on seed `K`, and its count kept. -/
theorem run2_ok {K : Nat} (hK : K < 4) {s : State} (h : P2W w16 σ K s) : WP isa (run2 K w16) s (P2W w16 σ (K + 1)) := by
  have hj : s.mem.readW (at' σ (oCnt + 8 * K)) 64 = BitVec.ofNat 64 (Lt σ K 168).length := by
    rw [h.j K hK, ite_eq_right (by omega)]
  have hst : Stored w16 s.mem (poly4W w16 (aP σ) K) (Lt σ K 168) := by
    have := h.st K hK; rwa [ite_eq_right (by omega)] at this
  unfold run2
  exact WP.seq (WP.mono (contSetup_ok hp hK (lb2 hK h) hj hst) fun s₁ ⟨h₁, h10⟩ =>
    WP.seq (WP.mono (loop_ok hp hK (N := 14) (by decide) (by decide) (by decide) h₁ h10) fun _ h₂ =>
      run2End_ok hp hK h h₂))

/-- The counts' AND, after the second runs. -/
theorem last_ok {s : State} (h : P2W w16 σ 4 s) : WP isa (.block cntFlags) s (DoneW w16 σ) := by
  have hj : ∀ k < 4, s.mem.readW (at' σ (oCnt + 8 * k)) 64 = BitVec.ofNat 64 (Lt σ k 280).length :=
    fun k hk => by simpa only [ite_eq_left hk] using h.j k hk
  refine WP.mono (cntFlags_ok hp h.sq.env hj) fun s' ⟨⟨hr, hm⟩, hk⟩ =>
    ⟨h.sq.env.keep hm hk (by simp), by rw [hr, okN_full]; split <;> rfl, fun k hk' => ?_⟩
  rw [hm]; simpa only [ite_eq_left hk'] using h.st k hk'

/-- The two more squeezes and the second runs, after the check. -/
theorem more4_ok {fast : Bool} {s : State} (h : CheckedW w16 σ s) : WP isa (more4 fast w16) s (DoneW w16 σ) := by
  unfold more4
  exact WP.seq (WP.mono (reset_ok h) fun _ m => WP.seq (WP.mono (sqM_ok hp m) fun _ q₀ =>
    WP.seq (WP.mono (run2_ok hp (by decide) q₀) fun _ q₁ =>
    WP.seq (WP.mono (run2_ok hp (by decide) q₁) fun _ q₂ => WP.seq (WP.mono (run2_ok hp (by decide) q₂) fun _ q₃ =>
      WP.seq (WP.mono (run2_ok hp (by decide) q₃) fun _ q₄ => last_ok hp q₄))))))

/-- The branch on the check. -/
theorem branch_ok {fast : Bool} {s : State} (h : CheckedW w16 σ s) :
    WP isa (.ite .e (more4 fast w16) (.block [])) s (DoneW w16 σ) := by
  cases hf : allFull σ 168 with
  | false =>
    have hz : s.zf = some true := by rw [h.zf, hf]; rfl
    exact WP.ite true hz (fun _ => more4_ok hp h) (fun hb => absurd hb (by decide))
  | true =>
    have hz : s.zf = some false := by rw [h.zf, hf]; rfl
    exact WP.ite false hz (fun hb => absurd hb (by decide)) (fun _ => WP.block_nil (DoneW.of_full h hf))

end

end VG.Proof.MlKem.X86_64.S4
