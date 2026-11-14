module
public import VerifiedGarbage.Proof.Rsa.Arm.CvDivD
public import VerifiedGarbage.Proof.Rsa.Arm.CvFail
public import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
public import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal

import VerifiedGarbage.Proof.Rsa.Arm.CvTaint
import VerifiedGarbage.Proof.Rsa.Arm.CvTaintW
public import VerifiedGarbage.Proof.Rsa.Arm.CvWords
public import VerifiedGarbage.Proof.Rsa.Arm.KdDivCT
public import VerifiedGarbage.Proof.Rsa.Arm.CvFinish
import VerifiedGarbage.Proof.Rsa.Arm.CvLoads
import VerifiedGarbage.Proof.Rsa.Arm.DivCT
import VerifiedGarbage.Proof.Rsa.Arm.InvParts
import VerifiedGarbage.Proof.Framework.Sig

/-! # `vg_rsa_crt_values` on ARMv7: constant time

Two runs from states that agree on what the contract makes public
(`PubI`) are related at every stage by what correctness says of each run
from its own initial state (`Lift`): the pieces the taint analysis checks
(`CvTaint.lean`) agree on the stack arguments and on the registers
correctness determines from them, and the divisions start from the same
geometry (`Div.code_ct`). The branch on the modulus' validity agrees, as
`n` is public.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CrtValues
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.CrtValues
open VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm

/-- What the two runs' initial states agree on. -/
structure PubI (σ₁ σ₂ : State) : Prop where
  sp : σ₁.sp = σ₂.sp
  n : nBytes σ₁ = nBytes σ₂
  r0 : σ₁.gpr .r0 = σ₂.gpr .r0
  r1 : σ₁.gpr .r1 = σ₂.gpr .r1
  r2 : σ₁.gpr .r2 = σ₂.gpr .r2
  r3 : σ₁.gpr .r3 = σ₂.gpr .r3
  args : ∀ i < 12, stackArg σ₁ i = stackArg σ₂ i

theorem PubI.geom {σ₁ σ₂ : State} (p : PubI σ₁ σ₂) :
    cvB σ₁ = cvB σ₂ ∧ cvZ σ₁ = cvZ σ₂ ∧ cvW σ₁ = cvW σ₂ := by
  simp only [cvB, cvZ, cvW, cvK, p.args 10 (by decide), p.args 11 (by decide), p.args 3 (by decide),
    and_self]

/-- What makes a state of a run agree with the other run's on the stack arguments. -/
structure Run (σ s : State) : Prop where
  pre : CvPre σ
  sp : s.sp = σ.sp
  wr : s.wr = σ.wr
  args : ∀ i < 12, stackArg s i = stackArg σ i

theorem Base.run {σ s : State} (h : Base σ s) : Run σ s := ⟨h.pre, h.sp, h.wr, fun _ hi => h.arg hi⟩
theorem Done.run {σ s : State} (h : Done σ s) : Run σ s := ⟨h.pre, h.sp, h.wr, fun _ hi => h.arg hi⟩

theorem run_wf {σ s : State} (h : Run σ s) :
    s.sp.toNat + 48 ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr s.sp, 48⟩ r := by
  refine ⟨by rw [h.sp]; exact h.pre.sp48, ?_⟩
  have e : (⟨State.addr s.sp, 48⟩ : Region) = rA σ := by
    simp only [rA, stackArgAddr, h.sp, Nat.mul_zero, BitVec.add_zero]
  rw [e, h.wr, h.pre.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  exacts [h.pre.dpA.symm, h.pre.dqA.symm, h.pre.qiA.symm, h.pre.sA.symm]

theorem agree {σ₁ σ₂ s₁ s₂ : State} (p : PubI σ₁ σ₂) (h₁ : Run σ₁ s₁) (h₂ : Run σ₂ s₂) {rs : List Reg}
    (hr : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) : VG.Arm.Taint.Agree (argTaint rs 48) s₁ s₂ := by
  have hsp : s₁.sp = s₂.sp := by rw [h₁.sp, h₂.sp, p.sp]
  exact agree_argTaint hr hsp (run_wf h₁) (run_wf h₂)
    (argMem_of (j := 12) hsp (by rw [h₁.sp]; exact h₁.pre.sp48) fun i hi => by
      rw [h₁.args i hi, h₂.args i hi, p.args i hi])

/-- Two runs at the same stage, each from its own initial state. -/
def Lift (F : State → State → Prop) (s t : State) : Prop := ∃ σ₁ σ₂, PubI σ₁ σ₂ ∧ F σ₁ s ∧ F σ₂ t

theorem Lift.mono {F G : State → State → Prop} (h : ∀ σ s, F σ s → G σ s) {s t : State} :
    Lift F s t → Lift G s t := fun ⟨σ₁, σ₂, p, h₁, h₂⟩ => ⟨σ₁, σ₂, p, h _ _ h₁, h _ _ h₂⟩

theorem lift {F G : State → State → Prop} {c : Prog isa}
    (h : ∀ σ₁ σ₂, PubI σ₁ σ₂ → RelCT isa (fun s t => F σ₁ s ∧ F σ₂ t) c fun s t => G σ₁ s ∧ G σ₂ t) :
    RelCT isa (Lift F) c (Lift G) := by
  intro s t tr1 tr2 u v ⟨σ₁, σ₂, p, h₁, h₂⟩ e1 e2
  obtain ⟨tr, g₁, g₂⟩ := h σ₁ σ₂ p s t tr1 tr2 u v ⟨h₁, h₂⟩ e1 e2
  exact ⟨tr, σ₁, σ₂, p, g₁, g₂⟩

/-- A piece the taint analysis checks with the registers `rs` public. -/
theorem piece {F G : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hc : ∃ hc, (VG.Taint.check taint (argTaint rs 48) c hc).isSome = true)
    (run : ∀ σ s, F σ s → Run σ s)
    (regs : ∀ σ₁ σ₂ s₁ s₂, PubI σ₁ σ₂ → F σ₁ s₁ → F σ₂ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hw : ∀ σ s, F σ s → WP isa c s (G σ)) : RelCT isa (Lift F) c (Lift G) :=
  lift fun σ₁ σ₂ p => rel_agree (F := F σ₁) (F' := F σ₂) (argTaint rs 48)
    (fun _ _ h h' => agree p (run _ _ h) (run _ _ h') (regs _ _ _ _ p h h')) hc (hw σ₁) (hw σ₂)

/-- `piece`, for code `taintU` checks: code with `umaal`. -/
theorem pieceU {F G : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hc : ∃ hc, (VG.Taint.check taintU (argTaint rs 48) c hc).isSome = true)
    (run : ∀ σ s, F σ s → Run σ s)
    (regs : ∀ σ₁ σ₂ s₁ s₂, PubI σ₁ σ₂ → F σ₁ s₁ → F σ₂ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hw : ∀ σ s, F σ s → WP isa c s (G σ)) : RelCT isa (Lift F) c (Lift G) :=
  lift fun σ₁ σ₂ p => by
    obtain ⟨_, hc⟩ := hc
    exact ((RelCT.taint (A := taintU) (argTaint rs 48)
      (fun s s' h => agree p (run _ _ h.1) (run _ _ h.2) (regs _ _ _ _ p h.1 h.2)) hc).wp
      fun s s' h => ⟨hw σ₁ s h.1, hw σ₂ s' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

/-- A division, from the same geometry in both runs. -/
theorem divPiece {g : State → VG.Proof.Rsa.Arm.Div.Geometry} {Q : State → State → Prop}
    (hg : ∀ σ₁ σ₂, PubI σ₁ σ₂ → g σ₁ = g σ₂) :
    RelCT isa (Lift fun σ u => VG.Proof.Rsa.Arm.Div.Context (g σ) u ∧ WP isa VG.Impl.Rsa.Arm.Div.code u (Q σ))
      VG.Impl.Rsa.Arm.Div.code (Lift Q) :=
  lift fun _ _ p => rel_wp (VG.Proof.Rsa.Arm.Div.code_ct.mono (fun _ _ h => ⟨h.1.1, hg _ _ p ▸ h.2.1⟩)
    fun _ _ h => h) (fun _ h => h.2) (fun _ h => h.2)

theorem geom_eq {σ₁ σ₂ : State} (p : PubI σ₁ σ₂) (q r d t : Nat) :
    divGeom (cvB σ₁) (cvZ σ₁) (cvW σ₁) q r d t = divGeom (cvB σ₂) (cvZ σ₂) (cvW σ₂) q r d t := by
  obtain ⟨eB, eZ, eW⟩ := p.geom
  rw [eB, eZ, eW]

/-- The registers `ptr` uses agree. -/
theorem ws_regs {σ₁ σ₂ s₁ s₂ : State} (p : PubI σ₁ σ₂) {N₁ N₂ : Nat}
    (h₁ : Ws s₁ (cvB σ₁) (cvZ σ₁) (cvW σ₁) N₁) (h₂ : Ws s₂ (cvB σ₂) (cvZ σ₂) (cvW σ₂) N₂) :
    s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 := by
  obtain ⟨eB, -, eW⟩ := p.geom
  rw [h₁.r7, h₂.r7, h₁.r8, h₂.r8, h₁.r9, h₂.r9, eB, eW]
  exact ⟨rfl, rfl, rfl⟩

/-- A piece constant time from the same geometry in both runs. -/
theorem gPiece {c : Prog isa} {Pre : State → State → Prop}
    (hc : ∀ σ₁ σ₂, PubI σ₁ σ₂ → RelCT isa (fun s t => Pre σ₁ s ∧ Pre σ₂ t) c fun _ _ => True)
    {F G : State → State → Prop} (hpre : ∀ σ s, F σ s → Pre σ s) (hw : ∀ σ s, F σ s → WP isa c s (G σ)) :
    RelCT isa (Lift F) c (Lift G) :=
  lift fun σ₁ σ₂ p => (((hc σ₁ σ₂ p).mono (P' := fun s t => F σ₁ s ∧ F σ₂ t)
    (fun _ _ h => ⟨hpre _ _ h.1, hpre _ _ h.2⟩) fun _ _ h => h).wp (F₁ := G σ₁) (F₂ := G σ₂)
    fun _ _ h => ⟨hw _ _ h.1, hw _ _ h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

/-- The product of a balanced key. -/
theorem mulPiece {F G : State → State → Prop} (hpre : ∀ σ s, F σ s → SA σ s ∧ BalCv σ)
    (hw : ∀ σ s, F σ s → WP isa (VG.Impl.Rsa.Arm.KeyDiv.mulLo aDR aP aQ) s (G σ)) :
    RelCT isa (Lift F) (VG.Impl.Rsa.Arm.KeyDiv.mulLo aDR aP aQ) (Lift G) :=
  gPiece (Pre := fun σ s => SA σ s ∧ BalCv σ) (fun σ₁ σ₂ p => by
    obtain ⟨eB, eZ, eW⟩ := p.geom
    exact RelCT.exists_ (P := fun (_ : 16 ≤ cvW σ₁ ∧ cvW σ₁ % 2 = 0) s t => (SA σ₁ s ∧ BalCv σ₁) ∧
        (SA σ₂ t ∧ BalCv σ₂)) (fun hw => (VG.Proof.Rsa.Arm.KeyDiv.mulLo_ct mulW_taint (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) hw.2 (by omega_using [hw])).mono
      (fun s t h => ⟨h.1.1.mulPre h.1.2, by rw [eB, eZ, eW]; exact h.2.1.mulPre h.2.2⟩) fun _ _ h => h)
      |>.mono (fun s t h => ⟨⟨h.1.1.base.pre.w16.1, h.1.2.2.2⟩, h⟩) fun _ _ h => h) hpre hw

/-- A division by words of a balanced key. -/
theorem divPieceW {r : Nat} (T : VG.Proof.Rsa.Arm.KeyDiv.DivTaint aD r aDD aDQ aDT aT1) (hr : r ∈ [aDR2, aDR3])
    {F G : State → State → Prop} {M : State → Nat}
    (hpre : ∀ σ s, F σ s → ∃ X₁, SW σ X₁ s ∧
      num s.mem (cvB σ) (cvW σ) aDD = VG.Proof.Rsa.fixT (cvW σ / 2) (M σ) ∧ M σ < 2 ^ (32 * (cvW σ / 2)))
    (hw : ∀ σ s, F σ s → WP isa (VG.Impl.Rsa.Arm.KeyDiv.divW aD r aDD aDQ aDT aT1) s (G σ)) :
    RelCT isa (Lift F) (VG.Impl.Rsa.Arm.KeyDiv.divW aD r aDD aDQ aDT aT1) (Lift G) := by
  have hr' : r < nArr ∧ r ≠ aD ∧ r ≠ aDQ ∧ r ≠ aT1 ∧ r ≠ aDT ∧ r ≠ aDD ∧ r ≠ 0 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> decide
  refine gPiece (Pre := fun σ s => 16 ≤ cvW σ ∧ VG.Proof.Rsa.Arm.KeyDiv.DivPre (cvB σ) (cvZ σ) (cvW σ) nArr aDD s)
    (fun σ₁ σ₂ p => ?_) (fun σ s h => ?_) hw
  · obtain ⟨eB, eZ, eW⟩ := p.geom
    exact RelCT.exists_ (P := fun (_ : 16 ≤ cvW σ₁) s t => (16 ≤ cvW σ₁ ∧
        VG.Proof.Rsa.Arm.KeyDiv.DivPre (cvB σ₁) (cvZ σ₁) (cvW σ₁) nArr aDD s) ∧
        (16 ≤ cvW σ₂ ∧ VG.Proof.Rsa.Arm.KeyDiv.DivPre (cvB σ₂) (cvZ σ₂) (cvW σ₂) nArr aDD t))
      (fun hw => (VG.Proof.Rsa.Arm.KeyDiv.divW_ct T (by decide) hr'.1 (by decide) (by decide) (by decide)
        (by decide) (by decide) hr'.2.1 hr'.2.2.1 hr'.2.2.2.1 (by decide) (Ne.symm hr'.2.2.2.2.2.1) (by decide)
        (by decide) (Ne.symm hr'.2.2.2.2.1) (by decide) (by decide) (by decide) hr'.2.2.2.2.2.2 (by decide)
        (by decide) (by decide) (by omega_using [hw])).mono
        (fun s t h => ⟨h.1.2, by rw [eB, eZ, eW]; exact h.2.2⟩) fun _ _ h => h)
      |>.mono (fun s t h => ⟨h.1.1, h⟩) fun _ _ h => h
  · obtain ⟨X₁, hs, hM, hMl⟩ := hpre σ s h
    exact ⟨hs.base.pre.w16.1, hs.divPre hM hMl⟩

/-- The checks and values of a balanced key are constant time. -/
theorem midW_ct [VG.Proof.Rsa.Arm.Keys.InvLaw] {um : Bool} :
    RelCT isa (Lift fun σ s => StA σ s ∧ BalCv σ) (midW um) (Lift MidW) := by
  rw [show midW um = seqs ([[.block (ctx ++ bitOf sPodd aP)], [VG.Impl.Rsa.Arm.KeyDiv.mulLo aDR aP aQ], chunkW um,
      [VG.Impl.Rsa.Arm.KeyDiv.divW aD aDR2 aDD aDQ aDT aT1],
      [copy aDD aQ, .block (clrLow aDD ++ VG.Impl.Rsa.Arm.KeyDiv.fixTop aDD)],
      [VG.Impl.Rsa.Arm.KeyDiv.divW aD aDR3 aDD aDQ aDT aT1]] : List (List (Prog isa))).flatten from rfl]
  refine RelCT.of_join (fun l hl => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> simp) (List.cons_ne_nil _ _) ?_
  simp only [List.map_cons, List.map_nil, seqs_single]
  refine RelCT.seq (piece (G := fun σ s => SA σ s ∧ BalCv σ) [] oddW_taint (fun _ _ h => h.1.base.run)
    (fun _ _ _ _ _ _ _ _ h => nomatch h) fun _ _ h => WP.mono (oddW_ok h.1) fun _ h' => ⟨h', h.2⟩) ?_
  refine RelCT.seq (mulPiece (G := fun σ s => (SA σ s ∧
      num s.mem (cvB σ) (cvW σ) aDR = cvP σ * cvQ σ % 2 ^ (32 * cvW σ)) ∧ BalCv σ) (fun _ _ h => h)
    fun _ _ h => WP.mono (mulW_ok h.1 h.2) fun _ h' => ⟨h', h.2⟩) ?_
  refine RelCT.seq (pieceU (G := fun σ s => (SW σ (xW σ) s ∧ num s.mem (cvB σ) (cvW σ) aDD = fP σ) ∧ BalCv σ)
    [.r7, .r8, .r9] (chunkW_taint um) (fun _ _ h => h.1.1.base.run)
    (fun _ _ _ _ p h₁ h₂ => by
      obtain ⟨e7, e8, e9⟩ := ws_regs p h₁.1.1.ws h₂.1.1.ws
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl) <;> first | exact e7 | exact e8 | exact e9)
    fun _ _ h => WP.mono (chunkW_ok h.1.1 h.2 h.1.2) fun _ h' => ⟨h', h.2⟩) ?_
  refine RelCT.seq (divPieceW (M := fun σ => 2 * (cvP σ / 2)) (G := fun σ s => (SW σ (xW σ) s ∧
      num s.mem (cvB σ) (cvW σ) aDR2 = cvD σ % fP σ) ∧ BalCv σ) divW2_taint (by decide)
    (fun _ _ h => ⟨_, h.1.1, h.1.2, Nat.lt_of_le_of_lt (by omega_using []) h.2.p_lt⟩)
    fun _ _ h => WP.mono (div2W_ok h.1.1 h.2 h.1.2) fun _ h' => ⟨h', h.2⟩) ?_
  refine RelCT.seq (piece (G := fun σ s => (SW σ (xW σ) s ∧ num s.mem (cvB σ) (cvW σ) aDR2 = cvD σ % fP σ ∧
      num s.mem (cvB σ) (cvW σ) aDD = fQ σ) ∧ BalCv σ)
    [.r7, .r8, .r9] setQ_taint (fun _ _ h => h.1.1.base.run)
    (fun _ _ _ _ p h₁ h₂ => by
      obtain ⟨e7, e8, e9⟩ := ws_regs p h₁.1.1.ws h₂.1.1.ws
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl) <;> first | exact e7 | exact e8 | exact e9)
    fun _ _ h => WP.mono (setQW_ok h.1.1 h.2 h.1.2) fun _ h' => ⟨h', h.2⟩) ?_
  exact divPieceW (M := fun σ => 2 * (cvQ σ / 2)) divW3_taint (by decide)
    (fun _ _ h => ⟨_, h.1.1, h.1.2.2, Nat.lt_of_le_of_lt (by omega_using []) h.2.q_lt⟩)
    fun _ _ h => div3W_ok h.1.1 h.2 h.1.2.1 h.1.2.2

/-- The stages of the valid branch. -/
abbrev F1 (σ u : State) : Prop :=
  VG.Proof.Rsa.Arm.Div.Context (gN σ) u ∧ WP isa VG.Impl.Rsa.Arm.Div.code u (StC σ)
abbrev F3 (σ u : State) : Prop := ∃ X₁ X₂, StD σ X₁ X₂ u
abbrev F4 (σ u : State) : Prop := ∃ X₁ X₂, StE σ X₁ X₂ u
abbrev F5 (σ u : State) : Prop :=
  VG.Proof.Rsa.Arm.Div.Context (gQ σ) u ∧ WP isa VG.Impl.Rsa.Arm.Div.code u (fun t => ∃ X₁ X₂, StG σ X₁ X₂ t)
abbrev F7 (σ u : State) : Prop := Base σ u ∧ Ws u (cvB σ) (cvZ σ) (cvW σ) nArr ∧
  u.gpr .r10 = σ.gpr .r0 ∧ u.gpr .r12 = σ.gpr .r2 ∧ WP isa stores u (Done σ)
/-- After either branch. -/
abbrev FJ (σ u : State) : Prop := ∃ X₁ X₂, StM σ X₁ X₂ u

/-- Any key's checks: `n` divided by `p`. -/
theorem midD_ct [VG.Proof.Rsa.Arm.Keys.InvLaw] {um : Bool} : RelCT isa (Lift StA) (midD um) (Lift FJ) := by
  unfold midD
  simp only [seqs]
  refine RelCT.seq (piece (G := F1) [.r7, .r8, .r9] divN_taint (fun _ _ h => h.base.run)
    (fun _ _ _ _ p h₁ h₂ => by
      obtain ⟨e7, e8, e9⟩ := ws_regs p h₁.ws h₂.ws
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl) <;> first | exact e7 | exact e8 | exact e9)
    fun _ _ h => divN_pre_ok h) ?_
  refine RelCT.seq (divPiece (g := gN) fun _ _ p => geom_eq p _ _ _ _) ?_
  refine RelCT.seq (pieceU (G := F3) [] (checks_taint um) (fun _ _ h => h.base.run)
    (fun _ _ _ _ _ _ _ _ h => nomatch h) fun _ _ h => ?_) ?_
  · rw [checks_eq]
    exact (wp_seqs_append (by unfold checksA invSetup; simp) (by unfold checksB; simp)).mpr
      (WP.mono (checksA_ok h) fun _ h3 => WP.mono (checksB_ok h3) fun _ h4 => ⟨_, _, h4⟩)
  refine RelCT.seq ((divPiece (g := gP) (Q := F4) fun _ _ p => geom_eq p _ _ _ _).mono
    (fun _ _ => Lift.mono fun _ _ ⟨_, _, h⟩ => ⟨h.ctx, WP.mono (divP_ok h) fun _ h' => ⟨_, _, h'⟩⟩)
    fun _ _ h => h) ?_
  refine RelCT.seq (piece (G := F5) [] divQ_taint (fun _ _ ⟨_, _, h⟩ => h.base.run)
    (fun _ _ _ _ _ _ _ _ h => nomatch h)
    fun _ _ ⟨_, _, h⟩ => WP.mono (divQ_pre_ok h) fun _ h' => ⟨h'.1, WP.mono h'.2 fun _ h'' => ⟨_, _, h''⟩⟩) ?_
  exact (divPiece (g := gQ) fun _ _ p => geom_eq p _ _ _ _).mono (fun _ _ h => h)
    fun _ _ h => Lift.mono (fun _ _ ⟨_, _, h⟩ => ⟨_, _, h.toM⟩) h

theorem valid_ct [VG.Proof.Rsa.Arm.Keys.InvLaw] {um : Bool} : RelCT isa (Lift Base) (valid um) (Lift Done) := by
  unfold valid
  simp only [seqs]
  refine RelCT.seq (piece (G := StA) [] loads_taint (fun _ _ h => h.run) (fun _ _ _ _ _ _ _ _ h => nomatch h)
    fun _ _ h => loads_ok h) ?_
  refine RelCT.seq (piece (G := fun σ u => StA σ u ∧ u.z = decide (BalCv σ)) [] shapeCv_taint
    (fun _ _ h => h.base.run) (fun _ _ _ _ _ _ _ _ h => nomatch h) fun _ _ h => shapeCv_ok h) ?_
  refine RelCT.seq (R := Lift FJ) (RelCT.ite (fun s t ⟨σ₁, σ₂, p, h₁, h₂⟩ => ?_) ?_ ?_) ?_
  · show some s.z = some t.z
    rw [h₁.2, h₂.2]
    simp only [BalCv, cvPl, cvQl, cvW, cvK, p.args 3 (by decide), p.args 5 (by decide), p.args 7 (by decide)]
  · exact (midW_ct.mono (fun s t ⟨⟨σ₁, σ₂, p, h₁, h₂⟩, hz⟩ => by
      have z₁ : s.z = true := Option.some.inj hz
      have b₁ : BalCv σ₁ := of_decide_eq_true (h₁.2 ▸ z₁)
      have b₂ : BalCv σ₂ := by
        obtain ⟨l1, l2, l3⟩ := b₁
        simp only [BalCv, cvPl, cvQl, cvW, cvK, ← p.args 3 (by decide), ← p.args 5 (by decide),
          ← p.args 7 (by decide)]
        exact ⟨l1, l2, l3⟩
      exact ⟨σ₁, σ₂, p, ⟨h₁.1, b₁⟩, ⟨h₂.1, b₂⟩⟩) fun _ _ h => h).mono (fun _ _ h => h)
      fun _ _ h => Lift.mono (fun _ _ h => ⟨_, _, h.1⟩) h
  · exact midD_ct.mono (fun _ _ ⟨h, _⟩ => Lift.mono (fun _ _ h => h.1) h) fun _ _ h => h
  refine RelCT.seq (piece (G := F7) [] glue_taint (fun _ _ ⟨_, _, h⟩ => h.base.run)
    (fun _ _ _ _ _ _ _ _ h => nomatch h)
    fun _ _ ⟨_, _, h⟩ => WP.mono (glue_ok h) fun _ ⟨b, w, p10, p12, k⟩ =>
      ⟨b, w, p10, p12, WP.mono k fun _ ⟨_, _, o⟩ => o.done⟩) ?_
  exact piece [.r7, .r8, .r9, .r10, .r12] stores_taint (fun _ _ h => h.1.run)
    (fun _ _ _ _ p h₁ h₂ => by
      obtain ⟨e7, e8, e9⟩ := ws_regs p h₁.2.1 h₂.2.1
      have e10 : _ = _ := (h₁.2.2.1.trans p.r0).trans h₂.2.2.1.symm
      have e12 : _ = _ := (h₁.2.2.2.1.trans p.r2).trans h₂.2.2.2.1.symm
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl | rfl)
      exacts [e7, e8, e9, e10, e12])
    fun _ _ h => h.2.2.2.2

/-- Entry: the initial state itself. -/
abbrev FE (σ s : State) : Prop := s = σ ∧ CvPre σ
abbrev GE (σ u : State) : Prop := Base σ u ∧ u.gpr .r0 = σ.gpr .r0 ∧ u.gpr .r3 = σ.gpr .r2 ∧
  u.z = Spec.Rsa.modulusValid (Spec.Rsa.os2ip (nBytes σ)) (cvK σ)

theorem code_ct [VG.Proof.Rsa.Arm.Keys.InvLaw] {um : Bool} : RelCT isa (Lift FE) (code um) fun _ _ => True := by
  refine RelCT.seq (piece (G := GE) [.r0, .r1, .r2, .r3] entry_taint
    (fun _ _ ⟨e, h⟩ => by subst e; exact ⟨h, rfl, rfl, fun _ _ => rfl⟩)
    (fun _ _ _ _ p ⟨e₁, _⟩ ⟨e₂, _⟩ => by
      subst e₁ e₂
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl)
      exacts [p.r0, p.r1, p.r2, p.r3])
    fun _ _ ⟨e, h⟩ => by
      subst e; exact WP.mono (entry_ok h) fun _ ⟨b, _, r0, r3, _, z⟩ => ⟨b, r0, r3, z⟩) ?_
  refine RelCT.seq (R := Lift Done) (RelCT.ite (fun s t ⟨σ₁, σ₂, p, h₁, h₂⟩ => ?_) ?_ ?_) ?_
  · have eK : cvK σ₁ = cvK σ₂ := by simp only [cvK, p.args 3 (by decide)]
    show some s.z = some t.z
    rw [h₁.2.2.2, h₂.2.2.2, p.n, eK]
  · exact valid_ct.mono (fun _ _ ⟨h, _⟩ => Lift.mono (fun _ _ h => h.1) h) fun _ _ h => h
  · refine (piece (F := fun σ s => Base σ s ∧ s.gpr .r0 = σ.gpr .r0 ∧ s.gpr .r3 = σ.gpr .r2) (G := Done)
      [.r0, .r3] fail_taint (fun _ _ h => h.1.run) (fun _ _ _ _ p h₁ h₂ => ?_)
      fun _ _ h => WP.mono (fail_ok h.1 h.2.1 h.2.2) fun _ h => h.1).mono
      (fun _ _ ⟨h, _⟩ => Lift.mono (fun _ _ h => ⟨h.1, h.2.1, h.2.2.1⟩) h) fun _ _ h => h
    have e0 : _ = _ := (h₁.2.1.trans p.r0).trans h₂.2.1.symm
    have e3 : _ = _ := (h₁.2.2.trans p.r2).trans h₂.2.2.symm
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    exacts [e0, e3]
  · exact (piece (G := fun _ _ => True) [] restore_taint (fun _ _ h => h.run)
      (fun _ _ _ _ _ _ _ _ h => nomatch h) fun _ _ h => WP.mono (restore_ok h) fun _ _ => trivial).mono
      (fun _ _ h => h) fun _ _ _ => trivial

theorem cv_contract_ct [VG.Proof.Rsa.Arm.Keys.InvLaw] {um : Bool} :
    ConstantTime isa (Spec.Rsa.crtValuesContract abi 0).pre (Spec.Rsa.crtValuesContract abi 0).pub (code um) := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  have is := cv_pre s hs
  have it := cv_pre t ht
  sig_pub [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at hp
  obtain ⟨sp, bytes, p0, p1, p2, p3, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := hp
  have nb : nBytes s = nBytes t := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 bytes
  have args : ∀ i < 12, stackArg s i = stackArg t i := fun i hi =>
    match i, hi with
    | 0, _ => a0 | 1, _ => a1 | 2, _ => a2 | 3, _ => a3 | 4, _ => a4 | 5, _ => a5
    | 6, _ => a6 | 7, _ => a7 | 8, _ => a8 | 9, _ => a9 | 10, _ => a10 | 11, _ => a11
    | _ + 12, h => absurd h (by omega_using [])
  exact (code_ct (um := um) s t tr1 tr2 u v ⟨s, t, ⟨sp, nb, p0, p1, p2, p3, args⟩, ⟨rfl, is⟩, ⟨rfl, it⟩⟩ e1 e2).1

end VG.Proof.Rsa.Arm.CrtValues
