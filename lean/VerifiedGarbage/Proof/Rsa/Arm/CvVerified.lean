module

public import VerifiedGarbage.Proof.Rsa.Arm.InvLaw
public import VerifiedGarbage.Proof.Rsa.Arm.CvWords
public import VerifiedGarbage.Proof.Rsa.Arm.CvFail
public import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
public import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
import VerifiedGarbage.Proof.Rsa.Arm.CvTaint
import VerifiedGarbage.Proof.Rsa.Arm.CvTaintW
public import VerifiedGarbage.Proof.Rsa.Arm.KdDivCT
import VerifiedGarbage.Proof.Rsa.Arm.CvLoads
import VerifiedGarbage.Proof.Rsa.Arm.DivCT
import VerifiedGarbage.Proof.Rsa.Arm.InvParts
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Rsa.Arm.CrtValues
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Rsa.Contract
meta import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Rsa.Arm.KcBodyW
import VerifiedGarbage.Proof.Rsa.KeyCheckMath
import VerifiedGarbage.Proof.Rsa.Arm.CvSpec
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.UmaalArithmetic

/-! ### `Rsa.Arm.CvCT`, which only this module used -/

section

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

end

end

/-! ### `Rsa.Arm.CvCorrect`, which only this module used -/

section

/-! ### `Rsa.Arm.CvValid`, which only this module used -/

section

/-! # `vg_rsa_crt_values` on ARMv7: a valid modulus (`valid_ok`) -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CrtValues
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.CrtValues
open VG.Proof.Rsa.Arm.Keys VG.Proof.Bignum.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm

/-- What a valid modulus leaves. -/
def ValidPost (s0 t : State) : Prop := ∃ X₁ X₂ V R₂ R₃ X : Nat,
  (0 < cvP s0 → X₁ = cvN s0 / cvP s0 ∧ X₂ = cvN s0 % cvP s0) ∧
  (1 < cvM s0 → V = Nat.gcd (cvQ s0) (cvM s0) ∧ (cvM s0 : Int) ∣ (X : Int) * cvQ s0 - V ∧ X < cvM s0) ∧
  (0 < 2 * (cvP s0 / 2) → R₂ = cvD s0 % (2 * (cvP s0 / 2))) ∧
  (0 < 2 * (cvQ s0 / 2) → R₃ = cvD s0 % (2 * (cvQ s0 / 2))) ∧
  Outs s0 t (maskOf (cvP s0) (cvQ s0) X₁ X₂ V) R₂ R₃ X

theorem Outs.congr {s0 t : State} {c : Bool} {R₂ R₃ R₂' R₃' X : Nat} (o : Outs s0 t c R₂ R₃ X)
    (e₂ : c = true → R₂ = R₂') (e₃ : c = true → R₃ = R₃') : Outs s0 t c R₂' R₃' X := by
  cases c
  · exact ⟨o.done, o.ret, o.dp, o.dq, o.qi⟩
  · rw [← e₂ rfl, ← e₃ rfl]; exact o

/-- For a balanced key, `p q < 2^(32 w)`. -/
theorem pq_lt {s0 : State} (hB : BalCv s0) (hp : cvP s0 < 2 ^ (32 * (cvW s0 / 2)))
    (hq : cvQ s0 < 2 ^ (32 * (cvW s0 / 2))) : cvP s0 * cvQ s0 < 2 ^ (32 * cvW s0) := by
  have hW : (2 : Nat) ^ (32 * cvW s0) = 2 ^ (32 * (cvW s0 / 2)) * 2 ^ (32 * (cvW s0 / 2)) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [hW]; exact VG.Proof.Rsa.mul_lt_sq hp hq

/-- The mask of a balanced key's checks is that of the division of `n` by `p`. -/
theorem maskW_eq {s0 : State} (hm : Spec.Rsa.modulusValid (cvN s0) (cvK s0) = true) (hB : BalCv s0)
    (hp : cvP s0 < 2 ^ (32 * (cvW s0 / 2))) (hq : cvQ s0 < 2 ^ (32 * (cvW s0 / 2))) (V : Nat) :
    maskOf (cvP s0) (cvQ s0) (xW s0) 0 V = maskOf (cvP s0) (cvQ s0) (cvN s0 / cvP s0) (cvN s0 % cvP s0) V := by
  have hN := (VG.Proof.Rsa.modulusValid_facts hm).1
  simp only [xW, Nat.mod_eq_of_lt (pq_lt hB hp hq)]
  by_cases e : cvP s0 * cvQ s0 = cvN s0
  · obtain ⟨a, b, c⟩ := (pq_iff hN).mpr e
    simp only [e, ↓reduceIte, maskOf, VG.Proof.Rsa.CrtValues.maskOf, b, c]
  · have r : ¬(cvP s0 % 2 = 1 ∧ cvN s0 / cvP s0 = cvQ s0 ∧ cvN s0 % cvP s0 = 0) := fun h => e ((pq_iff hN).mp h)
    simp only [e, ↓reduceIte, maskOf, VG.Proof.Rsa.CrtValues.maskOf]
    rw [decide_eq_false (by omega_using []), decide_eq_false (fun ⟨a, b, c, _⟩ => r ⟨a, b, c⟩)]

/-- Under the mask, a balanced key's remainders by words are those modulo `p - 1` and `q - 1`. -/
theorem remW_eq {s0 : State} (hm : Spec.Rsa.modulusValid (cvN s0) (cvK s0) = true) (hB : BalCv s0)
    (hp : cvP s0 < 2 ^ (32 * (cvW s0 / 2))) (hq : cvQ s0 < 2 ^ (32 * (cvW s0 / 2))) {V : Nat}
    (w16 : 16 ≤ cvW s0) (hc : maskOf (cvP s0) (cvQ s0) (xW s0) 0 V = true) :
    VG.Proof.Rsa.fixT (cvW s0 / 2) (2 * (cvP s0 / 2)) = 2 * (cvP s0 / 2) ∧
      VG.Proof.Rsa.fixT (cvW s0 / 2) (2 * (cvQ s0 / 2)) = 2 * (cvQ s0 / 2) := by
  have e : cvP s0 * cvQ s0 = cvN s0 := by
    simp only [xW, Nat.mod_eq_of_lt (pq_lt hB hp hq), maskOf, VG.Proof.Rsa.CrtValues.maskOf,
      decide_eq_true_eq] at hc
    by_contra n
    simp [n] at hc
  obtain ⟨-, a, b⟩ := VG.Proof.Rsa.top_words hm rfl (by simp only [cvW] at w16; omega_using [w16]) hp hq e
  exact ⟨VG.Proof.Rsa.fixT_of_ge a, VG.Proof.Rsa.fixT_of_ge b⟩

theorem valid_ok [VG.Proof.Rsa.Arm.Keys.InvLaw] {um : Bool} {s0 s : State} (h : Base s0 s)
    (hm : Spec.Rsa.modulusValid (cvN s0) (cvK s0) = true) : WP isa (valid um) s (ValidPost s0) := by
  unfold valid
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (loads_ok h) fun t1 h1 => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (shapeCv_ok h1) fun t2 ⟨h2, z2⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  rw [show seqs [Code.block (ctx ++ [Instr.ldr .r10 .r8 sDp, Instr.ldr .r12 .r8 sDq]), stores] =
    .seq (.block glue) stores from rfl]
  refine WP.ite t2.z rfl (fun hz => ?_) (fun _ => ?_)
  · -- A balanced key.
    rw [z2] at hz
    have hB : BalCv s0 := of_decide_eq_true hz
    have hp : cvP s0 < 2 ^ (32 * (cvW s0 / 2)) :=
      bytes_lt_half (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]; exact hB.1) hB.2.2
    have hq : cvQ s0 < 2 ^ (32 * (cvW s0 / 2)) :=
      bytes_lt_half (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]; exact hB.2.1) hB.2.2
    refine WP.mono (midW_ok h2 hB) fun t3 ⟨h3, e2, e3⟩ => ?_
    refine WP.mono (finish_ok h3) fun t ⟨V, iV, outs⟩ => ?_
    refine ⟨_, _, V, _, _, _, fun _ => ⟨rfl, rfl⟩, iV, fun _ => rfl, fun _ => rfl, ?_⟩
    rw [← maskW_eq hm hB hp hq V]
    exact outs.congr (fun hc => by rw [e2, fP, (remW_eq hm hB hp hq h.pre.w16.1 hc).1])
      (fun hc => by rw [e3, fQ, (remW_eq hm hB hp hq h.pre.w16.1 hc).2])
  · -- Any key: `n` divided by `p`.
    unfold midD
    rw [wp_seqs_cons (List.cons_ne_nil _ _)]
    refine WP.mono (WP.seq_iff.mp (divN_ok h2)) fun u hu => ?_
    rw [wp_seqs_cons (List.cons_ne_nil _ _)]
    refine WP.mono hu fun t3 h3 => ?_
    rw [wp_seqs_cons (List.cons_ne_nil _ _), checks_eq]
    refine (wp_seqs_append (by unfold checksA invSetup; simp) (by unfold checksB; simp)).mpr
      (WP.mono (checksA_ok h3) fun t4 h4 => WP.mono (checksB_ok h4) fun t5 h5 => ?_)
    rw [wp_seqs_cons (List.cons_ne_nil _ _)]
    refine WP.mono (divP_ok h5) fun t6 h6 => ?_
    rw [wp_seqs_cons (List.cons_ne_nil _ _)]
    refine WP.mono (WP.seq_iff.mp (divQ_ok h6)) fun u' hu' => ?_
    refine WP.mono hu' fun t7 h7 => ?_
    refine WP.mono (finish_ok h7.toM) fun t ⟨V, iV, outs⟩ => ?_
    exact ⟨_, _, V, _, _, _, h3.div, iV, h7.dp, h7.dq, outs⟩

end VG.Proof.Rsa.Arm.CrtValues

end

end


/-! # `vg_rsa_crt_values` on ARMv7: correctness

`cv_ok`: from a state meeting the contract's precondition, the code returns
with the callee-saved registers and `sp` restored and the results of `crtKey`
written out (`CvPost`); `cv_contract_correct` states it as the contract does.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CrtValues
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.CrtValues
open VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm

/-- The results as the contract states them. -/
def CvPost (s0 t : State) : Prop :=
  abiPreserved s0 t ∧ Spec.Rsa.writtenAll t.mem
    [(State.addr (s0.gpr .r0), cvPl s0), (State.addr (s0.gpr .r2), cvQl s0),
      (State.addr (stackArg s0 0), cvPl s0)] (t.gpr .r0)
    ((Spec.Rsa.crtKey (nBytes s0) (pBytes s0) (qBytes s0) (dBytes s0)).map fun v => [v.1, v.2.1, v.2.2])

/-- The outputs of the valid branch are `crtKey`'s. -/
theorem written_valid {s0 t : State} {c : Bool} {R₂ R₃ X : Nat} (o : Outs s0 t c R₂ R₃ X)
    (e : Spec.Rsa.crtKey (nBytes s0) (pBytes s0) (qBytes s0) (dBytes s0) = if c then
      some (Spec.Rsa.i2osp (R₂ % 2 ^ (8 * cvPl s0)) (cvPl s0), Spec.Rsa.i2osp (R₃ % 2 ^ (8 * cvQl s0)) (cvQl s0),
        Spec.Rsa.i2osp (X % 2 ^ (8 * cvPl s0)) (cvPl s0)) else none) :
    Spec.Rsa.writtenAll t.mem
      [(State.addr (s0.gpr .r0), cvPl s0), (State.addr (s0.gpr .r2), cvQl s0),
        (State.addr (stackArg s0 0), cvPl s0)] (t.gpr .r0)
      ((Spec.Rsa.crtKey (nBytes s0) (pBytes s0) (qBytes s0) (dBytes s0)).map fun v => [v.1, v.2.1, v.2.2]) := by
  have r := o.ret; have dp := o.dp; have dq := o.dq; have qi := o.qi
  rw [e]
  cases c
  · simp only [Bool.false_eq_true, ↓reduceIte] at r dp dq qi ⊢
    refine ⟨r, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨dp, dq, qi⟩
  · simp only [↓reduceIte] at r dp dq qi ⊢
    refine ⟨r, ?_⟩
    simp only [List.map_cons, List.map_nil]
    rw [show Spec.Rsa.bytesAt t.mem (State.addr (s0.gpr .r0)) (cvPl s0) = outDp t.mem s0 from rfl,
      show Spec.Rsa.bytesAt t.mem (State.addr (s0.gpr .r2)) (cvQl s0) = outDq t.mem s0 from rfl,
      show Spec.Rsa.bytesAt t.mem (State.addr (stackArg s0 0)) (cvPl s0) = outQi t.mem s0 from rfl,
      dp, dq, qi]

theorem crtKey_valid {s0 : State} (pre : CvPre s0)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (nBytes s0)) (cvK s0) = true)
    {X₁ X₂ V R₂ R₃ X : Nat}
    (h₁ : 0 < cvP s0 → X₁ = cvN s0 / cvP s0 ∧ X₂ = cvN s0 % cvP s0)
    (h₂ : 1 < cvM s0 → V = Nat.gcd (cvQ s0) (cvM s0) ∧ (cvM s0 : Int) ∣ (X : Int) * cvQ s0 - V ∧
      X < cvM s0)
    (h₃ : 0 < 2 * (cvP s0 / 2) → R₂ = cvD s0 % (2 * (cvP s0 / 2)))
    (h₄ : 0 < 2 * (cvQ s0 / 2) → R₃ = cvD s0 % (2 * (cvQ s0 / 2))) :
    Spec.Rsa.crtKey (nBytes s0) (pBytes s0) (qBytes s0) (dBytes s0) =
      if maskOf (cvP s0) (cvQ s0) X₁ X₂ V then
      some (Spec.Rsa.i2osp (R₂ % 2 ^ (8 * cvPl s0)) (cvPl s0), Spec.Rsa.i2osp (R₃ % 2 ^ (8 * cvQl s0)) (cvQl s0),
        Spec.Rsa.i2osp (X % 2 ^ (8 * cvPl s0)) (cvPl s0)) else none := by
  have ln : (nBytes s0).length = cvK s0 := bytesAt_length _ _ _
  have lp : (pBytes s0).length = cvPl s0 := bytesAt_length _ _ _
  have lq : (qBytes s0).length = cvQl s0 := bytesAt_length _ _ _
  have e := crtKey_masked (nb := nBytes s0) (pb := pBytes s0) (qb := qBytes s0) (db := dBytes s0)
    (by rw [ln]; exact hv) (by rw [lp, ln]; exact pre.pl2) (by rw [lq, ln]; exact pre.ql2) h₁ h₂ h₃ h₄
  rw [lp, lq] at e
  exact e

theorem crtKey_invalid {s0 : State}
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (nBytes s0)) (cvK s0) = false) :
    Spec.Rsa.crtKey (nBytes s0) (pBytes s0) (qBytes s0) (dBytes s0) = none := by
  have ln : (nBytes s0).length = cvK s0 := bytesAt_length _ _ _
  unfold Spec.Rsa.crtKey
  simp only [ln, hv, Bool.false_eq_true, false_and, ↓reduceIte]

/-- What the branches leave for `restore`. -/
def CvMid (s0 t : State) : Prop := Done s0 t ∧ Spec.Rsa.writtenAll t.mem
  [(State.addr (s0.gpr .r0), cvPl s0), (State.addr (s0.gpr .r2), cvQl s0),
    (State.addr (stackArg s0 0), cvPl s0)] (t.gpr .r0)
  ((Spec.Rsa.crtKey (nBytes s0) (pBytes s0) (qBytes s0) (dBytes s0)).map fun v => [v.1, v.2.1, v.2.2])

theorem branches_ok [VG.Proof.Rsa.Arm.Keys.InvLaw] {um : Bool} {s0 s : State} (pre : CvPre s0) (hb : Base s0 s) (p0 : s.gpr .r0 = s0.gpr .r0)
    (p3 : s.gpr .r3 = s0.gpr .r2)
    (hz : s.z = Spec.Rsa.modulusValid (Spec.Rsa.os2ip (nBytes s0)) (cvK s0)) :
    WP isa (.ite .eq (valid um) fail) s (CvMid s0) := by
  refine WP.ite s.z rfl (fun hv => ?_) (fun hv => ?_)
  · rw [hz] at hv
    refine WP.mono (valid_ok hb hv) fun (t : State) ⟨X₁, X₂, V, R₂, R₃, X, h₁, h₂, h₃, h₄, o⟩ => ⟨o.done, ?_⟩
    exact written_valid o (crtKey_valid pre hv h₁ h₂ h₃ h₄)
  · refine WP.mono (fail_ok hb p0 p3) fun (t : State) ⟨d, r0, dp, dq, qi⟩ => ⟨d, ?_⟩
    rw [hz] at hv
    rw [crtKey_invalid hv]
    refine ⟨r0, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨dp, dq, qi⟩

theorem cv_ok [VG.Proof.Rsa.Arm.Keys.InvLaw] {um : Bool} {s0 : State} (pre : CvPre s0) :
    WP isa (code um) s0 (CvPost s0) := by
  refine WP.seq (WP.mono (entry_ok pre) fun (s : State) ⟨hb, _, p0, p3, _, hz⟩ =>
    WP.seq (WP.mono (branches_ok pre hb p0 p3 hz) fun (t : State) ⟨ht, w⟩ =>
      WP.mono (restore_ok ht) fun (u : State) ⟨hr, hsp, hm, h0⟩ => ⟨⟨hr, hsp⟩, ?_⟩))
  rw [hm, h0]; exact w

theorem cv_contract_correct [VG.Proof.Rsa.Arm.Keys.InvLaw] {um : Bool} (s : State) (h : (Spec.Rsa.crtValuesContract abi 0).pre s) :
    ∃ tr t, Exec isa (code um) s tr t ∧ abiPreserved s t ∧ (Spec.Rsa.crtValuesContract abi 0).post s t := by
  obtain ⟨tr, t, run, ⟨pres, w⟩⟩ := cv_ok (cv_pre s h)
  refine ⟨tr, t, run, pres, ?_⟩
  sig_post [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  rw [BitVec.setWidth_append_eq_right]
  exact w

end VG.Proof.Rsa.Arm.CrtValues

end

end


/-! # `vg_rsa_crt_values` on ARMv7 is verified against the shared RSA contract -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CrtValues
open VG VG.Arm VG.Impl.Rsa.Arm.CrtValues

/-- A 64-byte modulus, one-byte factors, exponent and outputs, the working
space at `0x4000`, and the stack arguments at `0x8000`. -/
def cvSatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 1 | .r2 => 0x1200 | .r3 => 1 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x11 else if a = 0x8004 then 1 else if a = 0x8009 then 0x20
    else if a = 0x800C then 0x40 else if a = 0x8011 then 0x30 else if a = 0x8014 then 1
    else if a = 0x8019 then 0x31 else if a = 0x801C then 1 else if a = 0x8021 then 0x32
    else if a = 0x8024 then 1 else if a = 0x8029 then 0x40 else if a = 0x802C then 0x20
    else if a = 0x802D then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x3100, 1⟩, ⟨0x3200, 1⟩, ⟨0x8000, 48⟩]
  wr := [⟨0x1000, 1⟩, ⟨0x1200, 1⟩, ⟨0x1100, 1⟩, ⟨0x4000, 8448⟩]

theorem cv_contract_sat : ∃ s, (Spec.Rsa.crtValuesContract abi 0).pre s := by
  sig_implies_sat [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argRegs, reduceClassify, Loc.val,
    State.addr]
    [cvSatState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid, Spec.Rsa.scratchWords]
    using cvSatState

/-- `vg_rsa_crt_values`, either variant of its inverse. -/
theorem crt_values_verified [VG.Proof.Rsa.Arm.Keys.InvLaw] {um : Bool} :
    Verified target (code um) (Spec.Rsa.crtValuesContract abi 0) :=
  ⟨cv_contract_correct, cv_contract_ct, cv_contract_sat⟩

/-- `vg_rsa_crt_values` (`um = false`) or `vg_rsa_crt_values_umaal` (`um`). -/
theorem crt_values_for_verified [VG.Proof.Rsa.Arm.Keys.InvLaw] (um : Bool) :
    Verified target (codeFor um) (Spec.Rsa.crtValuesContract abi 0) := by
  cases um
  · exact crt_values_verified
  · exact VG.Proof.Bignum.Arm.umaalArithmetic_verified crt_values_verified

end VG.Proof.Rsa.Arm.CrtValues
