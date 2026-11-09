module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillCTLoop
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillFinish
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.OutputCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Memory
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillCTLoop
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillFinish
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.OutputCT
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # Timing of the refillable-tape search's end on AArch64

`finish`: the words written to `used` and `state`, at the pointers the
controller's words hold, which are public (`PtrsAt`), loaded once into `x14`
and `x15`; the output; the status. Every branch is on the controller's
status and the octets left, functions of its public state. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation.Refill
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.Dsa.AArch64.Generation VG.Proof.MlKem.AArch64

/-- The status the controller ends with (`exitStatus`). -/
def ctxExit (p : GenerationContext) (n c : Nat) : Nat :=
  if n = 0 then 2 else if p.rand.bytes.length - c < p.geo.qLen then 0 else
    match ctxResult p c with
    | some (some _, _) => 1
    | _ => 0

theorem exitStatus_eq {pBytes : Nat} {s₀ : State} (h : RefillABI pBytes s₀) (n c : Nat) :
    exitStatus h n c = ctxExit (refillContext h) n c := rfl

theorem LoopDone.keep {pBytes : Nat} {s₀ : State} {h : RefillABI pBytes s₀} {v : State} {n c : Nat} {t t' : State}
    (hd : LoopDone h v n c t) (hmem : t'.mem = t.mem) {rs : List Reg} (hk : Keep rs t t') : LoopDone h v n c t' := by
  obtain ⟨hs, W, hin, hm, c0, c1, fv, rd, wr, h19, c3, cases⟩ := hd
  refine ⟨hs, W, hin, genMem_keep hm hmem hk, by rw [ctlWord_eq_of_mem hmem]; exact c0,
    by rw [ctlWord_eq_of_mem hmem]; exact c1, by rw [hmem]; exact fv, hk.rd.trans rd, hk.wr.trans wr, h19,
    by rw [ctlWord_eq_of_mem hmem]; exact c3, ?_⟩
  rw [ctlWord_eq_of_mem hmem, hmem]
  exact cases

/-- After the pointers and the status are loaded. -/
def ResStarted (pBytes : Nat) (P : LoopPub) (t : State) : Prop :=
  DoneAt pBytes P t ∧ t.gpr .x14 = P.st ∧ t.gpr .x15 = P.us ∧ t.gpr .x3 = BitVec.ofNat 64 (ctxExit P.ctx P.n P.c)

theorem resStarted_wp {pBytes : Nat} {P : LoopPub} {t : State} (hd : DoneAt pBytes P t) :
    WP isa (.block Impl.Dsa.AArch64.Generation.Refill.resultsStart) t (ResStarted pBytes P) := by
  obtain ⟨s₀, h, v, hc, ⟨p7, p2⟩, hv, hl⟩ := hd
  have hl' := hl
  obtain ⟨hs, W, _, hm, c0, c1, _, _, wr, h19, _, _⟩ := hl
  obtain ⟨V, R⟩ := hm.rep
  have hv' : (⟨(refillGeometry h).F, 480⟩ : Region) ∈ t.wr := by rw [wr, hv]; exact List.mem_cons_self ..
  refine WP.mono (resultsStart_run hm.layout R hv') fun t₁ ⟨⟨x14, x15, x3, m₁⟩, k₁⟩ =>
    ⟨⟨s₀, h, v, hc, ⟨p7, p2⟩, hv, hl'.keep m₁ k₁⟩, x14.trans (c1.trans p7), x15.trans (c0.trans p2), ?_⟩
  rw [x3, h19, exitStatus_eq, hc]

/-- After a seed that ran out: the octets left reach the budget, or not. -/
def RanOut (pBytes : Nat) (P : LoopPub) (t : State) : Prop :=
  t.gpr .x14 = P.st ∧ t.gpr .x15 = P.us ∧
    t.gpr .x12 = BitVec.ofNat 64 (if 32769 * pBytes ≤ P.ctx.rand.bytes.length - P.c then 1 else 0)

theorem ranOut_wp {pBytes : Nat} {P : LoopPub} {t : State}
    (hr : ResStarted pBytes P t ∧ isa.eval (.zero .x .x3) t = some true) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.Refill.ranOutCheck pBytes)) t (RanOut pBytes P) := by
  obtain ⟨⟨⟨s₀, h, v, hc, -, hv, hl⟩, x14, x15, x3⟩, ev⟩ := hr
  obtain ⟨hs, W, _, hm, _, _, _, _, wr, h19, c3, cases⟩ := hl
  have hp3 : pBytes = 128 ∨ pBytes = 256 ∨ pBytes = 384 := by
    have := h.lengths; unfold Spec.Dsa.generationLengthsValid at this; omega
  have hz : BitVec.ofNat 64 (ctxExit P.ctx P.n P.c) = 0 := by
    simpa [eval, State.read, x3] using ev
  have w0 : W 19 = 0 := by rw [h19, exitStatus_eq, hc]; exact hz
  have hcl : P.c ≤ (randTape h).bytes.length := by
    rcases cases with ⟨e, _⟩ | ⟨_, hc', _⟩ | ⟨e, _⟩
    · rw [w0] at e; cases e
    · exact hc'
    · rw [w0] at e; cases e
  have h15 : W 15 = BitVec.ofNat 64 (randTape h).bytes.length :=
    (hm.slots 15 (by simp [generationSlots])).trans ((refillContext h).withHs hs).randLengthSlot
  obtain ⟨V, R⟩ := hm.rep
  have hv' : (⟨(refillGeometry h).F, 480⟩ : Region) ∈ t.wr := by rw [wr, hv]; exact List.mem_cons_self ..
  refine WP.mono (ranOutCheck_run hm.layout R hv' c3 h15 hcl (randTape h).size hp3)
    fun t₂ ⟨⟨_, _, _, x12, _⟩, k₂⟩ => ⟨(k₂.gpr .x14 (by decide)).trans x14, (k₂.gpr .x15 (by decide)).trans x15, ?_⟩
  rw [x12, ← hc]
  rfl

/-- After the status less one. -/
def Decided (P : LoopPub) (t : State) : Prop :=
  t.gpr .x14 = P.st ∧ t.gpr .x15 = P.us ∧
    isa.eval (.zero .x .x3) t = some (BitVec.ofNat 64 (ctxExit P.ctx P.n P.c) == 1)

theorem decided_wp {pBytes : Nat} {P : LoopPub} {t : State} (hr : ResStarted pBytes P t) :
    WP isa (.block [.subImm .x .x3 .x3 1]) t (Decided P) := by
  obtain ⟨-, x14, x15, x3⟩ := hr
  exact WP.mono minusOne_run fun t₂ ⟨⟨ev, _⟩, k₂⟩ =>
    ⟨(k₂.gpr .x14 (by decide)).trans x14, (k₂.gpr .x15 (by decide)).trans x15, by rw [← x3]; exact ev⟩

theorem pins_ptrs {α : Type} {Φ : α → State → Prop} (st us : α → BitVec 64)
    (h : ∀ a t, Φ a t → t.gpr .x14 = st a ∧ t.gpr .x15 = us a) : Pins Φ [.x14, .x15] := by
  intro a s t hs ht r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (h a s hs).1.trans (h a t ht).1.symm
  · exact (h a s hs).2.trans (h a t ht).2.symm

theorem results_ct_of (pBytes : Nat) {hc₁ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs []) (.block (Impl.Dsa.AArch64.Generation.Refill.ranOutCheck pBytes)) hc₁).isSome =
      true) :
    RelCT isa (Two (DoneAt pBytes)) (Impl.Dsa.AArch64.Generation.Refill.results pBytes) (fun _ _ => True) := by
  unfold Impl.Dsa.AArch64.Generation.Refill.results
  refine RelCT.seq (two_piece [] (nopin _) (by taint_decide) fun _ _ h => resStarted_wp h) ?_
  refine two_ite (fun P s t ⟨_, _, _, hs⟩ ⟨_, _, _, ht⟩ => by simp only [eval, State.read, hs, ht]) ?_ ?_
  · refine RelCT.seq (two_piece [] (nopin _) ht₁ fun _ _ h => ranOut_wp h) ?_
    refine two_ite (fun P s t ⟨_, _, hs⟩ ⟨_, _, ht⟩ => by simp only [eval, State.read, hs, ht]) ?_ ?_
    · exact two_taint _ (pins_ptrs LoopPub.st LoopPub.us fun _ _ h => ⟨h.1.1, h.1.2.1⟩) (by taint_decide)
    · exact two_taint _ (pins_ptrs LoopPub.st LoopPub.us fun _ _ h => ⟨h.1.1, h.1.2.1⟩) (by taint_decide)
  · refine RelCT.seq (two_piece [] (nopin _) (by taint_decide) fun _ _ h => decided_wp h.1) ?_
    refine two_ite (fun P s t ⟨_, _, hs⟩ ⟨_, _, ht⟩ => hs.trans ht.symm) ?_ ?_
    · exact two_taint _ (pins_ptrs LoopPub.st LoopPub.us fun _ _ h => ⟨h.1.1, h.1.2.1⟩) (by taint_decide)
    · exact two_taint _ (pins_ptrs LoopPub.st LoopPub.us fun _ _ h => ⟨h.1.1, h.1.2.1⟩) (by taint_decide)

/-- The output's public state after `results`. -/
def LoopPub.output (P : LoopPub) : OutputPublic := ⟨P.ctx, BitVec.ofNat 64 (ctxExit P.ctx P.n P.c) == (1#64)⟩

theorem results_output {pBytes : Nat} {P : LoopPub} {t : State} (hd : DoneAt pBytes P t) :
    WP isa (Impl.Dsa.AArch64.Generation.Refill.results pBytes) t (OutputBefore P.output) := by
  obtain ⟨ctx, n, c, st, us⟩ := P
  obtain ⟨s₀, h, v, hc, -, hv, hl⟩ := hd
  change refillContext h = ctx at hc
  refine WP.mono (results_ok h hv hl) fun t' D => ?_
  obtain ⟨hs, W, -, -, -, -, -, -, hm, h19, -⟩ := D
  obtain ⟨V, W', L, R, h5, h6, h7, e⟩ := outputBefore_of hm (a := BitVec.ofNat 64 (ctxExit ctx n c) == (1#64))
    (by rw [h19, exitStatus_eq, hc])
  subst hc
  exact ⟨V, W', L, R, h5, h6, h7, e⟩

theorem finish_ct (pBytes : Nat) (hp : pBytes = 128 ∨ pBytes = 256 ∨ pBytes = 384) :
    RelCT isa (Two (DoneAt pBytes)) (Impl.Dsa.AArch64.Generation.Refill.finish pBytes) (fun _ _ => True) := by
  have results : RelCT isa (Two (DoneAt pBytes)) (Impl.Dsa.AArch64.Generation.Refill.results pBytes)
      (Two OutputBefore) := by
    refine (two_post (Ψ := fun P t => OutputBefore P.output t) ?_ fun _ _ h => results_output h).mono
      (fun _ _ h => h) ?_
    · rcases hp with rfl | rfl | rfl <;> exact results_ct_of _ (by taint_decide)
    · rintro s t ⟨P, hs, ht, hsp⟩
      exact ⟨P.output, hs, ht, hsp⟩
  unfold Impl.Dsa.AArch64.Generation.Refill.finish
  simp only [VG.Impl.Bignum.AArch64.seqs]
  exact RelCT.seq results (RelCT.seq (two_sp finishOutput_ct) (two_taint [] (nopin _) (by taint_decide)))

end VG.Proof.Dsa.AArch64.Generation.Refill
