module

public import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTPoint
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Contract
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Contract
import VerifiedGarbage.Proof.Ffdh.Arm.Block
meta import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Geometry
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Geometry
import VerifiedGarbage.Proof.Bignum.Arm.RestoreSlots
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.FinishHead
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Outputs
public import VerifiedGarbage.Proof.Ffdh.Arm.Output
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Regions
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Memory
import VerifiedGarbage.Proof.Framework.Arm.Frame

/-! ### `Ffdh.Arm.KeySearch.Finish`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.KeySearch.FinishMemory`, which this module and modules that import it used -/

section

/-! Storing the consumed-byte count preserves the key pair, retry sampling,
and the saved registers needed for the controller's return. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Mont

structure ResultPost (p : KeyPublic sampling) (result : Spec.Ffdh.KeySearchResult) (s : State) : Prop where
  status : s.gpr .r0 = BitVec.ofNat 32 result.status
  output : KeyOutput p result s.mem
  policy : Spec.Rsa.wordsAt s.mem (State.addr p.control) 4 =
    [BitVec.ofNat 64 result.retries.keys, BitVec.ofNat 64 result.retries.scalars,
      BitVec.ofNat 64 p.len, BitVec.ofNat 64 (if result.status = 0 then p.len else 0)]
  used : Spec.Rsa.wordsAt s.mem (State.addr p.up) 1 = [BitVec.ofNat 64 result.used]

theorem KeyInput.used_separate {p : KeyPublic sampling} {s : State} (h : KeyInput p s) :
    (rX p).Disjoint (rUsed p) ∧ (rY p).Disjoint (rUsed p) ∧ (rControl p).Disjoint (rUsed p) := by
  have pairs := h.layout.pairwise
  rw [← h.layout.wr, h.write_regions] at pairs
  have indexed := List.pairwise_iff_getElem.mp pairs
  exact ⟨indexed 0 2 (by simp) (by simp) (by decide),
    indexed 1 2 (by simp) (by simp) (by decide),
    (indexed 2 4 (by simp) (by simp) (by decide)).symm⟩

theorem KeyInput.saved_used {p : KeyPublic sampling} {s : State} (h : KeyInput p s) :
    (rSaved p).Disjoint (rUsed p) :=
  (h.stack_separate (r := rUsed p) (by rw [h.write_regions]; simp)).sub_left
    (FrameStack.belowA_sub (by cases sampling <;> decide : 24 ≤ (stackUse sampling)) h.bounds.stackFits)

theorem KeyDone.used_buffer {p : KeyPublic sampling} {original s : State} {result : Spec.Ffdh.KeySearchResult}
    (h : KeyDone p original result s) : OutputBuffer p.up 8 s := by
  refine ⟨h.input.bounds.usedFit, ⟨rUsed p, ?_, Region.contains_self _ _⟩⟩
  rw [h.wr, h.input.write_regions]
  simp

theorem KeyDone.output_after_used {p : KeyPublic sampling} {original s : State} {result : Spec.Ffdh.KeySearchResult}
    {m : Mem} (h : KeyDone p original result s) (frame : Frame [rUsed p] s.mem m) :
    KeyOutput p result m := by
  have xeq := bytesAt_frame (r := rX p) frame (by simpa using h.input.used_separate.1)
    (by change p.len ≤ 2 ^ 64; have := h.input.bounds.maxLength; omega_using [this])
  have yeq := bytesAt_frame (r := rY p) frame (by simpa using h.input.used_separate.2.1)
    (by change p.len ≤ 2 ^ 64; have := h.input.bounds.maxLength; omega_using [this])
  have before := h.output
  cases outcome : result.outcome <;> simp only [KeyOutput, outcome] at before ⊢ <;>
    exact ⟨xeq.trans before.1, yeq.trans before.2⟩

theorem KeyDone.policy_after_used {p : KeyPublic sampling} {original s : State} {result : Spec.Ffdh.KeySearchResult}
    {m : Mem} (h : KeyDone p original result s) (frame : Frame [rUsed p] s.mem m) :
    Spec.Rsa.wordsAt m (State.addr p.control) 4 = Spec.Rsa.wordsAt s.mem (State.addr p.control) 4 := by
  unfold Spec.Rsa.wordsAt
  apply List.map_congr_left
  intro j hj
  have bound : j < 4 := List.mem_range.mp hj
  exact frame.readW (r := rControl p) (Offset.contains_base _ (by omega_using [bound]) (by omega_using [bound]))
    (by simpa using h.input.used_separate.2.2) (by decide)

/-- The buffers the controller reports in lie apart from its saved registers' frame. -/
theorem KeyInput.saved_separate {p : KeyPublic sampling} {s : State} (h : KeyInput p s) :
    (rX p).Disjoint (rSaved p) ∧ (rY p).Disjoint (rSaved p) ∧ (rControl p).Disjoint (rSaved p) ∧
      (rUsed p).Disjoint (rSaved p) := by
  have sub := FrameStack.belowA_sub (by cases sampling <;> decide : 24 ≤ (stackUse sampling)) h.bounds.stackFits
  exact ⟨((h.stack_separate (r := rX p) (by rw [h.write_regions]; simp)).sub_left sub).symm,
    ((h.stack_separate (r := rY p) (by rw [h.write_regions]; simp)).sub_left sub).symm,
    ((h.stack_separate (r := rControl p) (by rw [h.write_regions]; simp)).sub_left sub).symm,
    h.saved_used.symm⟩

theorem KeyOutput.of_frame {p : KeyPublic sampling} {result : Spec.Ffdh.KeySearchResult} {m m' : Mem}
    {rs : List Region} (before : KeyOutput p result m) (frame : Frame rs m m')
    (hx : ∀ w ∈ rs, (rX p).Disjoint w) (hy : ∀ w ∈ rs, (rY p).Disjoint w) (fit : p.len ≤ 2 ^ 64) :
    KeyOutput p result m' := by
  have xeq := bytesAt_frame (r := rX p) frame hx fit
  have yeq := bytesAt_frame (r := rY p) frame hy fit
  cases outcome : result.outcome <;> simp only [KeyOutput, outcome] at before ⊢ <;>
    exact ⟨xeq.trans before.1, yeq.trans before.2⟩

theorem wordsAt_of_frame {m m' : Mem} {rs : List Region} (frame : Frame rs m m') {a : Addr} {n : Nat}
    (hd : ∀ w ∈ rs, (⟨a, 8 * n⟩ : Region).Disjoint w) (fit : 8 * n < 2 ^ 64) :
    Spec.Rsa.wordsAt m' a n = Spec.Rsa.wordsAt m a n := by
  unfold Spec.Rsa.wordsAt
  apply List.map_congr_left
  intro j hj
  have bound : j < n := List.mem_range.mp hj
  exact frame.readW (r := ⟨a, 8 * n⟩) (Offset.contains_base _ (by omega_using [bound]) (by omega_using [bound, fit]))
    hd (by decide)

end VG.Proof.Ffdh.Arm.KeySearch

end

end

/-! The native controller writes its result and restores the complete AAPCS
callee-saved register set before its final frame pop. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm

def finishRestoreSlots : List (Reg × Nat) := [(.r9, 4), (.r10, 8), (.r11, 12), (.lr, 20)]

theorem finish_ok {p : KeyPublic sampling} {original s : State} {result : Spec.Ffdh.KeySearchResult}
    (h : KeyDone p original result s) :
    WP isa (.block VG.Impl.Ffdh.Arm.KeySearch.finish) s fun t =>
      ∀ m u, Frame [⟨State.addr (original.sp - BitVec.ofNat 32 24), 24⟩] t.mem m →
        abiPreserved original { popped .r4 24 t with mem := m, unknowns := u } ∧
          ResultPost p result { popped .r4 24 t with mem := m, unknowns := u } := by
  change WP isa (.block ([VG.Impl.Ffdh.Arm.KeySearch.ldf .r1 15, VG.Impl.Ffdh.Arm.KeySearch.ldf .r2 11,
    VG.Impl.Ffdh.Arm.KeySearch.ldf .r0 14, .mov .r3 (.imm 0), .str .r2 .r1 0, .str .r3 .r1 4] ++
    finishRestoreSlots.map (fun e => Instr.ldrSp e.1 e.2))) s _
  rw [WP.block_append_iff]
  refine WP.mono (finishHead_ok s h.controller h.used_buffer h.usedPtr h.used h.status) ?_
  rintro u ⟨⟨status, mem⟩, rest⟩
  have frame : Frame [rUsed p] s.mem u.mem := by rw [mem]; exact usedMem_frame _ _ _
  have saved : Spill.Saved u.mem (State.addr u.sp) original.gpr savedSlots := by
    rw [rest.sp, h.sp]
    apply h.saved.frame (lo := 0) (hi := 24) (by decide) frame
    simpa using h.input.saved_used
  have read : InRegions (u.rd ++ u.wr) (State.addr u.sp) 24 := by
    refine ⟨⟨State.addr u.sp, 24⟩, List.mem_append_right _ ?_, Region.contains_self _ _⟩
    rw [rest.wr, rest.sp, h.sp, h.wr]
    exact List.mem_cons_self
  have fit : u.sp.toNat + 24 ≤ 2 ^ 32 := by
    rw [rest.sp, h.sp, FrameStack.sub_toNat' (by have := h.input.bounds.stackFits; have min := stackUse_min sampling; omega_using [this, min])]
    have := p.sp.isLt
    omega_using []
  refine WP.mono (restoreSlots_ok finishRestoreSlots u original.gpr (by decide) fit read
    (by intro e he
        simp only [finishRestoreSlots, List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl | rfl <;> dsimp only <;> decide)
    (by intro e he
        apply saved e
        simp only [finishRestoreSlots, List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl | rfl <;> simp [savedSlots])) ?_
  rintro t ⟨restored, memT, restT⟩ m₀ u₀ hfl
  have spP : p.sp = original.sp := by rw [← h.input.2.1]; rfl
  have lost : Frame [rSaved p] u.mem m₀ := by
    show Frame [⟨State.addr (p.sp - BitVec.ofNat 32 24), 24⟩] u.mem m₀
    rw [spP, ← memT]; exact hfl
  have sep := h.input.saved_separate
  have fitLen : p.len ≤ 2 ^ 64 := by have := h.input.bounds.maxLength; omega_using [this]
  have popped4 : (popped .r4 24 t).gpr .r4 = original.gpr .r4 := by
    change t.mem.readW (State.addr t.sp) 32 = _
    rw [memT, restT.sp]
    simpa only [BitVec.add_zero] using saved (.r4, 0) (by simp [savedSlots])
  have kept (r : Reg) (member : r ∈ [.r5, .r6, .r7, .r8]) :
      (popped .r4 24 t).gpr r = original.gpr r := by
    rw [popped_gpr (by revert r member; decide)]
    exact (restT.gpr r (by revert r member; decide)).trans
      ((rest.gpr r (by revert r member; decide)).trans (h.kept r member))
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩ <;> dsimp only
  · intro r hr
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact popped4
    · exact kept .r5 (by simp)
    · exact kept .r6 (by simp)
    · exact kept .r7 (by simp)
    · exact kept .r8 (by simp)
    · rw [popped_gpr (by decide : Reg.r9 ≠ .r4)]; exact restored (.r9, 4) (by simp [finishRestoreSlots])
    · rw [popped_gpr (by decide : Reg.r10 ≠ .r4)]; exact restored (.r10, 8) (by simp [finishRestoreSlots])
    · rw [popped_gpr (by decide : Reg.r11 ≠ .r4)]; exact restored (.r11, 12) (by simp [finishRestoreSlots])
    · rw [popped_gpr (by decide : Reg.lr ≠ .r4)]; exact restored (.lr, 20) (by simp [finishRestoreSlots])
  · rw [popped_sp, restT.sp, rest.sp, h.sp, BitVec.sub_add_cancel]
    rw [← h.input.2.1]
    rfl
  · rw [popped_gpr (by decide : Reg.r0 ≠ .r4)]
    exact (restT.gpr .r0 (by simp [finishRestoreSlots])).trans status
  · exact (h.output_after_used frame).of_frame lost (by simpa using sep.1) (by simpa using sep.2.1) fitLen
  · rw [wordsAt_of_frame (n := 4) lost (by
      simp only [List.mem_singleton, forall_eq]
      exact sep.2.2.1.sub_left fun _ hc => by simp only [Region.Contains] at hc ⊢; omega_using [hc]) (by decide)]
    exact (h.policy_after_used frame).trans h.policy
  · rw [wordsAt_of_frame (n := 1) lost (by simpa using sep.2.2.2) (by decide), mem]
    exact usedMem_words _ _ _ (by have := h.used_le; have := h.input.bounds.randomFits; omega_arith)

end VG.Proof.Ffdh.Arm.KeySearch

end

end

/-! The native return path uses public control/output/stack addresses;
its consumed-byte count and saved register values do not affect timing. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Bignum.Arm

def KeyCTDone (p : KeyPublic sampling) (s : State) : Prop := ∃ original result, KeyDone p original result s

private theorem done_pins : Pins (KeyCTDone (sampling := sampling)) [.r4] := by
  intro p s t ⟨_, _, h₁⟩ ⟨_, _, h₂⟩ r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact h₁.pointer.trans h₂.pointer.symm

private theorem finish_pointer (p : KeyPublic sampling) (s : State) (h : KeyCTDone p s) :
    WP isa (.block [VG.Impl.Ffdh.Arm.KeySearch.ldf .r1 15, VG.Impl.Ffdh.Arm.KeySearch.ldf .r2 11,
      VG.Impl.Ffdh.Arm.KeySearch.ldf .r0 14]) s (fun t => t.gpr .r1 = p.up) := by
  obtain ⟨_, _, finished⟩ := h
  have controller := finished.controller
  have pointer := finished.usedPtr
  unfold VG.Impl.Ffdh.Arm.KeySearch.ldf lowWord at *
  ffrun [controller.addr (by decide : 15 < 16), controller.addr (by decide : 11 < 16),
    controller.addr (by decide : 14 < 16), controller.read (by decide : 15 < 16),
    controller.read (by decide : 11 < 16), controller.read (by decide : 14 < 16), pointer]

theorem finish_ct : RelCT isa (Two (KeyCTDone (sampling := sampling))) (.block VG.Impl.Ffdh.Arm.KeySearch.finish) (fun _ _ => True) := by
  have stores : RelCT isa (Two fun (p : KeyPublic sampling) s => s.gpr .r1 = p.up)
      (.block [.mov .r3 (.imm 0), .str .r2 .r1 0, .str .r3 .r1 4]) (fun s t => s.sp = t.sp) := by
    apply relCT_keep_sp (two_taint [.r1] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr
      subst r
      exact h₁.trans h₂.symm) (by taint_decide))
    exact fun _ _ ⟨_, _, _, sp⟩ => sp
  change RelCT isa _ (.block (([VG.Impl.Ffdh.Arm.KeySearch.ldf .r1 15,
    VG.Impl.Ffdh.Arm.KeySearch.ldf .r2 11, VG.Impl.Ffdh.Arm.KeySearch.ldf .r0 14] ++
      [.mov .r3 (.imm 0), .str .r2 .r1 0, .str .r3 .r1 4]) ++
        [.ldrSp .r9 4, .ldrSp .r10 8, .ldrSp .r11 12, .ldrSp .lr 20])) _
  refine RelCT.block_append (RelCT.seq (RelCT.block_append (RelCT.seq
    (two_piece [.r4] done_pins (by taint_decide) finish_pointer) stores)) ?_)
  exact (stackLoads_ct [(.r9, 4), (.r10, 8), (.r11, 12), (.lr, 20)]).mono (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Ffdh.Arm.KeySearch
