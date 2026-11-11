module

public import VerifiedGarbage.Proof.Bignum.Arm.PrivPreModulus
public import VerifiedGarbage.Proof.Bignum.Arm.CrtInput
public import VerifiedGarbage.Proof.Bignum.Arm.PcPush
import VerifiedGarbage.Proof.Bignum.Arm.PublicPush
import VerifiedGarbage.Proof.Bignum.Arm.CrtCallStack
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block

/-! # The private CRT's frame around the precomputation's body

The precomputation runs the private CRT's own frame and entry, from a state
that is a call of the CRT (`CrtFnInput`) but for `pre`, which it writes past
the CRT's output.
-/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.PrivPreFn VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

/-- `pre` at the call of the CRT's frame: writable, cleared, and apart from
the frame, the CRT's arguments, storage and sources but the input and the
coefficient. -/
structure PpCall (g : CrtGeometry) (s : State) : Prop where
  fit : g.output.toNat + 8 * ppPreWords g ≤ 2 ^ 32
  write : InRegions s.wr (State.addr g.output) (8 * ppPreWords g)
  workspace : Region.Disjoint ⟨State.addr g.base, g.size⟩ ⟨State.addr g.output, 8 * ppPreWords g⟩
  below : (FrameStack.belowA s.sp 56).Disjoint ⟨State.addr g.output, 8 * ppPreWords g⟩
  args : Region.Disjoint ⟨State.addr s.sp, 56⟩ ⟨State.addr g.output, 8 * ppPreWords g⟩
  sources : ∀ i : Fin 7, i ≠ 1 → i ≠ 6 →
    Region.Disjoint ⟨State.addr (g.source i), g.sourceLength i⟩ ⟨State.addr g.output, 8 * ppPreWords g⟩
  input : g.input = g.output
  qi : g.qi = g.output
  cleared : Spec.Rsa.wordsAt s.mem (State.addr g.output) (ppPreWords g) = List.replicate (ppPreWords g) 0
  noR2 : g.r2 = none

/-- The CRT's frame and arguments together, `112` bytes from the pushed stack pointer. -/
theorem pp_push_separate {s : State} {r : Region} (fit : 56 ≤ s.sp.toNat)
    (below : (FrameStack.belowA s.sp 56).Disjoint r) (args : Region.Disjoint ⟨State.addr s.sp, 56⟩ r) :
    (⟨State.addr (pcPushed s).sp, 112⟩ : Region).Disjoint r := by
  intro a ha hb
  have lo : (⟨State.addr (pcPushed s).sp, 56⟩ : Region).Disjoint r := by
    have e : FrameStack.belowA s.sp 56 = ⟨State.addr (pcPushed s).sp, 56⟩ := by
      show _ = (⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩ : Region)
      unfold FrameStack.belowA
      rw [FrameStack.addr_sub' fit]
    rw [← e]; exact below
  by_cases low : (a - State.addr (pcPushed s).sp).toNat < 56
  · exact lo a low hb
  · apply args a ?_ hb
    rw [← public_push_argAddr fit]
    change (a - (State.addr (pcPushed s).sp + BitVec.ofNat 64 56)).toNat + 1 ≤ 56
    have inside := (Offset.lt_iff a (State.addr (pcPushed s).sp) (d := 56) (n := 56) (by decide)).mpr
      ⟨by omega, by change (a - State.addr (pcPushed s).sp).toNat + 1 ≤ 112 at ha; omega⟩
    omega

/-- The saved callee registers survive the body's writes. -/
theorem pp_callee_saved {s t : State} {g : CrtGeometry} {regs : Reg → BitVec 32}
    (saved : Spill.Saved s.mem (State.addr s.sp) regs pcCalleeSaved)
    (frame : Frame (crtMutable g s.sp ++ [⟨State.addr g.output, 8 * ppPreWords g⟩]) s.mem t.mem)
    (workspace : (⟨State.addr s.sp, 56⟩ : Region).Disjoint ⟨State.addr g.base, g.size⟩)
    (output : (⟨State.addr s.sp, 56⟩ : Region).Disjoint ⟨State.addr g.output, 8 * ppPreWords g⟩) :
    Spill.Saved t.mem (State.addr s.sp) regs pcCalleeSaved := by
  intro p hp
  have fit : p.2 + 4 ≤ 56 := by
    simp only [pcCalleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have gap : p.2 + 4 ≤ 48 ∨ 52 ≤ p.2 := by
    simp only [pcCalleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have low : 16 ≤ p.2 := by
    simp only [pcCalleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have sub : (⟨off (State.addr s.sp) p.2, 4⟩ : Region).Sub ⟨State.addr s.sp, 56⟩ :=
    Offset.sub_base _ fit
  have keep := frame.readW (a := off (State.addr s.sp) p.2) (w := 32) (r := ⟨off (State.addr s.sp) p.2, 4⟩)
    (by simp [Region.Contains])
    (by
      intro r hr
      simp only [crtMutable, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl | rfl | rfl) | rfl
      · exact workspace.sub_left sub
      · exact Offset.disjoint_base _ (by omega) (by omega)
      · exact Offset.disjoint _ (Or.inr (by omega)) (by omega) (by decide)
      · exact Offset.disjoint _ gap (by omega) (by decide)
      · exact output.sub_left sub) (by decide : 32 / 8 < 2 ^ 64)
  exact keep.trans (saved p hp)

theorem pp_crtFrame_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} (h : CrtFnInput g bs s)
    (pre : PpCall g s) :
    WP isa crtFrame s fun t =>
      t.gpr .r0 = (if ppGood g bs then 1 else 0) ∧
      Spec.Rsa.wordsAt t.mem (State.addr g.output) (ppPreWords g) =
        (if ppGood g bs then ppValues g bs else List.replicate (ppPreWords g) 0) ∧
      t.sp = s.sp ∧ t.wr = s.wr ∧ t.rd = s.rd ∧
      Frame [FrameStack.belowA s.sp 56, ⟨State.addr g.base, g.size⟩,
        ⟨State.addr g.output, 8 * ppPreWords g⟩] s.mem t.mem := by
  unfold crtFrame
  refine WP.frame (by decide) h.stackFit (by decide) ?_
  rw [WP.seq_iff]
  refine WP.mono (crt_entry_ready s h) ?_
  rintro u ⟨ready, frameU, savedU, restU⟩
  have spU : u.sp = (pcPushed s).sp := restU.sp
  have preU : PpPre g u := by
    refine ⟨pre.fit, ?_, pre.workspace, ?_, pre.sources, pre.input, pre.qi, pre.noR2⟩
    · rw [restU.wr]; obtain ⟨r, hr, hc⟩ := pre.write; exact ⟨r, List.mem_cons_of_mem _ hr, hc⟩
    · rw [spU]; exact pp_push_separate h.stackFit pre.below pre.args
  have clearedU : Spec.Rsa.wordsAt u.mem (State.addr g.output) (ppPreWords g) = List.replicate (ppPreWords g) 0 := by
    rw [Proof.Rsa.wordsAt_frame frameU (by have := pre.fit; omega)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst r; exact pre.below.symm)]
    exact pre.cleared
  rw [WP.seq_iff]
  refine WP.mono (pp_body_scoped_ok u ready preU clearedU) ?_
  rintro v ⟨r0, words, frameV, restV⟩
  have spV : v.sp = s.sp - BitVec.ofNat 32 56 := restV.sp.trans restU.sp
  have wrV : v.wr = (pcPushed s).wr := restV.wr.trans restU.wr
  have below : FrameStack.belowA s.sp 56 = ⟨State.addr u.sp, 56⟩ := by
    rw [spU]
    show _ = (⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩ : Region)
    unfold FrameStack.belowA
    rw [FrameStack.addr_sub' h.stackFit]
  have saved : Spill.Saved v.mem (State.addr v.sp) s.gpr pcCalleeSaved := by
    rw [restV.sp]
    apply pp_callee_saved savedU frameV
    · rw [← below]; exact h.stackWorkspace
    · rw [← below]; exact pre.below
  have fit : v.sp.toNat + 56 ≤ 2 ^ 32 := by
    rw [spV, FrameStack.sub_toNat' h.stackFit]
    have := s.sp.isLt
    omega
  have read : InRegions (v.rd ++ v.wr) (State.addr v.sp) 56 := by
    refine ⟨⟨State.addr v.sp, 56⟩, List.mem_append_right _ ?_, Region.contains_self _ _⟩
    rw [wrV, spV]
    exact List.mem_cons_self
  refine WP.mono (pc_restore_ok v s.gpr fit read saved) ?_
  rintro t ⟨_, memT, restT⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [popped_gpr (by decide : Reg.r0 ≠ .r12), restT.gpr .r0 (by decide)]; exact r0
  · rw [popped_mem, memT]; exact words
  · rw [popped_sp, restT.sp, spV]; exact BitVec.sub_add_cancel _ _
  · rw [popped_wr, restT.wr, wrV]; rfl
  · rw [popped_rd, restT.rd, restV.rd, restU.rd]; rfl
  · rw [popped_mem, memT]
    have f2 : Frame [FrameStack.belowA s.sp 56, ⟨State.addr g.base, g.size⟩,
        ⟨State.addr g.output, 8 * ppPreWords g⟩] u.mem v.mem := frameV.sub fun r hr => by
      simp only [crtMutable, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl | rfl | rfl) | rfl
      · exact ⟨⟨State.addr g.base, g.size⟩, by simp, fun _ h => h⟩
      · exact ⟨FrameStack.belowA s.sp 56, by simp, by rw [below]; exact Region.sub_prefix (by decide)⟩
      · exact ⟨FrameStack.belowA s.sp 56, by simp, by rw [below]; exact Offset.sub_base _ (by decide)⟩
      · exact ⟨FrameStack.belowA s.sp 56, by simp, by rw [below]; exact Offset.sub_base _ (by decide)⟩
      · exact ⟨⟨State.addr g.output, 8 * ppPreWords g⟩, by simp, fun _ h => h⟩
    exact (frameU.mono (by simp)).trans f2

end VG.Proof.Bignum.Arm
