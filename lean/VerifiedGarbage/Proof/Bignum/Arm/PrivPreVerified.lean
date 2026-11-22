module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Bignum.Arm.UmaalArithmetic
import VerifiedGarbage.Proof.Bignum.Arm.ZeroCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT
public import VerifiedGarbage.Proof.Bignum.Arm.PcPush
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Bignum.Arm.ZeroCT
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT
meta import VerifiedGarbage.Proof.Bignum.Arm.PcPush
meta import VerifiedGarbage.Proof.Framework.Arm.Frame
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Spec.Rsa.PrivatePrecompute
import VerifiedGarbage.Proof.Bignum.Arm.Zero
import VerifiedGarbage.Proof.Bignum.Arm.PublicPush
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Bignum.ExportEncoding
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Spec.Rsa.PrivatePrecompute
meta import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Proof.Bignum.Arm.Zero
meta import VerifiedGarbage.Proof.Bignum.Arm.PublicPush
meta import VerifiedGarbage.Proof.Bignum.Arm.Stack
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout
meta import VerifiedGarbage.Proof.Bignum.ByteWords
meta import VerifiedGarbage.Proof.Bignum.MemoryFrame
meta import VerifiedGarbage.Proof.Bignum.ExportEncoding
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.Rsa.BytesFrame
meta import VerifiedGarbage.Proof.Framework.Arm.CallF
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheck
import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheckCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtEntryCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtEntryReady
import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheck
meta import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheckCT
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtEntryCT
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
meta import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Bignum.Arm.PrivPreModulus
public import VerifiedGarbage.Proof.Bignum.Arm.CrtPrepareState
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Bignum.Arm.PrepareAcceptedPrime
import VerifiedGarbage.Proof.Bignum.Arm.SubModArrayCT
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeOut
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeOutCT
import VerifiedGarbage.Proof.Bignum.Arm.MaskOutputCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtSelectWorkspace
import VerifiedGarbage.Proof.Bignum.Arm.CrtPrepareCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtBothPowers
import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandState
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.CrtHeaderCopiesCT
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowPrime
import VerifiedGarbage.Proof.Bignum.Arm.PrimeR2FromCT
import VerifiedGarbage.Proof.Bignum.Arm.TransferArray
import VerifiedGarbage.Proof.Bignum.Arm.TransferArrayCT
import VerifiedGarbage.Proof.Bignum.Arm.LayoutFrameReady
import VerifiedGarbage.Proof.Bignum.Arm.PrimeR2From
import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowPowerCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowPower
import VerifiedGarbage.Proof.Bignum.Arm.ExportArrayCT
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFnCT
public import VerifiedGarbage.Proof.Bignum.Arm.CrtCallStack
meta import VerifiedGarbage.Proof.Bignum.Arm.PrivPreModulus
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtCallStack
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtPrepareState
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Bignum.Arm.PrepareAcceptedPrime
meta import VerifiedGarbage.Proof.Bignum.Arm.SubModArrayCT
meta import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeOut
meta import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeOutCT
meta import VerifiedGarbage.Proof.Bignum.Arm.MaskOutputCT
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtSelectWorkspace
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtPrepareCT
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtBothPowers
meta import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandState
meta import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtHeaderCopiesCT
meta import VerifiedGarbage.Proof.Framework.CallLay
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowPrime
meta import VerifiedGarbage.Proof.Bignum.Arm.PrimeR2FromCT
meta import VerifiedGarbage.Proof.Bignum.Arm.TransferArray
meta import VerifiedGarbage.Proof.Bignum.Arm.TransferArrayCT
meta import VerifiedGarbage.Proof.Bignum.Arm.LayoutFrameReady
meta import VerifiedGarbage.Proof.Bignum.Arm.PrimeR2From
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowPowerCT
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowPower
meta import VerifiedGarbage.Proof.Bignum.Arm.ExportArrayCT
meta import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFnCT
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtEntryReady
public import VerifiedGarbage.Proof.Bignum.Arm.CrtInput
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtInput

/-! ### `Bignum.Arm.PrivPreFrame`, which only this module used -/

section

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
      ⟨by omega_using [low], by change (a - State.addr (pcPushed s).sp).toNat + 1 ≤ 112 at ha; omega_using [ha]⟩
    omega_using [inside]

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
      · exact Offset.disjoint_base _ (by omega_using [low]) (by omega_using [fit])
      · exact Offset.disjoint _ (Or.inr (by omega_using [low])) (by omega_using [fit]) (by decide)
      · exact Offset.disjoint _ gap (by omega_using [fit]) (by decide)
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
    rw [Proof.Rsa.wordsAt_frame frameU (by have := pre.fit; omega_using [this])
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
    omega_using []
  have read : InRegions (v.rd ++ v.wr) (State.addr v.sp) 56 := by
    refine ⟨⟨State.addr v.sp, 56⟩, List.mem_append_right _ ?_, Region.contains_self _ _⟩
    rw [wrV, spV]
    exact List.mem_cons_self
  refine WP.mono (pc_restore_ok v s.gpr fit read saved) ?_
  rintro t ⟨_, memT, restT⟩ ml ul hfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [popped_gpr (by decide : Reg.r0 ≠ .r12), restT.gpr .r0 (by decide)]; exact r0
  · dsimp only
    rw [Proof.Rsa.wordsAt_frame hfl (by have := pre.fit; omega_using [this])
      (fun r hr => by simp only [List.mem_singleton] at hr; subst r; exact pre.below.symm), memT]
    exact words
  · rw [popped_sp, restT.sp, spV]; exact BitVec.sub_add_cancel _ _
  · rw [popped_wr, restT.wr, wrV]; rfl
  · rw [popped_rd, restT.rd, restV.rd, restU.rd]; rfl
  · dsimp only
    rw [memT] at hfl
    have f2 : Frame [FrameStack.belowA s.sp 56, ⟨State.addr g.base, g.size⟩,
        ⟨State.addr g.output, 8 * ppPreWords g⟩] u.mem v.mem := frameV.sub fun r hr => by
      simp only [crtMutable, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl | rfl | rfl) | rfl
      · exact ⟨⟨State.addr g.base, g.size⟩, by simp, fun _ h => h⟩
      · exact ⟨FrameStack.belowA s.sp 56, by simp, by rw [below]; exact Region.sub_prefix (by decide)⟩
      · exact ⟨FrameStack.belowA s.sp 56, by simp, by rw [below]; exact Offset.sub_base _ (by decide)⟩
      · exact ⟨FrameStack.belowA s.sp 56, by simp, by rw [below]; exact Offset.sub_base _ (by decide)⟩
      · exact ⟨⟨State.addr g.output, 8 * ppPreWords g⟩, by simp, fun _ h => h⟩
    exact ((frameU.mono (by simp)).trans f2).trans
      (hfl.mono fun r hr => by simp only [List.mem_singleton] at hr; subst r; exact List.mem_cons_self)

end VG.Proof.Bignum.Arm

end

end

/-! ### `Bignum.Arm.PrivPreFrameCT`, which only this module used -/

section

/-! ### `Bignum.Arm.PrivPreValidCT`, which only this module used -/

section

/-! ### `Bignum.Arm.PrivPreBlocksCT`, which only this module used -/

section

/-! # The precomputation's address blocks depend only on the stack pointer and the main workspace

Each reads the frame and the main header, whose address the frame holds, and
computes the offsets in `pre` from public lengths.
-/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.PrivPreFn VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

/-- The frame's slot 8 holds the main workspace. -/
def MainSaved (g : CrtGeometry) (s : State) : Prop :=
  s.mem.readW (off (State.addr s.sp) 8) 32 = g.base ∧ s.sp.toNat + 112 ≤ 2 ^ 32 ∧
    InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 8) 4

theorem CrtShared.mainSaved {g : CrtGeometry} {bs : Fin 7 → List Byte} {s : State} (h : CrtShared g bs s) :
    MainSaved g s :=
  ⟨h.savedMain, h.stack.nowrap, h.stack.read (by decide)⟩

/-- `r1` loaded with the main workspace, after a load of `r4`. -/
theorem pp_loadMain_wp (s : State) {g : CrtGeometry} (h : MainSaved g s) (d : Nat) (hd : d + 4 ≤ 112)
    (read : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) d) 4) :
    WP isa (.block [.ldrSp .r4 d, .ldrSp .r1 8]) s fun t => t.gpr .r1 = g.base := by
  obtain ⟨saved, fit, read8⟩ := h
  refine wp_loadStack (a := off (State.addr s.sp) d) (by omega_using [hd]) (addr_add (by omega_using [hd, fit])) read fun u a => ?_
  refine wp_loadStack (a := off (State.addr s.sp) 8) (by decide) (by rw [a.sp]; exact addr_add (by omega_using [fit]))
    (by rw [a.rd, a.wr]; exact read8) fun t b => WP.block_nil ?_
  rw [b.gpr, a.mem]; exact saved

theorem pp_modulusEnd_ct {g : CrtGeometry} {P1 P2 : State → Prop}
    (h1 : ∀ s, P1 s → MainSaved g s ∧ InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 4) 4)
    (h2 : ∀ s, P2 s → MainSaved g s ∧ InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 4) 4) :
    RelCT isa (fun s t => P1 s ∧ P2 t ∧ s.sp = t.sp) (.block modulusEnd) (fun s t => s.sp = t.sp) := by
  have loads : RelCT isa (fun s t => s.sp = t.sp) (.block [.ldrSp .r4 4, .ldrSp .r1 8]) (fun s t => s.sp = t.sp) :=
    stackLoads_ct [(.r4, 4), (.r1, 8)]
  have first := (loads.mono
    (P' := fun (s t : State) => P1 s ∧ P2 t ∧ s.sp = t.sp) (fun _ _ h => h.2.2) (fun _ _ h => h)).wp
    (F₁ := fun (t : State) => t.gpr .r1 = g.base) (F₂ := fun (t : State) => t.gpr .r1 = g.base)
    (fun s t h => ⟨pp_loadMain_wp s (h1 s h.1).1 4 (by decide) (h1 s h.1).2,
      pp_loadMain_wp t (h2 t h.2.1).1 4 (by decide) (h2 t h.2.1).2⟩)
  have second : RelCT isa (fun s t => s.sp = t.sp ∧ s.gpr .r1 = g.base ∧ t.gpr .r1 = g.base)
      (.block [.ldr .r1 .r1 48, .dp .add .r4 .r4 (.shifted .r1 .lsl 4)]) (fun s t => s.sp = t.sp) := by
    apply relCT_keep_sp (sp := fun _ _ h => h.1)
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r1]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.2.1.trans h.2.2.symm
  exact RelCT.block_append (M := isa) (l₁ := ([.ldrSp .r4 4, .ldrSp .r1 8] : List Instr)) (first.seq second)

theorem pp_pDest_ct {g : CrtGeometry} {P1 P2 : State → Prop}
    (h1 : ∀ s, P1 s → MainSaved g s ∧ InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 4) 4)
    (h2 : ∀ s, P2 s → MainSaved g s ∧ InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 4) 4) :
    RelCT isa (fun s t => P1 s ∧ P2 t ∧ s.sp = t.sp) (.block pDest) (fun _ _ => True) := by
  have last := (by
    apply relCT_keep_sp (sp := fun _ _ h => h)
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp) : RelCT isa (fun s t => s.sp = t.sp) (.block [.mov .r2 (.imm 4)]) (fun s t => s.sp = t.sp))
  exact (RelCT.block_append ((pp_modulusEnd_ct h1 h2).seq last)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem pp_qDest_ct {g : CrtGeometry} {P1 P2 : State → Prop}
    (h1 : ∀ s, P1 s → MainSaved g s ∧ InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 4) 4)
    (h2 : ∀ s, P2 s → MainSaved g s ∧ InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 4) 4) :
    RelCT isa (fun s t => P1 s ∧ P2 t ∧ s.sp = t.sp) (.block qDest) (fun _ _ => True) := by
  have last := (by
    apply relCT_keep_sp (sp := fun _ _ h => h)
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp) : RelCT isa (fun s t => s.sp = t.sp) (.block [.dp .add .r4 .r4 (.shifted .r7 .lsl 3), .mov .r2 (.imm 4)]) (fun s t => s.sp = t.sp))
  have head := RelCT.block_append ((pp_modulusEnd_ct h1 h2).seq (primeWidth_ct 68))
  exact (RelCT.block_append (head.seq last)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem pp_maskArgs_ct {g : CrtGeometry} {P1 P2 : State → Prop}
    (h1 : ∀ s, P1 s → MainSaved g s) (h2 : ∀ s, P2 s → MainSaved g s) :
    RelCT isa (fun s t => P1 s ∧ P2 t ∧ s.sp = t.sp) (.block maskArgs) (fun _ _ => True) := by
  have wp (s : State) (h : MainSaved g s) : WP isa (.block [.ldrSp .r1 8]) s fun t => t.gpr .r1 = g.base := by
    obtain ⟨saved, fit, read8⟩ := h
    refine wp_loadStack (a := off (State.addr s.sp) 8) (by decide) (addr_add (by omega_using [fit])) read8 fun t b => WP.block_nil ?_
    rw [b.gpr]; exact saved
  have first := ((loadStack_ct .r1 8).mono
    (P' := fun (s t : State) => P1 s ∧ P2 t ∧ s.sp = t.sp) (fun _ _ h => h.2.2) (fun _ _ h => h)).wp
    (F₁ := fun (t : State) => t.gpr .r1 = g.base) (F₂ := fun (t : State) => t.gpr .r1 = g.base)
    (fun s t h => ⟨wp s (h1 s h.1), wp t (h2 t h.2.1)⟩)
  have second : RelCT isa (fun s t => s.sp = t.sp ∧ s.gpr .r1 = g.base ∧ t.gpr .r1 = g.base)
      (.block [.ldr .r1 .r1 48, .mov .r6 (.shifted .r1 .lsl 4)]) (fun s t => s.sp = t.sp) := by
    apply relCT_keep_sp (sp := fun _ _ h => h.1)
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r1]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.2.1.trans h.2.2.symm
  have a := RelCT.block_append (M := isa) (l₁ := ([.ldrSp .r1 8] : List Instr)) (first.seq second)
  have b := RelCT.block_append (a.seq (primeWidth_ct 68))
  have add := (by
    apply relCT_keep_sp (sp := fun _ _ h => h)
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp) : RelCT isa (fun s t => s.sp = t.sp) (.block [.dp .add .r6 .r6 (.shifted .r7 .lsl 3)]) (fun s t => s.sp = t.sp))
  have c := RelCT.block_append (b.seq add)
  have d := RelCT.block_append (c.seq (primeWidth_ct 76))
  have last : RelCT isa (fun s t => s.sp = t.sp) (.block [.dp .add .r6 .r6 (.shifted .r7 .lsl 3), .ldrSp .r4 4])
      (fun s t => s.sp = t.sp) :=
    RelCT.block_append (M := isa) (l₁ := ([.dp .add .r6 .r6 (.shifted .r7 .lsl 3)] : List Instr))
      (add.seq (loadStack_ct .r4 4))
  exact (RelCT.block_append (d.seq last)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Bignum.Arm

end

end

/-! # The modulus' values and the mask are computed in constant time -/

@[expose] public section


namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Impl.Bignum.Arm.PrivPreFn VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

/-- A factor's phase: the shared state, and the acceptance bit, which accepts
only a valid factor. -/
def PpFactorIn (g : CrtGeometry) (bs : Fin 7 → List Byte) (j : Fin 6) (s : State) : Prop :=
  CrtShared g bs s ∧ ppFlag s ≤ 1 ∧
    (ppFlag s ≠ 0 → 1 < Spec.Rsa.os2ip (bs j.succ) ∧ Spec.Rsa.os2ip (bs j.succ) % 2 = 1)

theorem pp_phase_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} (j : Fin 6) (prime : j = 1 ∨ j = 2)
    {dest : List Instr} {d : BitVec 32}
    (destOk : ∀ (bs : Fin 7 → List Byte) (u : State), CrtShared g bs u → WP isa (.block dest) u fun t =>
      t.gpr .r4 = d ∧ t.gpr .r2 = BitVec.ofNat 32 4 ∧ t.mem = u.mem ∧ Rest [.r1, .r2, .r3, .r4, .r7] u t)
    (destCt : ∀ {P1 P2 : State → Prop}, (∀ s, P1 s → MainSaved g s ∧ InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 4) 4) →
      (∀ s, P2 s → MainSaved g s ∧ InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 4) 4) →
      RelCT isa (fun s t => P1 s ∧ P2 t ∧ s.sp = t.sp) (.block dest) (fun _ _ => True)) :
    RelCT isa (fun s t => PpFactorIn g bs1 j s ∧ PpFactorIn g bs2 j t ∧ s.sp = t.sp)
      (phase (56 + 8 * j.val) dest) (fun _ _ => True) := by
  let v := ppWords (g.sourceLength j.succ)
  let N := crtN g.base g.words
  -- The narrow workspace entered.
  let Entered := fun (bs : Fin 7 → List Byte) (s : State) =>
    CrtShared g bs s ∧ NarrowPrimeInput N (g.source j.succ) (workspaceWords g.words) v
      (g.sourceLength j.succ) (56 + 8 * j.val) (bs j.succ) s
  have enterWP (s : State) {bs : Fin 7 → List Byte} (h : PpFactorIn g bs j s) :
      WP isa (enterFactor (56 + 8 * j.val + 4)) s (Entered bs) := by
    obtain ⟨_, _, kfit, kpos, _, _⟩ := h.1.pp_fits j prime
    have hj := j.isLt
    refine WP.mono (pp_enterFactor_ok s h.1 j prime) ?_
    rintro z ⟨sharedZ, selectedZ, flagZ, _, _⟩
    have flag : ppFlag z = ppFlag s := by unfold ppFlag; rw [flagZ]
    refine ⟨sharedZ, selectedZ, ?_, kpos, kfit, by have := sharedZ.stack.nowrap; omega_using [this], sharedZ.stack.read (by decide),
      by rw [← ppFlag, flag]; exact h.2.1, by rw [← ppFlag, flag]; exact h.2.2⟩
    simpa only [show 56 + 8 * j.val + 4 = 60 + 8 * j.val by omega_using []] using sharedZ.savedOperand j sharedZ.narrow_member
  have enterCT : RelCT isa (fun s t => PpFactorIn g bs1 j s ∧ PpFactorIn g bs2 j t ∧ s.sp = t.sp)
      (enterFactor (56 + 8 * j.val + 4)) (fun _ _ => True) :=
    (pp_enterFactor_ct j prime).mono (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ _ => trivial)
  -- The factor prepared.
  let Prepared := fun (bs : Fin 7 → List Byte) (s : State) =>
    CrtShared g bs s ∧ ArithmeticReady N (workspaceWords g.words) v s
  have le {bs : Fin 7 → List Byte} {s : State} (h : CrtShared g bs s) : v ≤ g.words := by
    obtain ⟨_, le, _⟩ := h.pp_fits j prime
    exact le
  have prepWP (s : State) {bs : Fin 7 → List Byte} (h : Entered bs s) :
      WP isa (narrowPrimeFrom (56 + 8 * j.val)) s (Prepared bs) := by
    refine WP.mono (crt_narrowPrimeFrom_ok s h.1 h.2 (le h.1)) ?_
    rintro y ⟨readyY, _, _, _, _, frameY, restY⟩
    exact ⟨h.1.after_narrow (frameY.mono (by simp)) restY, readyY⟩
  have prepCT : RelCT isa (fun s t => Entered bs1 s ∧ Entered bs2 t ∧ s.sp = t.sp)
      (narrowPrimeFrom (56 + 8 * j.val)) (fun _ _ => True) := by
    intro s t tr1 tr2 u w h e1 e2
    exact crt_narrowPrimeFrom_ct (le h.1.1) s t tr1 tr2 u w h e1 e2
  -- The destination.
  let Ready := fun (s : State) => SmallFnReady N (workspaceWords g.words) v 4 s ∧ s.gpr .r4 = d
  have destWP (s : State) {bs : Fin 7 → List Byte} (h : Prepared bs s) : WP isa (.block dest) s Ready := by
    refine WP.mono (destOk bs s h.1) ?_
    rintro t ⟨r4, r2, mem, rest⟩
    exact ⟨⟨h.2.workspace.congr rest.wr, by rw [mem]; exact h.2.layout, by rw [mem]; exact h.2.width,
      (rest.gpr .r0 (by decide)).trans h.2.ptr, r2⟩, r4⟩
  have destRel : RelCT isa (fun s t => Prepared bs1 s ∧ Prepared bs2 t ∧ s.sp = t.sp) (.block dest) (fun _ _ => True) :=
    destCt (fun s h => ⟨h.1.mainSaved, h.1.stack.read (by decide)⟩) (fun s h => ⟨h.1.mainSaved, h.1.stack.read (by decide)⟩)
  have exportCT : RelCT isa (fun s t => Ready s ∧ Ready t ∧ s.sp = t.sp) exportArray (fun _ _ => True) :=
    (exportArray_ct (dst := d) (by decide : 4 < 8)).mono (fun _ _ h => ⟨h.1.1, h.2.1.1, h.1.2, h.2.1.2⟩)
      (fun _ _ _ => trivial)
  rw [phase]
  exact crt_seq_ct enterCT (fun s h => enterWP s h) (fun s h => enterWP s h)
    (crt_seq_ct prepCT (fun s h => prepWP s h) (fun s h => prepWP s h)
      (crt_seq_ct destRel (fun s h => destWP s h) (fun s h => destWP s h) exportCT))

end VG.Proof.Bignum.Arm


namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Impl.Bignum.Arm.PrivPreFn VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt Layout wOf)
open VG.Proof.X25519.Arm (Rest)

/-- What the steps after the main workspace's selection keep: the frame, the
main workspace in its slot, and `pre`. -/
def PpKept (g : CrtGeometry) (s : State) : Prop :=
  CrtCallStack g s ∧ s.mem.readW (off (State.addr s.sp) 8) 32 = g.base ∧ PpPre g s ∧ Spec.Rsa.lenValid g.length ∧
    Region.Disjoint ⟨State.addr g.base, 8 * workspaceWords g.words⟩ ⟨State.addr g.output, 8 * ppPreWords g⟩ ∧
    (0 < g.pLength ∧ g.pLength < g.length ∧ 0 < g.qLength ∧ g.qLength < g.length)

theorem PpKept.after {g : CrtGeometry} {s t : State} {rs : List Reg} {regions : List Region}
    (h : PpKept g s) (frame : Frame regions s.mem t.mem) (rest : Rest rs s t)
    (stack : ∀ r ∈ regions, (⟨State.addr s.sp, 112⟩ : Region).Disjoint r) : PpKept g t := by
  refine ⟨h.1.after_outside frame rest stack, ?_, h.2.2.1.after rest, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
  rw [rest.sp]
  exact (frame.readW (r := ⟨off (State.addr s.sp) 8, 4⟩) (Region.contains_self _ _)
    (fun r hr => (stack r hr).sub_left (Offset.sub_base _ (by decide))) (by decide)).trans h.2.1

theorem pp_selectP_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} :
    RelCT isa (fun s t => CrtShared g bs1 s ∧ CrtShared g bs2 t ∧ s.sp = t.sp) selectP (fun _ _ => True) := by
  have mainWP (s : State) {bs : Fin 7 → List Byte} (h : CrtShared g bs s) :
      WP isa selectMain s (CrtSelected g bs g.base) :=
    (crt_selectMain_ready s h).mono fun _ j => ⟨j.1, j.2.1⟩
  rw [selectP]
  exact crt_seq_ct (crt_selectMain_ct.mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial))
    (fun s h => mainWP s h) (fun s h => mainWP s h)
    ((crt_selectChild_ct 224).mono (fun _ _ h => ⟨h.1.2.ptr.trans h.2.1.2.ptr.symm, h.2.2⟩) (fun _ _ _ => trivial))

theorem pp_modulusR2_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte}
    (hn : Spec.Rsa.os2ip (bs1 0) = Spec.Rsa.os2ip (bs2 0)) :
    RelCT isa (fun s t => CrtShared g bs1 s ∧ CrtShared g bs2 t ∧ s.sp = t.sp) modulusR2 (fun _ _ => True) := by
  let L := workspaceWords g.words
  let P := crtP g.base g.words
  -- p's workspace selected.
  have selectWP (s : State) {bs : Fin 7 → List Byte} (h : CrtShared g bs s) :
      WP isa selectP s (CrtSelected g bs P) :=
    (pp_selectP_ok s h).mono fun _ j => ⟨j.1, j.2.1⟩
  -- The main workspace's pointer in r1.
  let T := fun (bs : Fin 7 → List Byte) (s : State) =>
    TransferArrayInput P g.base L L g.words s ∧ numAt s.mem (State.addr g.base) g.words 0 = Spec.Rsa.os2ip (bs 0) ∧
      Spec.Rsa.modulusValid (Spec.Rsa.os2ip (bs 0)) g.length = true ∧ Spec.Rsa.lenValid g.length
  have loadWP (s : State) {bs : Fin 7 → List Byte} (h : CrtSelected g bs P s) :
      WP isa (.block [.ldrSp .r1 8]) s (T bs) := by
    refine wp_loadStack (a := off (State.addr s.sp) 8) (by decide)
      (addr_add (by have := h.1.stack.nowrap; omega_using [this])) (h.1.stack.read (by decide)) fun x a => WP.block_nil ?_
    have ra : Rest [.r1] s x := a.rest (by decide)
    exact ⟨⟨h.2.of_mem a.mem ra ((a.other .r0 (by decide)).trans h.2.ptr),
      h.1.buffers.context.main.congr ra.wr, by rw [a.mem]; exact h.1.main.toCrtLayoutState,
      a.gpr.trans h.1.savedMain, h.1.buffers.context.sepMP⟩, by rw [a.mem]; exact h.1.modulus, h.1.valid,
      h.1.buffers.lengthValid⟩
  have loadCT : RelCT isa (fun s t => CrtSelected g bs1 P s ∧ CrtSelected g bs2 P t ∧ s.sp = t.sp)
      (.block [.ldrSp .r1 8]) (fun _ _ => True) :=
    (loadStack_ct .r1 8).mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  -- `n` copied into p's workspace.
  let M := fun (bs : Fin 7 → List Byte) (s : State) =>
    PrecomputeModulus P L g.words s ∧ numAt s.mem (State.addr P) g.words 0 = Spec.Rsa.os2ip (bs 0) ∧
      Spec.Rsa.lenValid g.length
  have copyWP (s : State) {bs : Fin 7 → List Byte} (h : T bs s) : WP isa (transferArray 0 0) s (M bs) := by
    refine (transferArray_ok s h.1 (by decide) (by decide)).mono ?_
    rintro y ⟨readyY, numY, _, _, _⟩
    rw [h.2.1] at numY
    obtain ⟨odd, gt, _⟩ := valid_facts h.2.2.1 h.2.2.2.1
    exact ⟨⟨⟨readyY.workspace, readyY.layout, readyY.width, readyY.ptr, readyY.stackRead, readyY.stackSep,
      readyY.saved⟩, by rw [numY]; exact gt, by rw [numY]; exact odd⟩, numY, h.2.2.2⟩
  have copyCT : RelCT isa (fun s t => T bs1 s ∧ T bs2 t ∧ s.sp = t.sp) (transferArray 0 0) (fun _ _ => True) :=
    (transferArray_ct (by decide) (by decide)).mono (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ _ => trivial)
  have prepCT : RelCT isa (fun s t => M bs1 s ∧ M bs2 t ∧ s.sp = t.sp) prepareModulus (fun _ _ => True) := by
    intro s t tr1 tr2 u w h e1 e2
    have words : g.words ≤ 128 := (crt_width_valid h.1.2.2).2.1
    exact prepareModulus_ct (M := Spec.Rsa.os2ip (bs1 0)) (by omega_using [words]) s t tr1 tr2 u w
      ⟨⟨h.1.1, h.1.2.1⟩, ⟨h.2.1.1, h.2.1.2.1.trans hn.symm⟩, h.2.2⟩ e1 e2
  rw [modulusR2]
  exact crt_seq_ct pp_selectP_ct (fun s h => selectWP s h) (fun s h => selectWP s h)
    (crt_seq_ct loadCT (fun s h => loadWP s h) (fun s h => loadWP s h)
      (crt_seq_ct copyCT (fun s h => copyWP s h) (fun s h => copyWP s h) prepCT))

theorem pp_modulusPart_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} :
    RelCT isa (fun s t => (CrtShared g bs1 s ∧ PpPre g s ∧ ppFlag s ≤ 1) ∧
      (CrtShared g bs2 t ∧ PpPre g t ∧ ppFlag t ≤ 1) ∧ s.sp = t.sp) modulusPart (fun _ _ => True) := by
  let len := workspaceWords g.words
  let P := crtP g.base g.words
  have mainSize : 256 ≤ 8 * len := by simp only [len, workspaceWords]; omega_using []
  have mainSub {bs : Fin 7 → List Byte} {s : State} (h : CrtShared g bs s) :
      (⟨State.addr g.base, 8 * len⟩ : Region).Sub ⟨State.addr g.base, g.size⟩ :=
    crt_region_sub_workspace h.buffers.workspace h.buffers.storageFits (by simp [crtRegions, len])
  have pSub {bs : Fin 7 → List Byte} {s : State} (h : CrtShared g bs s) :
      (⟨State.addr P, 8 * len⟩ : Region).Sub ⟨State.addr g.base, g.size⟩ :=
    crt_region_sub_workspace h.buffers.workspace h.buffers.storageFits (by simp [crtRegions, len, P])
  -- The main workspace, which the mask's arguments read.
  let Main := fun (s : State) => Workspace s g.base (8 * len) ∧ Layout s.mem (State.addr g.base) len ∧
    wOf s.mem (State.addr g.base) = g.words
  -- p's workspace selected.
  let S1 := fun (s : State) => LayoutFrameReady P len g.words s ∧ PpKept g s ∧
    (⟨State.addr s.sp, 112⟩ : Region).Disjoint ⟨State.addr P, 8 * len⟩ ∧
    Region.Disjoint ⟨State.addr P, 8 * len⟩ ⟨State.addr g.output, 8 * ppPreWords g⟩ ∧ Main s
  have selectWP (s : State) {bs : Fin 7 → List Byte} (h : CrtShared g bs s ∧ PpPre g s ∧ ppFlag s ≤ 1) :
      WP isa selectP s S1 := by
    refine WP.mono (pp_selectP_ok s h.1) ?_
    rintro u ⟨sharedU, readyU, _, restU⟩
    have preU := h.2.1.after restU
    exact ⟨readyU, ⟨sharedU.stack, sharedU.savedMain, preU, sharedU.buffers.lengthValid,
        preU.workspace.sub_left (mainSub sharedU), sharedU.buffers.pPositive, sharedU.buffers.pShort,
        sharedU.buffers.qPositive, sharedU.buffers.qShort⟩,
      sharedU.stack.separate.sub_right (pSub sharedU), preU.workspace.sub_left (pSub sharedU),
      sharedU.buffers.context.main, sharedU.main.layout, sharedU.main.width⟩
  have selectCT : RelCT isa (fun s t => (CrtShared g bs1 s ∧ PpPre g s ∧ ppFlag s ≤ 1) ∧
      (CrtShared g bs2 t ∧ PpPre g t ∧ ppFlag t ≤ 1) ∧ s.sp = t.sp) selectP (fun _ _ => True) :=
    pp_selectP_ct.mono (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ _ => trivial)
  -- `pre` in r4.
  let S3 := fun (s : State) => ExportState P g.output len g.words (16 * g.words) s ∧ PpKept g s ∧ Main s
  have loadWP (s : State) (h : S1 s) : WP isa (.block [.ldrSp .r4 4]) s S3 := by
    obtain ⟨dl, kept, sep, sepOut, ws, layout, width⟩ := h
    have pre := kept.2.2.1
    have preFit := pre.fit
    have six : 16 * g.words ≤ 8 * ppPreWords g := by simp only [ppPreWords]; omega_using []
    refine wp_loadStack (a := off (State.addr s.sp) 4) (by decide) (addr_add (by have := kept.1.nowrap; omega_using [this]))
      (kept.1.read (by decide)) fun t a => WP.block_nil ?_
    have rest : Rest [.r4] s t := a.rest (by decide)
    refine ⟨⟨dl.workspace.congr a.wr, by rw [a.mem]; exact dl.layout, by rw [a.mem]; exact dl.width,
      (a.other .r0 (by decide)).trans dl.ptr, a.gpr.trans kept.1.output, by omega_using [], by omega_using [preFit, six], ?_, ?_⟩,
      kept.after (regions := []) (by rw [a.mem]; exact Frame.refl _ _) rest (by simp),
      ws.congr a.wr, by rw [a.mem]; exact layout, by rw [a.mem]; exact width⟩
    · rw [a.wr]
      have := CallLay.inRegions_sub (off := 0) (l := 16 * g.words) pre.write (by omega_using [six]) (by omega_using [preFit])
      simpa only [BitVec.add_zero] using this
    · exact sepOut.sub_right (Region.sub_prefix six)
  have loadCT : RelCT isa (fun s t => S1 s ∧ S1 t ∧ s.sp = t.sp) (.block [.ldrSp .r4 4]) (fun _ _ => True) :=
    (loadStack_ct .r4 4).mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  -- `n` and `R² mod n` exported.
  let S4 := fun (s : State) => PpKept g s ∧ Main s
  have exportWP (s : State) (h : S3 s) : WP isa precomputeOut s S4 := by
    obtain ⟨ex, kept, ws, layout, width⟩ := h
    refine WP.mono (precomputeOut_ok s ex.workspace ex.layout ex.width ex.fits ex.write ex.separate ex.ptr ex.output) ?_
    rintro t ⟨_, _, frame, rest⟩
    have pre := kept.2.2.1
    have sub : Region.Sub ⟨State.addr g.output, 16 * g.words⟩ ⟨State.addr g.output, 8 * ppPreWords g⟩ :=
      Region.sub_prefix (by simp only [ppPreWords]; omega_using [])
    have eq : WorkspaceEq (State.addr g.base) (8 * len) s.mem t.mem :=
      WorkspaceEq.of_frame (by have := ws.nowrap; omega_using [this]) frame
        (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact kept.2.2.2.2.1.sub_right sub)
    exact ⟨kept.after frame rest (fun r hr => by
        simp only [List.mem_singleton] at hr; subst r; exact pre.stack.sub_right sub),
      ws.congr rest.wr, eq.layout layout, (eq.width (by have := mainSize; omega_using [mainSize])).trans width⟩
  have exportCT : RelCT isa (fun s t => S3 s ∧ S3 t ∧ s.sp = t.sp) precomputeOut (fun _ _ => True) :=
    precomputeOut_ct.mono (fun _ _ h => ⟨h.1.1, h.2.1.1⟩) (fun _ _ _ => trivial)
  -- The mask's arguments, and the mask.
  let S5 := MaskOutputInput g.output (8 * ppPreWords g)
  have argsWP (s : State) (h : S4 s) : WP isa (.block maskArgs) s S5 := by
    obtain ⟨kept, ws, layout, width⟩ := h
    have header := nativeHeader_of_layout s.mem g.base ws.nowrap (Nat.le_refl _) layout
    rw [width] at header
    obtain ⟨p1, p2, q1, q2⟩ := kept.2.2.2.2.2
    refine WP.mono (pp_maskArgs_ok s kept.1 kept.2.1 (by have := ws.nowrap; omega_using [mainSize, this])
      (ws.read (by omega_using [mainSize])) header.count kept.2.2.2.1 p1 p2 q1 q2) ?_
    rintro t ⟨r4, r6, mem, rest⟩
    exact ⟨r4, r6, by rw [rest.sp]; have := kept.1.nowrap; omega_using [this],
      by rw [rest.rd, rest.wr, rest.sp]; exact kept.1.read (by decide)⟩
  have argsCT : RelCT isa (fun s t => S4 s ∧ S4 t ∧ s.sp = t.sp) (.block maskArgs) (fun _ _ => True) :=
    pp_maskArgs_ct (fun s h => ⟨h.1.2.1, h.1.1.nowrap, h.1.1.read (by decide)⟩)
      (fun s h => ⟨h.1.2.1, h.1.1.nowrap, h.1.1.read (by decide)⟩)
  rw [modulusPart]
  exact crt_seq_ct selectCT (fun s h => selectWP s h) (fun s h => selectWP s h)
    (crt_seq_ct loadCT (fun s h => loadWP s h) (fun s h => loadWP s h)
      (crt_seq_ct exportCT (fun s h => exportWP s h) (fun s h => exportWP s h)
        (crt_seq_ct argsCT (fun s h => argsWP s h) (fun s h => argsWP s h) maskOutput_ct)))

theorem PpValidInput.prepare_input {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : PpValidInput g bs s) : CrtPrepareInput g.base g.modulus g.size g.words g.length (bs 0) s := by
  have mainSub : (⟨State.addr g.base, 8 * workspaceWords g.words⟩ : Region).Sub ⟨State.addr g.base, g.size⟩ :=
    crt_region_sub_workspace h.buffers.workspace h.buffers.storageFits (by simp [crtRegions])
  have source : SavedOperand g.base g.modulus (workspaceWords g.words) g.length 8 12 (bs 0) s :=
    ⟨h.stack.nowrap, ⟨h.stack.read (by decide), h.stack.read (by decide)⟩, h.stack.separate.sub_right mainSub, by decide,
      by decide, h.modulusPtr, h.stack.count, h.buffers.source 0, (h.buffers.sourceSeparate 0).sub_right mainSub⟩
  exact ⟨h.buffers.workspace, h.buffers.context, h.buffers.storageFits, source, h.stack.separate, h.buffers.sourceSeparate 0,
    by simpa only [off, BitVec.add_zero] using h.stack.read (d := 0) (by decide),
    h.stack.write (by decide), h.saved, h.ptr, h.count, h.buffers.lengthValid, rfl⟩

/-- After the validation: the shared state, `pre`, and the acceptance bit. -/
def PpChecked (g : CrtGeometry) (bs : Fin 7 → List Byte) (s : State) : Prop :=
  CrtShared g bs s ∧ PpPre g s ∧ s.mem.readW (off (State.addr s.sp) 48) 32 = (if crtAccepted bs then 1 else 0)

theorem PpChecked.factor {g : CrtGeometry} {bs : Fin 7 → List Byte} {s : State} (h : PpChecked g bs s)
    (j : Fin 6) (prime : j = 1 ∨ j = 2) : PpFactorIn g bs j s := by
  refine ⟨h.1, by unfold ppFlag; rw [h.2.2]; split <;> decide, fun ne => ?_⟩
  have acc : crtAccepted bs := by
    by_contra acc
    unfold ppFlag at ne; rw [h.2.2] at ne; simp [acc] at ne
  rcases prime with rfl | rfl
  · exact (h.1.accepted_factors acc).1
  · exact (h.1.accepted_factors acc).2

theorem PpChecked.accepted {g : CrtGeometry} {bs : Fin 7 → List Byte} {s : State} (h : PpChecked g bs s)
    (ne : ppFlag s ≠ 0) : crtAccepted bs := by
  by_contra acc
  unfold ppFlag at ne; rw [h.2.2] at ne; simp [acc] at ne

/-- After `R² mod n`: it, in p's workspace. -/
def PpReady (g : CrtGeometry) (bs : Fin 7 → List Byte) (s : State) : Prop :=
  PpChecked g bs s ∧
    numAt s.mem (State.addr (crtP g.base g.words)) g.words 4 = 2 ^ (128 * g.words) % Spec.Rsa.os2ip (bs 0)

theorem pp_modulusR2_wp (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} (h : PpChecked g bs s) :
    WP isa modulusR2 s (PpReady g bs) := by
  have pSub : (⟨State.addr (crtP g.base g.words), 8 * workspaceWords g.words⟩ : Region).Sub
      ⟨State.addr g.base, g.size⟩ :=
    crt_region_sub_workspace h.1.buffers.workspace h.1.buffers.storageFits (by simp [crtRegions])
  refine WP.mono (pp_modulusR2_ok s h.1) ?_
  rintro t ⟨shared, _, r2, frame, rest⟩
  refine ⟨⟨shared, h.2.1.after rest, ?_⟩, r2⟩
  rw [rest.sp, ← h.2.2]
  refine frame.readW (r := ⟨off (State.addr s.sp) 48, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (h.1.stack.separate.sub_right pSub).sub_left (Offset.sub_base _ (by decide))
  · exact Offset.disjoint_base _ (by decide) (by decide)

/-- A factor's phase keeps p's workspace. -/
theorem PpReady.after_phase {g : CrtGeometry} {bs : Fin 7 → List Byte} {s t : State} {d : BitVec 32} {n : Nat}
    (h : PpReady g bs s) (dest : PpDest g d n s) (checked : PpChecked g bs t)
    (frame : Frame [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩, ⟨State.addr s.sp, 4⟩,
      ⟨State.addr d, n⟩] s.mem t.mem) : PpReady g bs t := by
  have pSub : (⟨State.addr (crtP g.base g.words), 8 * workspaceWords g.words⟩ : Region).Sub
      ⟨State.addr g.base, g.size⟩ :=
    crt_region_sub_workspace h.1.1.buffers.workspace h.1.1.buffers.storageFits (by simp [crtRegions])
  have sepP := (h.1.1.child (child := crtP g.base g.words) (slot := 224) (Or.inl ⟨rfl, rfl⟩)).2.2.2.1
  refine ⟨checked, (h.1.1.p_num (regions := [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩,
    ⟨State.addr d, n⟩]) (frame.mono (by simp)) (fun r hr => ?_) (by decide)).trans h.2⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact sepP
  · exact dest.workspace.sub_left pSub

theorem pp_phaseP_wp (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} (h : PpReady g bs s) :
    WP isa (phase 64 pDest) s (PpReady g bs) := by
  have pre := h.1.2.1
  have words : g.words ≤ 128 := (crt_width_valid h.1.1.buffers.lengthValid).2.1
  have wordsLen : g.length ≤ 8 * g.words := by
    change g.length ≤ 8 * Spec.Rsa.modulusWords g.length; simp only [Spec.Rsa.modulusWords]; omega_using []
  have twoP := pre.words_le
  have dest : PpDest g (ppDestP g) (8 * ppWords g.pLength) s :=
    pre.dest wordsLen (by have := h.1.1.buffers.pShort; omega_using [wordsLen, this]) pre.addrP (Nat.le_refl _)
      (by simp only [ppPreWords]; omega_using [])
  have fac := h.1.factor 1 (Or.inl rfl)
  refine WP.mono (pp_phase_ok s h.1.1 1 (Or.inl rfl) (fun u hu => pp_pDest_ok u hu) dest fac.2.1 fac.2.2
    (fun ne => ⟨Spec.Rsa.os2ip (bs 3), (h.1.accepted ne).2.2.symm⟩) h.2) ?_
  rintro t ⟨shared, flag, _, frame, rest⟩
  refine h.after_phase dest ⟨shared, pre.after rest, ?_⟩ frame
  rw [← h.1.2.2]; exact BitVec.eq_of_toNat_eq flag

theorem pp_phaseQ_wp (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} (h : PpReady g bs s) :
    WP isa (phase 72 qDest) s (PpReady g bs) := by
  have pre := h.1.2.1
  have words : g.words ≤ 128 := (crt_width_valid h.1.1.buffers.lengthValid).2.1
  have wordsLen : g.length ≤ 8 * g.words := by
    change g.length ≤ 8 * Spec.Rsa.modulusWords g.length; simp only [Spec.Rsa.modulusWords]; omega_using []
  have twoP := pre.words_le
  have dest : PpDest g (ppDestQ g) (8 * ppWords g.qLength) s :=
    pre.dest wordsLen (by have := h.1.1.buffers.pShort; omega_using [wordsLen, this]) pre.addrQ (by omega_using [])
      (by simp only [ppPreWords]; omega_using [])
  have fac := h.1.factor 2 (Or.inr rfl)
  refine WP.mono (pp_phase_ok s h.1.1 2 (Or.inr rfl) (fun u hu => pp_qDest_ok u hu) dest fac.2.1 fac.2.2
    (fun ne => ⟨Spec.Rsa.os2ip (bs 2), by rw [Nat.mul_comm]; exact (h.1.accepted ne).2.2.symm⟩) h.2) ?_
  rintro t ⟨shared, flag, _, frame, rest⟩
  refine h.after_phase dest ⟨shared, pre.after rest, ?_⟩ frame
  rw [← h.1.2.2]; exact BitVec.eq_of_toNat_eq flag

theorem pp_valid_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte}
    (hn : Spec.Rsa.os2ip (bs1 0) = Spec.Rsa.os2ip (bs2 0)) :
    RelCT isa (fun s t => (PpValidInput g bs1 s ∧ PpPre g s) ∧ (PpValidInput g bs2 t ∧ PpPre g t) ∧ s.sp = t.sp)
      valid (fun _ _ => True) := by
  let V1 := fun (bs : Fin 7 → List Byte) (s : State) => CrtSelected g bs g.base s ∧ PpPre g s
  have prepareWP (s : State) {bs : Fin 7 → List Byte} (h : PpValidInput g bs s ∧ PpPre g s) :
      WP isa CrtFn.prepare s (V1 bs) :=
    (crt_begin_ok s h.1.buffers h.1.stack h.1.ptr h.1.count h.1.saved h.1.modulusPtr h.1.valid).mono
      fun _ j => ⟨⟨j.1, j.2.1⟩, h.2.after j.2.2.2⟩
  have prepareCT : RelCT isa (fun s t => (PpValidInput g bs1 s ∧ PpPre g s) ∧ (PpValidInput g bs2 t ∧ PpPre g t) ∧
      s.sp = t.sp) CrtFn.prepare (fun _ _ => True) :=
    crt_prepare_ct.mono (fun _ _ h => ⟨h.1.1.prepare_input, h.2.1.1.prepare_input, h.2.2⟩) (fun _ _ _ => trivial)
  have validateWP (s : State) {bs : Fin 7 → List Byte} (h : V1 bs s) :
      WP isa (CrtFn.validateWith (validateProductWith lengthCount)) s (PpChecked g bs) := by
    obtain ⟨p0, pLe, q0, qLe, pFit, qFit⟩ := pp_lengthCounts h.1.1
    exact (crt_validateStageWith_ok s h.1.1 h.1.2 (fun x hx => countFrom_lengthCount hx) p0 pLe q0 qLe pFit
      qFit).mono fun _ j => ⟨j.1, h.2.after j.2.2.2.2.2.2, j.2.2.2.2.1⟩
  have validateCT : RelCT isa (fun s t => V1 bs1 s ∧ V1 bs2 t ∧ s.sp = t.sp)
      (CrtFn.validateWith (validateProductWith lengthCount)) (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    obtain ⟨p0, pLe, q0, qLe, -, -⟩ := pp_lengthCounts h.1.1.1
    exact crt_validateStageWith_ct (fun x hx => countFrom_lengthCount hx) p0 pLe q0 qLe lengthCount_ct
      s t tr1 tr2 u v ⟨h.1.1, h.2.1.1, h.2.2⟩ e1 e2
  have modR2CT : RelCT isa (fun s t => PpChecked g bs1 s ∧ PpChecked g bs2 t ∧ s.sp = t.sp) modulusR2
      (fun _ _ => True) :=
    (pp_modulusR2_ct hn).mono (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ _ => trivial)
  have phasePCT : RelCT isa (fun s t => PpReady g bs1 s ∧ PpReady g bs2 t ∧ s.sp = t.sp)
      (phase 64 pDest) (fun _ _ => True) :=
    (pp_phase_ct (g := g) (bs1 := bs1) (bs2 := bs2) 1 (Or.inl rfl) (dest := pDest) (d := ppDestP g)
      (fun _ u hu => pp_pDest_ok u hu) (fun h1 h2 => pp_pDest_ct h1 h2)).mono
      (fun _ _ h => ⟨h.1.1.factor 1 (Or.inl rfl), h.2.1.1.factor 1 (Or.inl rfl), h.2.2⟩) (fun _ _ _ => trivial)
  have phaseQCT : RelCT isa (fun s t => PpReady g bs1 s ∧ PpReady g bs2 t ∧ s.sp = t.sp)
      (phase 72 qDest) (fun _ _ => True) :=
    (pp_phase_ct (g := g) (bs1 := bs1) (bs2 := bs2) 2 (Or.inr rfl) (dest := qDest) (d := ppDestQ g)
      (fun _ u hu => pp_qDest_ok u hu) (fun h1 h2 => pp_qDest_ct h1 h2)).mono
      (fun _ _ h => ⟨h.1.1.factor 2 (Or.inr rfl), h.2.1.1.factor 2 (Or.inr rfl), h.2.2⟩) (fun _ _ _ => trivial)
  have modCT : RelCT isa (fun s t => PpReady g bs1 s ∧ PpReady g bs2 t ∧ s.sp = t.sp) modulusPart
      (fun _ _ => True) :=
    pp_modulusPart_ct.mono (fun _ _ h => ⟨⟨h.1.1.1, h.1.1.2.1, (h.1.1.factor 1 (Or.inl rfl)).2.1⟩,
      ⟨h.2.1.1.1, h.2.1.1.2.1, (h.2.1.1.factor 1 (Or.inl rfl)).2.1⟩, h.2.2⟩) (fun _ _ _ => trivial)
  rw [valid]
  exact crt_seq_ct prepareCT (fun s h => prepareWP s h) (fun s h => prepareWP s h)
    (crt_seq_ct validateCT (fun s h => validateWP s h) (fun s h => validateWP s h)
      (crt_seq_ct modR2CT (fun s h => pp_modulusR2_wp s h) (fun s h => pp_modulusR2_wp s h)
        (crt_seq_ct phasePCT (fun s h => pp_phaseP_wp s h) (fun s h => pp_phaseP_wp s h)
          (crt_seq_ct phaseQCT (fun s h => pp_phaseQ_wp s h) (fun s h => pp_phaseQ_wp s h) modCT))))

end VG.Proof.Bignum.Arm

end

end

/-! # The precomputation's body and the CRT's frame around it leak only the modulus -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.PrivPreFn VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem pp_body_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} (modulus : bs1 0 = bs2 0) :
    RelCT isa (fun s t => (CrtBodyInput g bs1 s ∧ PpPre g s) ∧ (CrtBodyInput g bs2 t ∧ PpPre g t) ∧ s.sp = t.sp)
      body (fun _ _ => True) := by
  let Checked := fun (bs : Fin 7 → List Byte) (s : State) => (CrtBodyInput g bs s ∧ PpPre g s) ∧
    s.z = Spec.Rsa.modulusValid (Spec.Rsa.os2ip (bs 0)) g.length
  have checkWP (s : State) {bs : Fin 7 → List Byte} (h : CrtBodyInput g bs s ∧ PpPre g s) :
      WP isa (.block modulusCheck) s (Checked bs) := by
    refine WP.mono (modulusCheck_ok s h.1.buffers.lengthValid.1 h.1.buffers.lengthValid.2
      (h.1.buffers.source 0).fits (h.1.buffers.source 0).read h.1.source h.1.count) ?_
    rintro t ⟨flag, mem, rest⟩
    have nb : Spec.Rsa.bytesAt s.mem (State.addr g.modulus) g.length = bs 0 := (h.1.buffers.source 0).bytes
    change t.z = Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr g.modulus) g.length)) g.length at flag
    rw [nb] at flag
    exact ⟨⟨h.1.of_mem mem rest ((rest.gpr .r0 (by decide)).trans h.1.ptr)
      ((rest.gpr .r4 (by decide)).trans h.1.source) ((rest.gpr .r6 (by decide)).trans h.1.count), h.2.after rest⟩, flag⟩
  have check : RelCT isa (fun s t => (CrtBodyInput g bs1 s ∧ PpPre g s) ∧ (CrtBodyInput g bs2 t ∧ PpPre g t) ∧
      s.sp = t.sp) (.block modulusCheck) (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    exact ⟨modulusCheck_ct s t tr1 tr2 u v trivial trivial
      ⟨h.1.1.source.trans h.2.1.1.source.symm, h.1.1.count.trans h.2.1.1.count.symm⟩ e1 e2, trivial⟩
  have ready := (relCT_keep_sp check (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨checkWP s h.1, checkWP t h.2.1⟩)
  refine ready.seq (RelCT.ite ?_ ?_ ?_)
  · intro s t h
    change some s.z = some t.z
    rw [h.2.1.2, h.2.2.2, modulus]
  · apply (pp_valid_ct (g := g) (bs1 := bs1) (bs2 := bs2) (by rw [modulus])).mono ?_ (fun _ _ _ => trivial)
    intro s t h
    have flag : s.z = true := Option.some.inj h.2
    have good := h.1.2.1.2.symm.trans flag
    have good2 : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (bs2 0)) g.length = true := by rw [← modulus]; exact good
    let a := h.1.2.1.1.1
    let b := h.1.2.2.1.1
    exact ⟨⟨⟨a.buffers, a.stack, a.ptr, a.count, a.saved, a.modulusPtr, good⟩, h.1.2.1.1.2⟩,
      ⟨⟨b.buffers, b.stack, b.ptr, b.count, b.saved, b.modulusPtr, good2⟩, h.1.2.2.1.2⟩, h.1.1⟩
  · apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)

theorem PpPre.expanded {g : CrtGeometry} {s : State} (h : PpPre g s) : PpPre g (crtExpanded s g.base g.words) :=
  ⟨h.fit, (by obtain ⟨r, hr, hc⟩ := h.write; exact ⟨r, List.mem_append_right _ hr, hc⟩), h.workspace, h.stack,
    h.sources, h.input, h.qi, h.noR2⟩

theorem pp_body_scoped_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} (modulus : bs1 0 = bs2 0) :
    RelCT isa (fun s t =>
      (CrtScopedInput g bs1 s ∧ PpPre g s ∧
        Spec.Rsa.wordsAt s.mem (State.addr g.output) (ppPreWords g) = List.replicate (ppPreWords g) 0) ∧
      (CrtScopedInput g bs2 t ∧ PpPre g t ∧
        Spec.Rsa.wordsAt t.mem (State.addr g.output) (ppPreWords g) = List.replicate (ppPreWords g) 0) ∧
      s.sp = t.sp) body (fun _ _ => True) := by
  intro s t tr1 tr2 u v h e1 e2
  obtain ⟨trS, uS, runS, _⟩ := pp_body_ok _ h.1.1.body h.1.2.1.expanded h.1.2.2
  obtain ⟨trT, uT, runT, _⟩ := pp_body_ok _ h.2.1.1.body h.2.1.2.1.expanded h.2.1.2.2
  obtain ⟨writeS, readS⟩ := crt_expanded_covers h.1.1.workspace h.1.1.body.buffers.storageFits
  obtain ⟨writeT, readT⟩ := crt_expanded_covers h.2.1.1.workspace h.2.1.1.body.buffers.storageFits
  have wideS : Exec isa body s trS (uS.withRegions s.rd s.wr) := by
    simpa only [crtExpanded, State.withRegions_withRegions, State.withRegions_self] using VG.Arm.Exec.widen runS readS writeS
  have wideT : Exec isa body t trT (uT.withRegions t.rd t.wr) := by
    simpa only [crtExpanded, State.withRegions_withRegions, State.withRegions_self] using VG.Arm.Exec.widen runT readT writeT
  have trace := pp_body_ct modulus _ _ _ _ _ _
    ⟨⟨h.1.1.body, h.1.2.1.expanded⟩, ⟨h.2.1.1.body, h.2.1.2.1.expanded⟩, h.2.2⟩ runS runT
  exact ⟨(Exec.det e1 wideS).1.trans (trace.1.trans (Exec.det e2 wideT).1.symm), trivial⟩

theorem pp_crtFrame_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} (modulus : bs1 0 = bs2 0) :
    RelCT isa (fun s t => (CrtFnInput g bs1 s ∧ PpCall g s) ∧ (CrtFnInput g bs2 t ∧ PpCall g t) ∧ s.sp = t.sp)
      crtFrame (fun _ _ => True) := by
  unfold crtFrame
  apply RelCT.frame (fun _ _ h => h.2.2)
  intro s t tr1 tr2 u v hp e1 e2
  obtain ⟨s0, t0, ⟨hs, ht, sp⟩, ps, pt⟩ := hp
  have ps' := push_pushed
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) (by decide) hs.1.stackFit
  have pt' := push_pushed
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) (by decide) ht.1.stackFit
  have es : pcPushed s0 = s := Option.some.inj (ps'.symm.trans ps)
  have et : pcPushed t0 = t := Option.some.inj (pt'.symm.trans pt)
  subst s; subst t
  have prep (x : State) {bs : Fin 7 → List Byte} (hx : CrtFnInput g bs x ∧ PpCall g x) :
      WP isa (.block CrtFn.entry) (pcPushed x) fun y => CrtScopedInput g bs y ∧ PpPre g y ∧
        Spec.Rsa.wordsAt y.mem (State.addr g.output) (ppPreWords g) = List.replicate (ppPreWords g) 0 := by
    refine WP.mono (crt_entry_ready x hx.1) ?_
    rintro y ⟨ready, frameY, _, restY⟩
    refine ⟨ready, ⟨hx.2.fit, ?_, hx.2.workspace, ?_, hx.2.sources, hx.2.input, hx.2.qi, hx.2.noR2⟩, ?_⟩
    · rw [restY.wr]; obtain ⟨r, hr, hc⟩ := hx.2.write; exact ⟨r, List.mem_cons_of_mem _ hr, hc⟩
    · rw [restY.sp]; exact pp_push_separate hx.1.stackFit hx.2.below hx.2.args
    · rw [Proof.Rsa.wordsAt_frame frameY (by have := hx.2.fit; omega_using [this])
        (fun r hr => by simp only [List.mem_singleton] at hr; subst r; exact hx.2.below.symm)]
      exact hx.2.cleared
  cases e1 with
  | seq entry1 tail1 =>
    cases e2 with
    | seq entry2 tail2 =>
      obtain ⟨trace, sp'⟩ := crt_entry_ct _ _ _ _ _ _ (by simp only [pcPushed, pushed_sp, sp]) entry1 entry2
      obtain ⟨_, s1, run1, ready1⟩ := prep s0 hs
      obtain ⟨_, t1, run2, ready2⟩ := prep t0 ht
      obtain ⟨-, rfl⟩ := Exec.det entry1 run1
      obtain ⟨-, rfl⟩ := Exec.det entry2 run2
      have bodyCT := relCT_keep_sp (pp_body_scoped_ct (g := g) modulus) (fun _ _ h => h.2.2)
      have restore : RelCT isa (fun s t => s.sp = t.sp) (.block PcFn.restore) (fun s t => s.sp = t.sp) :=
        stackLoads_ct pcCalleeSaved
      obtain ⟨tailTrace, _⟩ := bodyCT.seq restore _ _ _ _ _ _ ⟨ready1, ready2, sp'⟩ tail1 tail2
      exact ⟨by rw [trace, tailTrace], trivial⟩

end VG.Proof.Bignum.Arm

end

end

/-! ### `Bignum.Arm.PrivPreFn`, which only this module used -/

section

/-! # The callable private precomputation

The caller's frame is saved and `pre` cleared; a second frame pushes the
private CRT's stack arguments, and the CRT's own frame runs the body.
-/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.PrivPreFn VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_mov op2_reg op2_imm op2_lsl)

/-- The private CRT's arguments: the input and the coefficient are `pre`, the
exponents the factors. -/
def ppGeometry (s : State) : CrtGeometry where
  base := stackArg s 4
  output := s.gpr .r0
  modulus := s.gpr .r2
  input := s.gpr .r0
  p := stackArg s 0
  q := stackArg s 2
  dp := stackArg s 0
  dq := stackArg s 2
  qi := s.gpr .r0
  size := (stackArg s 5).toNat * 8
  length := (s.gpr .r3).toNat
  pLength := (stackArg s 1).toNat
  qLength := (stackArg s 3).toNat

/-- The sources' bytes when the CRT runs: the input and the coefficient cleared. -/
def ppBytes (s : State) (i : Fin 7) : List Byte :=
  if i = 1 ∨ i = 6 then List.replicate ((ppGeometry s).sourceLength i) 0
  else Spec.Rsa.bytesAt s.mem (State.addr ((ppGeometry s).source i)) ((ppGeometry s).sourceLength i)

theorem ppBytes_other (s : State) (i : Fin 7) (h1 : i ≠ 1) (h6 : i ≠ 6) :
    ppBytes s i = Spec.Rsa.bytesAt s.mem (State.addr ((ppGeometry s).source i)) ((ppGeometry s).sourceLength i) := by
  unfold ppBytes
  split
  · next hc => rcases hc with hc | hc <;> contradiction
  · rfl

theorem ppBytes_zero (s : State) (i : Fin 7) (h : i = 1 ∨ i = 6) :
    ppBytes s i = List.replicate ((ppGeometry s).sourceLength i) 0 := by
  unfold ppBytes
  split
  · rfl
  · next hc => exact absurd h hc

/-- The contract's precondition, named. -/
structure PpFnInput (s : State) : Prop where
  stackFit : 168 ≤ s.sp.toNat
  argFit : s.sp.toNat + 24 ≤ 2 ^ 32
  argRead : (⟨State.addr s.sp, 24⟩ : Region) ∈ s.rd
  preW : (⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat * 8⟩ : Region) ∈ s.wr
  wsW : (⟨State.addr (stackArg s 4), (stackArg s 5).toNat * 8⟩ : Region) ∈ s.wr
  nR : (⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩ : Region) ∈ s.rd
  pR : (⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩ : Region) ∈ s.rd
  qR : (⟨State.addr (stackArg s 2), (stackArg s 3).toNat⟩ : Region) ∈ s.rd
  preN : Region.Disjoint ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat * 8⟩ ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
  preP : Region.Disjoint ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat * 8⟩ ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩
  preQ : Region.Disjoint ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat * 8⟩ ⟨State.addr (stackArg s 2), (stackArg s 3).toNat⟩
  preWs : Region.Disjoint ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat * 8⟩
    ⟨State.addr (stackArg s 4), (stackArg s 5).toNat * 8⟩
  preArgs : Region.Disjoint ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat * 8⟩ ⟨State.addr s.sp, 24⟩
  nWs : Region.Disjoint ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩ ⟨State.addr (stackArg s 4), (stackArg s 5).toNat * 8⟩
  pWs : Region.Disjoint ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩ ⟨State.addr (stackArg s 4), (stackArg s 5).toNat * 8⟩
  qWs : Region.Disjoint ⟨State.addr (stackArg s 2), (stackArg s 3).toNat⟩ ⟨State.addr (stackArg s 4), (stackArg s 5).toNat * 8⟩
  stPre : (FrameStack.belowA s.sp 168).Disjoint ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat * 8⟩
  stN : (FrameStack.belowA s.sp 168).Disjoint ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
  stP : (FrameStack.belowA s.sp 168).Disjoint ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩
  stQ : (FrameStack.belowA s.sp 168).Disjoint ⟨State.addr (stackArg s 2), (stackArg s 3).toNat⟩
  stWs : (FrameStack.belowA s.sp 168).Disjoint ⟨State.addr (stackArg s 4), (stackArg s 5).toNat * 8⟩
  stArgs : (FrameStack.belowA s.sp 168).Disjoint ⟨State.addr s.sp, 24⟩
  /-- The 216 bytes of the contract's stack: the 168 of the frames and the 48
  of a call the CRT makes from its own. -/
  stackFit216 : 216 ≤ s.sp.toNat
  st216Pre : (FrameStack.belowA s.sp 216).Disjoint ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat * 8⟩
  st216N : (FrameStack.belowA s.sp 216).Disjoint ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
  st216P : (FrameStack.belowA s.sp 216).Disjoint ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩
  st216Q : (FrameStack.belowA s.sp 216).Disjoint ⟨State.addr (stackArg s 2), (stackArg s 3).toNat⟩
  st216Ws : (FrameStack.belowA s.sp 216).Disjoint ⟨State.addr (stackArg s 4), (stackArg s 5).toNat * 8⟩
  preFit : (s.gpr .r0).toNat + (s.gpr .r1).toNat * 8 ≤ 2 ^ 32
  nFit : (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32
  pFit : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 32
  qFit : (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 32
  wsFit : (stackArg s 4).toNat + (stackArg s 5).toNat * 8 ≤ 2 ^ 32
  valid : Spec.Rsa.lenValid (s.gpr .r3).toNat
  pPositive : 1 ≤ (stackArg s 1).toNat
  pShort : (stackArg s 1).toNat < (s.gpr .r3).toNat
  qPositive : 1 ≤ (stackArg s 3).toNat
  qShort : (stackArg s 3).toNat < (s.gpr .r3).toNat
  preLen : (s.gpr .r1).toNat =
    Spec.Rsa.privatePrecomputedWords (s.gpr .r3).toNat (stackArg s 1).toNat (stackArg s 3).toNat
  space : Spec.Rsa.scratchWords (s.gpr .r3).toNat ≤ (stackArg s 5).toNat

theorem pp_contract_pre (s : State) (h : (Spec.Rsa.privatePrecomputeContract abi 216).pre s) :
    PpFnInput s := by
  sig_pre [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs, reduceClassify,
    Loc.val] at h
  obtain argAddr : stackArgAddr s 0 = State.addr s.sp := by simp [stackArgAddr]
  rw [argAddr] at h
  obtain ⟨stackFit216, argFit, rd, wr, preN, preP, preQ, preWs, preArgs, nWs, pWs, qWs, _,
    stPre, stN, stP, stQ, stWs, stArgs, preFit, nFit, pFit, qFit, wsFit,
    valid, pPositive, pShort, qPositive, qShort, preLen, space⟩ := h
  obtain stackFit : 168 ≤ s.sp.toNat := by omega_using [stackFit216]
  obtain below : FrameStack.belowA s.sp 216 = ⟨State.addr s.sp - BitVec.ofNat 64 216, 216⟩ := by
    unfold FrameStack.belowA
    rw [FrameStack.addr_sub' stackFit216]
  obtain sub : Region.Sub (FrameStack.belowA s.sp 168) (FrameStack.belowA s.sp 216) :=
    FrameStack.belowA_sub (by decide) stackFit216
  refine ⟨stackFit, argFit, by rw [rd]; simp [State.addr], by rw [wr]; simp [State.addr], by rw [wr]; simp [State.addr],
    by rw [rd]; simp [State.addr], by rw [rd]; simp [State.addr], by rw [rd]; simp [State.addr],
    preN, preP, preQ, preWs, preArgs, nWs, pWs, qWs,
    Region.Disjoint.sub_left (by rw [below]; exact stPre) sub, Region.Disjoint.sub_left (by rw [below]; exact stN) sub,
    Region.Disjoint.sub_left (by rw [below]; exact stP) sub, Region.Disjoint.sub_left (by rw [below]; exact stQ) sub,
    Region.Disjoint.sub_left (by rw [below]; exact stWs) sub, Region.Disjoint.sub_left (by rw [below]; exact stArgs) sub,
    stackFit216, by rw [below]; exact stPre, by rw [below]; exact stN, by rw [below]; exact stP,
    by rw [below]; exact stQ, by rw [below]; exact stWs,
    preFit, nFit, pFit, qFit, wsFit, valid, pPositive, pShort, qPositive, qShort, preLen, space⟩

/-! ## Helpers -/

/-- Bytes read as zero are zero. -/
theorem byte_zero_of_read {m : Mem} {a : Addr} {n i : Nat} (h : (m.read a n).toNat = 0) (hi : i < n) :
    m (a + BitVec.ofNat 64 i) = 0 := by
  obtain split := read_toNat_add m (n - i) i a
  rw [show n - i + i = n by omega_using [hi], h] at split
  obtain high : (m.read (a + BitVec.ofNat 64 i) (n - i)).toNat = 0 := by
    have := Nat.two_pow_pos (8 * i)
    rcases Nat.eq_zero_of_add_eq_zero split.symm with ⟨_, h2⟩
    exact (Nat.mul_eq_zero.mp h2).resolve_left (by omega_using [split])
  rw [show n - i = n - i - 1 + 1 by omega_using [hi], read_toNat_succ] at high
  apply BitVec.eq_of_toNat_eq
  have := Nat.eq_zero_of_add_eq_zero high
  exact this.1

theorem bytesAt_zero_of_read {m : Mem} {a : Addr} {n k : Nat} (h : (m.read a n).toNat = 0) (hk : k ≤ n) :
    Spec.Rsa.bytesAt m a k = List.replicate k 0 := by
  apply List.ext_getElem
  · simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range, List.length_replicate]
  · intro i hi _
    obtain hi' : i < k := by simpa only [Spec.Rsa.bytesAt, List.length_map, List.length_range] using hi
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
    exact byte_zero_of_read h (by omega_using [hk, hi'])

/-- The three frames below the caller's stack pointer: the caller's
registers', the CRT's arguments' and the CRT's own, at `112`, `56` and `0`
bytes above `sp - 168`. -/
theorem pp_stack_addrs {sp : BitVec 32} (fit : 168 ≤ sp.toNat) :
    FrameStack.belowA sp 168 = ⟨State.addr sp - BitVec.ofNat 64 168, 168⟩ ∧
    State.addr (sp - BitVec.ofNat 32 56) = State.addr sp - BitVec.ofNat 64 168 + BitVec.ofNat 64 112 ∧
    State.addr (sp - BitVec.ofNat 32 56 - BitVec.ofNat 32 56) =
      State.addr sp - BitVec.ofNat 64 168 + BitVec.ofNat 64 56 ∧
    State.addr (sp - BitVec.ofNat 32 56 - BitVec.ofNat 32 56 - BitVec.ofNat 32 56) =
      State.addr sp - BitVec.ofNat 64 168 := by
  obtain a1 : (sp - BitVec.ofNat 32 56).toNat = sp.toNat - 56 := FrameStack.sub_toNat' (by omega_using [fit])
  obtain a2 : (sp - BitVec.ofNat 32 56 - BitVec.ofNat 32 56).toNat = sp.toNat - 112 := by
    rw [FrameStack.sub_toNat' (by omega_using [fit, a1]), a1]; omega_using []
  have lt := sp.isLt
  have eq (x : BitVec 32) (k : Nat) (hx : x.toNat = sp.toNat - k) (hk : k ≤ 168) :
      State.addr x = State.addr sp - BitVec.ofNat 64 168 + BitVec.ofNat 64 (168 - k) := by
    apply BitVec.eq_of_toNat_eq
    simp only [State.addr, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, hx]
    omega_using [fit, hk]
  refine ⟨?_, eq _ 56 a1 (by decide), eq _ 112 a2 (by decide), ?_⟩
  · unfold FrameStack.belowA; rw [FrameStack.addr_sub' fit]
  · have := eq (sp - BitVec.ofNat 32 56 - BitVec.ofNat 32 56 - BitVec.ofNat 32 56) 168
      (by rw [FrameStack.sub_toNat' (by omega_using [fit, a2]), a2]; omega_using []) (by decide)
    simpa only [Nat.sub_self, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this

theorem pp_loadArgs_ok (x : State) (fit : x.sp.toNat + 76 ≤ 2 ^ 32)
    (read : ∀ d, d + 4 ≤ 56 ∨ 56 ≤ d ∧ d + 4 ≤ 76 → InRegions (x.rd ++ x.wr) (off (State.addr x.sp) d) 4) :
    WP isa (.block loadArgs) x fun t =>
      let v := fun d => x.mem.readW (off (State.addr x.sp) d) 32
      t.gpr .r0 = v 0 ∧ t.gpr .r1 = v 12 ∧ t.gpr .r2 = v 56 ∧ t.gpr .r3 = v 60 ∧ t.gpr .r4 = v 64 ∧
      t.gpr .r5 = v 68 ∧ t.gpr .r6 = v 56 ∧ t.gpr .r7 = v 60 ∧ t.gpr .r8 = v 64 ∧ t.gpr .r9 = v 68 ∧
      t.gpr .r10 = v 0 ∧ t.gpr .r11 = v 60 ∧ t.gpr .r12 = v 72 ∧ t.mem = x.mem ∧
      Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12] x t := by
  unfold loadArgs
  have ld (d : Nat) (hd : d + 4 ≤ 76) := addr_add (a := x.sp) (k := d) (by omega_using [fit, hd])
  refine wp_loadStack (a := off (State.addr x.sp) 0) (by decide) (ld 0 (by decide)) (read 0 (Or.inl (by decide))) fun a1 h1 => ?_
  refine wp_loadStack (a := off (State.addr x.sp) 12) (by decide) (by rw [h1.sp]; exact ld 12 (by decide))
    (by rw [h1.rd, h1.wr]; exact read 12 (Or.inl (by decide))) fun a2 h2 => ?_
  refine wp_loadStack (a := off (State.addr x.sp) 56) (by decide) (by rw [h2.sp, h1.sp]; exact ld 56 (by decide))
    (by rw [h2.rd, h2.wr, h1.rd, h1.wr]; exact read 56 (Or.inr ⟨by decide, by decide⟩)) fun a3 h3 => ?_
  refine wp_loadStack (a := off (State.addr x.sp) 60) (by decide) (by rw [h3.sp, h2.sp, h1.sp]; exact ld 60 (by decide))
    (by rw [h3.rd, h3.wr, h2.rd, h2.wr, h1.rd, h1.wr]; exact read 60 (Or.inr ⟨by decide, by decide⟩)) fun a4 h4 => ?_
  refine wp_loadStack (a := off (State.addr x.sp) 64) (by decide)
    (by rw [h4.sp, h3.sp, h2.sp, h1.sp]; exact ld 64 (by decide))
    (by rw [h4.rd, h4.wr, h3.rd, h3.wr, h2.rd, h2.wr, h1.rd, h1.wr]; exact read 64 (Or.inr ⟨by decide, by decide⟩)) fun a5 h5 => ?_
  refine wp_loadStack (a := off (State.addr x.sp) 68) (by decide)
    (by rw [h5.sp, h4.sp, h3.sp, h2.sp, h1.sp]; exact ld 68 (by decide))
    (by rw [h5.rd, h5.wr, h4.rd, h4.wr, h3.rd, h3.wr, h2.rd, h2.wr, h1.rd, h1.wr]; exact read 68 (Or.inr ⟨by decide, by decide⟩))
    fun a6 h6 => ?_
  refine wp_mov (op2_reg _ _) fun a7 h7 => ?_
  refine wp_mov (op2_reg _ _) fun a8 h8 => ?_
  refine wp_mov (op2_reg _ _) fun a9 h9 => ?_
  refine wp_mov (op2_reg _ _) fun a10 h10 => ?_
  refine wp_mov (op2_reg _ _) fun a11 h11 => ?_
  refine wp_mov (op2_reg _ _) fun a12 h12 => ?_
  refine wp_loadStack (a := off (State.addr x.sp) 72) (by decide)
    (by rw [h12.sp, h11.sp, h10.sp, h9.sp, h8.sp, h7.sp, h6.sp, h5.sp, h4.sp, h3.sp, h2.sp, h1.sp]
        exact ld 72 (by decide))
    (by rw [h12.rd, h12.wr, h11.rd, h11.wr, h10.rd, h10.wr, h9.rd, h9.wr, h8.rd, h8.wr, h7.rd, h7.wr,
          h6.rd, h6.wr, h5.rd, h5.wr, h4.rd, h4.wr, h3.rd, h3.wr, h2.rd, h2.wr, h1.rd, h1.wr]
        exact read 72 (Or.inr ⟨by decide, by decide⟩)) fun t h13 => WP.block_nil ?_
  obtain m12 : a12.mem = x.mem := by
    rw [h12.mem, h11.mem, h10.mem, h9.mem, h8.mem, h7.mem, h6.mem, h5.mem, h4.mem, h3.mem, h2.mem, h1.mem]
  obtain g6 : a6.gpr .r0 = x.mem.readW (off (State.addr x.sp) 0) 32 ∧ a6.gpr .r1 = x.mem.readW (off (State.addr x.sp) 12) 32 ∧
      a6.gpr .r2 = x.mem.readW (off (State.addr x.sp) 56) 32 ∧ a6.gpr .r3 = x.mem.readW (off (State.addr x.sp) 60) 32 ∧
      a6.gpr .r4 = x.mem.readW (off (State.addr x.sp) 64) 32 ∧ a6.gpr .r5 = x.mem.readW (off (State.addr x.sp) 68) 32 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h6.other .r0 (by decide), h5.other .r0 (by decide), h4.other .r0 (by decide), h3.other .r0 (by decide),
        h2.other .r0 (by decide), h1.gpr]
    · rw [h6.other .r1 (by decide), h5.other .r1 (by decide), h4.other .r1 (by decide), h3.other .r1 (by decide),
        h2.gpr, h1.mem]
    · rw [h6.other .r2 (by decide), h5.other .r2 (by decide), h4.other .r2 (by decide), h3.gpr, h2.mem, h1.mem]
    · rw [h6.other .r3 (by decide), h5.other .r3 (by decide), h4.gpr, h3.mem, h2.mem, h1.mem]
    · rw [h6.other .r4 (by decide), h5.gpr, h4.mem, h3.mem, h2.mem, h1.mem]
    · rw [h6.gpr, h5.mem, h4.mem, h3.mem, h2.mem, h1.mem]
  obtain ⟨r0, r1, r2, r3, r4, r5⟩ := g6
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [h13.mem, m12], ?_⟩
  · rw [h13.other .r0 (by decide), h12.other .r0 (by decide), h11.other .r0 (by decide), h10.other .r0 (by decide),
      h9.other .r0 (by decide), h8.other .r0 (by decide), h7.other .r0 (by decide), r0]
  · rw [h13.other .r1 (by decide), h12.other .r1 (by decide), h11.other .r1 (by decide), h10.other .r1 (by decide),
      h9.other .r1 (by decide), h8.other .r1 (by decide), h7.other .r1 (by decide), r1]
  · rw [h13.other .r2 (by decide), h12.other .r2 (by decide), h11.other .r2 (by decide), h10.other .r2 (by decide),
      h9.other .r2 (by decide), h8.other .r2 (by decide), h7.other .r2 (by decide), r2]
  · rw [h13.other .r3 (by decide), h12.other .r3 (by decide), h11.other .r3 (by decide), h10.other .r3 (by decide),
      h9.other .r3 (by decide), h8.other .r3 (by decide), h7.other .r3 (by decide), r3]
  · rw [h13.other .r4 (by decide), h12.other .r4 (by decide), h11.other .r4 (by decide), h10.other .r4 (by decide),
      h9.other .r4 (by decide), h8.other .r4 (by decide), h7.other .r4 (by decide), r4]
  · rw [h13.other .r5 (by decide), h12.other .r5 (by decide), h11.other .r5 (by decide), h10.other .r5 (by decide),
      h9.other .r5 (by decide), h8.other .r5 (by decide), h7.other .r5 (by decide), r5]
  · rw [h13.other .r6 (by decide), h12.other .r6 (by decide), h11.other .r6 (by decide), h10.other .r6 (by decide),
      h9.other .r6 (by decide), h8.other .r6 (by decide), h7.gpr, r2]
  · rw [h13.other .r7 (by decide), h12.other .r7 (by decide), h11.other .r7 (by decide), h10.other .r7 (by decide),
      h9.other .r7 (by decide), h8.gpr, h7.other .r3 (by decide), r3]
  · rw [h13.other .r8 (by decide), h12.other .r8 (by decide), h11.other .r8 (by decide), h10.other .r8 (by decide),
      h9.gpr, h8.other .r4 (by decide), h7.other .r4 (by decide), r4]
  · rw [h13.other .r9 (by decide), h12.other .r9 (by decide), h11.other .r9 (by decide), h10.gpr,
      h9.other .r5 (by decide), h8.other .r5 (by decide), h7.other .r5 (by decide), r5]
  · rw [h13.other .r10 (by decide), h12.other .r10 (by decide), h11.gpr, h10.other .r0 (by decide),
      h9.other .r0 (by decide), h8.other .r0 (by decide), h7.other .r0 (by decide), r0]
  · rw [h13.other .r11 (by decide), h12.gpr, h11.other .r3 (by decide), h10.other .r3 (by decide),
      h9.other .r3 (by decide), h8.other .r3 (by decide), h7.other .r3 (by decide), r3]
  · rw [h13.gpr, m12]
  · have r1' : Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12] x a6 :=
      (h1.rest (by decide)).trans ((h2.rest (by decide)).trans ((h3.rest (by decide)).trans
        ((h4.rest (by decide)).trans ((h5.rest (by decide)).trans (h6.rest (by decide))))))
    obtain r2' : Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12] a6 a12 :=
      (h7.rest (by decide)).trans ((h8.rest (by decide)).trans ((h9.rest (by decide)).trans
        ((h10.rest (by decide)).trans ((h11.rest (by decide)).trans (h12.rest (by decide))))))
    exact r1'.trans (r2'.trans (h13.rest (by decide)))

theorem pp_preWords {s : State} (h : PpFnInput s) : (s.gpr .r1).toNat = ppPreWords (ppGeometry s) := by
  rw [h.preLen]; rfl

/-- The facts of `PpFnInput` its steps share: `pre`'s `P` words, and the
`168` bytes of stack from `B`, apart from every buffer. -/
structure PpLayout (s : State) (B : Addr) (P : Nat) : Prop where
  hPw : ppPreWords (ppGeometry s) = P
  hP : (s.gpr .r1).toNat = P
  lenP : (s.gpr .r1).toNat * 8 = 8 * P
  preFit : (s.gpr .r0).toNat + 8 * P ≤ 2 ^ 32
  a1 : State.addr (s.sp - BitVec.ofNat 32 56) = B + BitVec.ofNat 64 112
  a2 : State.addr (s.sp - BitVec.ofNat 32 56 - BitVec.ofNat 32 56) = B + BitVec.ofNat 64 56
  a3 : State.addr (s.sp - BitVec.ofNat 32 56 - BitVec.ofNat 32 56 - BitVec.ofNat 32 56) = B
  Bnat : B.toNat = s.sp.toNat - 168
  spB : State.addr s.sp = B + BitVec.ofNat 64 168
  preD : Region.Disjoint ⟨B, 168⟩ ⟨State.addr (s.gpr .r0), 8 * P⟩
  nD : Region.Disjoint ⟨B, 168⟩ ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
  pD : Region.Disjoint ⟨B, 168⟩ ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩
  qD : Region.Disjoint ⟨B, 168⟩ ⟨State.addr (stackArg s 2), (stackArg s 3).toNat⟩
  wsD : Region.Disjoint ⟨B, 168⟩ ⟨State.addr (stackArg s 4), (stackArg s 5).toNat * 8⟩
  preW : (⟨State.addr (s.gpr .r0), 8 * P⟩ : Region) ∈ s.wr

theorem pp_layout (s : State) (h : PpFnInput s) :
    PpLayout s (State.addr s.sp - BitVec.ofNat 64 168) (ppPreWords (ppGeometry s)) := by
  obtain hP := pp_preWords h
  obtain lenP : (s.gpr .r1).toNat * 8 = 8 * ppPreWords (ppGeometry s) := by rw [hP]; omega_using []
  obtain ⟨below168, a1, a2, a3⟩ := pp_stack_addrs h.stackFit
  refine ⟨rfl, hP, lenP, by have := h.preFit; omega_using [hP, this], a1, a2, a3, ?_, (BitVec.sub_add_cancel _ _).symm,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := h.stackFit
    simp only [State.addr, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega_using [this]
  · have := h.stPre; rw [below168, lenP] at this; exact this
  · have := h.stN; rw [below168] at this; exact this
  · have := h.stP; rw [below168] at this; exact this
  · have := h.stQ; rw [below168] at this; exact this
  · have := h.stWs; rw [below168] at this; exact this
  · have := h.preW; rw [lenP] at this; exact this

theorem PpLayout.stackSub {s : State} {B : Addr} {P : Nat} (_L : PpLayout s B P) (k : Nat) (hk : k + 56 ≤ 168) :
    Region.Sub ⟨B + BitVec.ofNat 64 k, 56⟩ ⟨B, 168⟩ := Offset.sub_base _ hk

/-- The frame that saves the caller's registers. -/
theorem PpLayout.frame1 {s : State} {B : Addr} {P : Nat} (L : PpLayout s B P) (h : PpFnInput s) :
    Frame [⟨B + BitVec.ofNat 64 112, 56⟩] s.mem (pcPushed s).mem := by
  have := FrameStack.pushed_frameA
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) (s := s)
    (by show 56 ≤ _; have := h.stackFit; omega_using [this])
  unfold FrameStack.belowA at this
  rw [show 4 * List.length [Reg.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr] = 56
    from rfl, L.a1] at this
  exact this

/-! ### `pre` cleared -/

def PpZeroReady (s : State) (P : Nat) (v : State) : Prop :=
  v.gpr .r0 = s.gpr .r0 ∧ v.gpr .lr = BitVec.ofNat 32 (2 * P) ∧ v.gpr .r3 = 0 ∧ v.mem = (pcPushed s).mem ∧
    Rest [.lr, .r3] (pcPushed s) v

theorem pp_zeroArgs_ok (s : State) {B : Addr} {P : Nat} (L : PpLayout s B P) :
    WP isa (.block zeroArgs) (pcPushed s) (PpZeroReady s P) := by
  refine wp_mov (op2_lsl ⟨by decide, by decide⟩) fun u a => ?_
  refine wp_mov (op2_imm (by decide)) fun v b => WP.block_nil ?_
  refine ⟨?_, ?_, by rw [b.gpr], by rw [b.mem, a.mem], (a.rest (by decide)).trans (b.rest (by decide))⟩
  · rw [b.other .r0 (by decide), a.other .r0 (by decide)]; simp
  · rw [b.other .lr (by decide), a.gpr]
    change s.gpr .r1 <<< 1 = _
    obtain e : s.gpr .r1 = BitVec.ofNat 32 (s.gpr .r1).toNat := by simp
    rw [e, shl_ofNat, L.hP]

structure PpZeroed (s : State) (P : Nat) (w : State) : Prop where
  rest : Rest [.r0, .lr, .r3] (pcPushed s) w
  frame : Frame [⟨State.addr (s.gpr .r0), 8 * P⟩] (pcPushed s).mem w.mem
  zero : (w.mem.read (State.addr (s.gpr .r0)) (8 * P)).toNat = 0

theorem pp_zero_ok (s : State) (h : PpFnInput s) {B : Addr} {P : Nat} (L : PpLayout s B P) (v : State)
    (hv : PpZeroReady s P v) : WP isa zero v (PpZeroed s P) := by
  obtain ⟨r0, lr, r3, memV, restV⟩ := hv
  refine WP.mono (zero_ok v (base := s.gpr .r0) (size := 8 * P) (o := 0) (n := 2 * P)
    ⟨L.preFit, by omega_using [], ?_⟩ (by have := h.pPositive; rw [← L.hPw]; simp only [ppPreWords, ppWords]; omega_using [])
    (by rw [r0]; simp) lr r3) ?_
  · rw [restV.wr]; exact ⟨_, List.mem_cons_of_mem _ L.preW, Region.contains_self _ _⟩
  rintro w ⟨_, _, _, outside, value, restW⟩
  refine ⟨(restV.mono (by decide)).trans (restW.mono (by decide)), ?_, ?_⟩
  · have := outside_frame outside (by have := L.preFit; omega_using [this])
    rw [memV, show 4 * (2 * P) = 8 * P by omega_using []] at this
    simpa only [off, BitVec.add_zero] using this
  · have := read_eq_val32 w.mem (State.addr (s.gpr .r0)) (2 * P) 0
    rw [value, show 4 * (2 * P) = 8 * P by omega_using []] at this
    simpa only [off, BitVec.add_zero] using this

/-! ### The CRT's stack arguments in registers -/

structure PpLoaded (s : State) (P : Nat) (x : State) : Prop where
  rest : Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr] (pcPushed s) x
  frame : Frame [⟨State.addr (s.gpr .r0), 8 * P⟩] (pcPushed s).mem x.mem
  zero : (x.mem.read (State.addr (s.gpr .r0)) (8 * P)).toNat = 0
  saved : Spill.Saved x.mem (State.addr x.sp) s.gpr pcAllSaved
  r0 : x.gpr .r0 = s.gpr .r0
  r1 : x.gpr .r1 = s.gpr .r3
  r2 : x.gpr .r2 = stackArg s 0
  r3 : x.gpr .r3 = stackArg s 1
  r4 : x.gpr .r4 = stackArg s 2
  r5 : x.gpr .r5 = stackArg s 3
  r6 : x.gpr .r6 = stackArg s 0
  r7 : x.gpr .r7 = stackArg s 1
  r8 : x.gpr .r8 = stackArg s 2
  r9 : x.gpr .r9 = stackArg s 3
  r10 : x.gpr .r10 = s.gpr .r0
  r11 : x.gpr .r11 = stackArg s 1
  r12 : x.gpr .r12 = stackArg s 4

theorem pp_load_ok (s : State) (h : PpFnInput s) {B : Addr} {P : Nat} (L : PpLayout s B P) (w : State)
    (hw : PpZeroed s P w) : WP isa (.block loadArgs) w (PpLoaded s P) := by
  have stackFit := h.stackFit
  have argFit := h.argFit
  have restW := hw.rest
  obtain spW : w.sp = s.sp - BitVec.ofNat 32 56 := by rw [restW.sp]; rfl
  have argAddr (d : Nat) (hd : d + 4 ≤ 24) :
      off (State.addr w.sp) (56 + d) = off (State.addr s.sp) d := by
    rw [spW]; exact public_push_argOffset (s := s) (by omega_using [stackFit]) d
  obtain savedW : Spill.Saved w.mem (State.addr w.sp) s.gpr pcAllSaved := by
    rw [spW]
    refine (pc_push_saved s (by omega_using [stackFit])).frame (lo := 0) (hi := 56) (by decide) hw.frame ?_
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    rw [BitVec.add_zero]
    have e : State.addr (s.sp - 56) = B + BitVec.ofNat 64 112 := L.a1
    rw [e]
    exact L.preD.sub_left (L.stackSub 112 (by decide))
  have argW (i : Nat) (hi : 4 * i + 4 ≤ 24) :
      w.mem.readW (off (State.addr w.sp) (56 + 4 * i)) 32 = stackArg s i := by
    rw [argAddr (4 * i) hi]
    obtain keep1 : w.mem.readW (off (State.addr s.sp) (4 * i)) 32 = (pcPushed s).mem.readW (off (State.addr s.sp) (4 * i)) 32 :=
      hw.frame.readW (r := ⟨off (State.addr s.sp) (4 * i), 4⟩) (Region.contains_self _ _)
        (fun r hr => by
          simp only [List.mem_singleton] at hr; subst r
          have := h.preArgs; rw [L.lenP] at this
          exact (this.symm.sub_left (Offset.sub_base _ hi))) (by decide)
    obtain keep2 : (pcPushed s).mem.readW (off (State.addr s.sp) (4 * i)) 32 = s.mem.readW (off (State.addr s.sp) (4 * i)) 32 :=
      (L.frame1 h).readW (r := ⟨off (State.addr s.sp) (4 * i), 4⟩) (Region.contains_self _ _)
        (fun r hr => by
          simp only [List.mem_singleton] at hr; subst r
          have := L.Bnat
          simp only [off]; rw [L.spB, BitVec.add_assoc, ← BitVec.ofNat_add]
          exact Offset.disjoint _ (Or.inr (by omega_using [])) (by omega_using [hi]) (by omega_using [])) (by decide)
    rw [keep1, keep2]
    unfold stackArg stackArgAddr
    rw [addr_add (by omega_using [argFit, hi])]
  refine WP.mono (pp_loadArgs_ok w (by rw [spW, FrameStack.sub_toNat' (by omega_using [stackFit])]; omega_using [argFit]) ?_) ?_
  · intro d hd
    rcases hd with low | ⟨high, hd⟩
    · refine ⟨_, List.mem_append_right _ ?_, Offset.contains_base _ low (by omega_using [low])⟩
      rw [restW.wr, spW]; exact List.mem_cons_self
    · have e := argAddr (d - 56) (by omega_using [hd])
      rw [show 56 + (d - 56) = d by omega_using [high]] at e
      rw [e, restW.rd]
      exact ⟨_, List.mem_append_left _ h.argRead, Offset.contains_base _ (by omega_using [hd]) (by omega_using [hd])⟩
  rintro x ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, memX, restX⟩
  dsimp only at x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
  have sv (r : Reg) (d : Nat) (hr : (r, d) ∈ pcAllSaved) :
      w.mem.readW (off (State.addr w.sp) d) 32 = s.gpr r := savedW (r, d) hr
  rw [sv .r0 0 (by decide)] at x0 x10
  rw [sv .r3 12 (by decide)] at x1
  rw [show (56 : Nat) = 56 + 4 * 0 from rfl, argW 0 (by decide)] at x2 x6
  rw [show (60 : Nat) = 56 + 4 * 1 from rfl, argW 1 (by decide)] at x3 x7 x11
  rw [show (64 : Nat) = 56 + 4 * 2 from rfl, argW 2 (by decide)] at x4 x8
  rw [show (68 : Nat) = 56 + 4 * 3 from rfl, argW 3 (by decide)] at x5 x9
  rw [show (72 : Nat) = 56 + 4 * 4 from rfl, argW 4 (by decide)] at x12
  refine ⟨(restW.mono (by decide)).trans (restX.mono (by decide)), by rw [memX]; exact hw.frame, by rw [memX]; exact hw.zero,
    by rw [memX, restX.sp]; exact savedW, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12⟩

/-! ### The CRT's stack arguments pushed, and its register arguments -/

structure PpCalled (s : State) (B : Addr) (P : Nat) (y : State) : Prop where
  input : CrtFnInput (ppGeometry s) (ppBytes s) y
  call : PpCall (ppGeometry s) y
  sp : y.sp = s.sp - BitVec.ofNat 32 56 - BitVec.ofNat 32 56
  wr : y.wr = ⟨State.addr y.sp, 56⟩ :: ⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩ :: s.wr
  frame : Frame [⟨State.addr (s.gpr .r0), 8 * P⟩, ⟨B + BitVec.ofNat 64 56, 56⟩] (pcPushed s).mem y.mem

theorem pp_call_ok (s : State) (h : PpFnInput s) {B : Addr} {P : Nat} (L : PpLayout s B P) (x : State)
    (hx : PpLoaded s P x) : WP isa (.block callArgs) (pcPushed x) (PpCalled s B P) := by
  have stackFit := h.stackFit
  have argFit := h.argFit
  have hPw := L.hPw
  have preFit := L.preFit
  have Bnat := L.Bnat
  have preD := L.preD
  have nD := L.nD
  have pD := L.pD
  have qD := L.qD
  have wsD := L.wsD
  have preW := L.preW
  have lenP := L.lenP
  have stackSub := L.stackSub
  have restX := hx.rest
  obtain spX : x.sp = s.sp - BitVec.ofNat 32 56 := by rw [restX.sp]; rfl
  obtain spXnat : x.sp.toNat = s.sp.toNat - 56 := by rw [spX, FrameStack.sub_toNat' (by omega_using [stackFit])]
  obtain frameY0 : Frame [⟨B + BitVec.ofNat 64 56, 56⟩] x.mem (pcPushed x).mem := by
    have := FrameStack.pushed_frameA
      (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) (s := x) (by show 56 ≤ _; omega_using [stackFit, spXnat])
    unfold FrameStack.belowA at this
    rw [show 4 * List.length [Reg.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr] = 56
      from rfl, spX, L.a2] at this
    exact this
  have outerY0 (d : Nat) (hd : d + 4 ≤ 56) :
      (pcPushed x).mem.readW (off (State.addr (pcPushed x).sp) (56 + d)) 32 = x.mem.readW (off (State.addr x.sp) d) 32 := by
    rw [public_push_argOffset (by omega_using [stackFit, spXnat]) d]
    refine frameY0.readW (r := ⟨off (State.addr x.sp) d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    simp only [off]; rw [spX, L.a1, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.disjoint _ (Or.inr (by omega_using [])) (by omega_using [hd]) (by omega_using [])
  have outerW (r : Reg) (d : Nat) (hr : (r, d) ∈ pcAllSaved) :
      x.mem.readW (off (State.addr x.sp) d) 32 = s.gpr r := hx.saved (r, d) hr
  unfold callArgs
  have rd0 (d : Nat) (hd : 56 + d + 4 ≤ 112) : InRegions ((pcPushed x).rd ++ (pcPushed x).wr)
      (off (State.addr (pcPushed x).sp) (56 + d)) 4 := by
    rw [public_push_argOffset (by omega_using [stackFit, spXnat]) d]
    refine ⟨⟨State.addr x.sp, 56⟩, List.mem_append_right _ (List.mem_cons_of_mem _ ?_),
      Offset.contains_base _ (by omega_using [hd]) (by omega_using [hd])⟩
    rw [restX.wr, spX]; exact List.mem_cons_self
  obtain sp0 : (pcPushed x).sp.toNat + 112 ≤ 2 ^ 32 := by
    change (x.sp - BitVec.ofNat 32 56).toNat + 112 ≤ _; rw [FrameStack.sub_toNat' (by omega_using [stackFit, spXnat])]; omega_using [spXnat]
  refine wp_loadStack (a := off (State.addr (pcPushed x).sp) (56 + 0)) (by decide) (addr_add (by omega_using [sp0])) (rd0 0 (by decide))
    fun y1 c1 => ?_
  refine wp_loadStack (a := off (State.addr (pcPushed x).sp) (56 + 8)) (by decide)
    (by rw [c1.sp]; exact addr_add (by omega_using [sp0])) (by rw [c1.rd, c1.wr]; exact rd0 8 (by decide)) fun y2 c2 => ?_
  refine wp_loadStack (a := off (State.addr (pcPushed x).sp) (56 + 12)) (by decide)
    (by rw [c2.sp, c1.sp]; exact addr_add (by omega_using [sp0])) (by rw [c2.rd, c2.wr, c1.rd, c1.wr]; exact rd0 12 (by decide))
    fun y c3 => WP.block_nil ?_
  obtain memY : y.mem = (pcPushed x).mem := by rw [c3.mem, c2.mem, c1.mem]
  obtain spY : y.sp = (pcPushed x).sp := by rw [c3.sp, c2.sp, c1.sp]
  obtain y0 : y.gpr .r0 = s.gpr .r0 := by
    rw [c3.other .r0 (by decide), c2.other .r0 (by decide), c1.gpr, outerY0 0 (by decide)]
    exact outerW .r0 0 (by decide)
  obtain y2 : y.gpr .r2 = s.gpr .r2 := by
    rw [c3.other .r2 (by decide), c2.gpr, c1.mem, outerY0 8 (by decide)]
    exact outerW .r2 8 (by decide)
  obtain y3 : y.gpr .r3 = s.gpr .r3 := by
    rw [c3.gpr, c2.mem, c1.mem, outerY0 12 (by decide)]
    exact outerW .r3 12 (by decide)
  obtain spY' : y.sp = s.sp - BitVec.ofNat 32 56 - BitVec.ofNat 32 56 := by rw [spY, ← spX]; rfl
  obtain addrY : State.addr y.sp = B + BitVec.ofNat 64 56 := by rw [spY', L.a2]
  obtain belowY : FrameStack.belowA y.sp 56 = ⟨B, 56⟩ := by
    unfold FrameStack.belowA; rw [spY', L.a3]
  obtain ySpNat : y.sp.toNat = s.sp.toNat - 112 := by
    rw [spY', FrameStack.sub_toNat' (by rw [FrameStack.sub_toNat' (by omega_using [stackFit])]; omega_using [stackFit]),
      FrameStack.sub_toNat' (by omega_using [stackFit])]; omega_using []
  obtain wrY : y.wr = ⟨State.addr y.sp, 56⟩ :: ⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩ :: s.wr := by
    rw [c3.wr, c2.wr, c1.wr, spY]; change ⟨_, 56⟩ :: x.wr = _; rw [restX.wr]; rfl
  obtain rdY : y.rd = s.rd := by rw [c3.rd, c2.rd, c1.rd]; change x.rd = _; rw [restX.rd]; rfl
  have slotY (r : Reg) (d : Nat) (hr : (r, d) ∈ pcAllSaved) :
      y.mem.readW (off (State.addr y.sp) d) 32 = x.gpr r := by
    rw [memY, spY]; exact pc_push_saved x (by omega_using [stackFit, spXnat]) (r, d) hr
  obtain frameSY : Frame [⟨B + BitVec.ofNat 64 112, 56⟩, ⟨State.addr (s.gpr .r0), 8 * P⟩,
      ⟨B + BitVec.ofNat 64 56, 56⟩] s.mem y.mem := by
    obtain f2 : Frame [⟨B + BitVec.ofNat 64 112, 56⟩, ⟨State.addr (s.gpr .r0), 8 * P⟩,
      ⟨B + BitVec.ofNat 64 56, 56⟩] (pcPushed s).mem x.mem := hx.frame.mono (by simp)
    rw [memY]
    exact ((L.frame1 h).mono (by simp)).trans (f2.trans (frameY0.mono (by simp)))
  obtain nLe : (s.gpr .r3).toNat ≤ 8 * P := by
    rw [← hPw]; simp only [ppPreWords, ppGeometry, CrtGeometry.words, Spec.Rsa.modulusWords]; omega_using []
  obtain pLe : (stackArg s 1).toNat ≤ 8 * P := by have := h.pShort; omega_using [nLe, this]
  have preCont (k : Nat) (hk : k ≤ 8 * P) : (⟨State.addr (s.gpr .r0), 8 * P⟩ : Region).Contains (State.addr (s.gpr .r0)) k := by
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using [hk]
  have zeroBytesY (k : Nat) (hk : k ≤ 8 * P) :
      Spec.Rsa.bytesAt y.mem (State.addr (s.gpr .r0)) k = List.replicate k 0 := by
    rw [memY, Proof.Rsa.rsa_bytes_frame frameY0 (by omega_using [preFit, hk])
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst r
        exact ((preD.sub_left (stackSub 56 (by decide))).sub_right (Region.sub_prefix hk)).symm)]
    exact bytesAt_zero_of_read hx.zero hk
  have keptBytes {a : BitVec 32} {k : Nat} (fit : k < 2 ^ 64)
      (stack : Region.Disjoint ⟨B, 168⟩ ⟨State.addr a, k⟩)
      (pre : Region.Disjoint ⟨State.addr (s.gpr .r0), 8 * P⟩ ⟨State.addr a, k⟩) :
      Spec.Rsa.bytesAt y.mem (State.addr a) k = Spec.Rsa.bytesAt s.mem (State.addr a) k := by
    refine Proof.Rsa.rsa_bytes_frame frameSY fit fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (stack.sub_left (stackSub 112 (by decide))).symm
    · exact pre.symm
    · exact (stack.sub_left (stackSub 56 (by decide))).symm
  obtain preN : Region.Disjoint ⟨State.addr (s.gpr .r0), 8 * P⟩ ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩ := by
    have := h.preN; rw [lenP] at this; exact this
  obtain preP' : Region.Disjoint ⟨State.addr (s.gpr .r0), 8 * P⟩ ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩ := by
    have := h.preP; rw [lenP] at this; exact this
  obtain preQ' : Region.Disjoint ⟨State.addr (s.gpr .r0), 8 * P⟩ ⟨State.addr (stackArg s 2), (stackArg s 3).toNat⟩ := by
    have := h.preQ; rw [lenP] at this; exact this
  obtain preWs' : Region.Disjoint ⟨State.addr (s.gpr .r0), 8 * P⟩ ⟨State.addr (stackArg s 4), (stackArg s 5).toNat * 8⟩ := by
    have := h.preWs; rw [lenP] at this; exact this
  obtain preMem : (⟨State.addr (s.gpr .r0), 8 * P⟩ : Region) ∈ y.wr := by
    rw [wrY]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ preW)
  obtain hIn : CrtFnInput (ppGeometry s) (ppBytes s) y := by
    refine {
      workspace := ⟨h.wsFit, by rw [wrY]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h.wsW)⟩
      lengthValid := h.valid
      storageFits := by
        have := crt_layout_fits h.valid; have := h.space
        change Impl.Bignum.Arm.Crt.totalBytes (Spec.Rsa.modulusWords (s.gpr .r3).toNat) ≤ (stackArg s 5).toNat * 8
        omega_arith
      pPositive := by have := h.pPositive; change 0 < (stackArg s 1).toNat; omega_using [this]
      pShort := h.pShort
      qPositive := by have := h.qPositive; change 0 < (stackArg s 3).toNat; omega_using [this]
      qShort := h.qShort
      source := ?_
      sourceSeparate := ?_
      outputFits := by change (s.gpr .r0).toNat + (s.gpr .r3).toNat ≤ _; omega_using [preFit, nLe]
      write := ⟨_, preMem, preCont _ nLe⟩
      outputSeparate := (preWs'.symm.sub_right (Region.sub_prefix nLe))
      output := y0
      modulus := y2
      count := by rw [y3]; change s.gpr .r3 = BitVec.ofNat 32 (s.gpr .r3).toNat; simp
      stackFit := by omega_using [stackFit, ySpNat]
      argFit := by omega_using [ySpNat]
      argRead := ⟨⟨State.addr y.sp, 56⟩, List.mem_append_right _ (by rw [wrY]; exact List.mem_cons_self),
        Region.contains_self _ _⟩
      pointer := ?_
      length := ?_
      r2 := fun _ ha => by cases ha
      workspaceArg := by rw [slotY .r12 48 (by decide), hx.r12]; rfl
      stackWorkspace := by rw [belowY]; exact wsD.sub_left (Region.sub_prefix (by decide))
      argsWorkspace := by rw [addrY]; exact wsD.sub_left (stackSub 56 (by decide))
      stackSource := ?_
      stackOutput := by rw [belowY]; exact (preD.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix nLe)
      stackArgs := by
        rw [belowY, addrY]
        exact (Offset.disjoint_base B (Nat.le_refl 56) (by omega_using [])).symm
      reserve := by
        obtain sub : Region.Sub (FrameStack.belowA y.sp 104) (FrameStack.belowA s.sp 216) := by
          rw [spY', BitVec.sub_sub, ← BitVec.ofNat_add]
          exact FrameStack.belowA_inner (by decide) h.stackFit216
        obtain pre216 : (FrameStack.belowA s.sp 216).Disjoint ⟨State.addr (s.gpr .r0), 8 * P⟩ := by
          have := h.st216Pre; rw [lenP] at this; exact this
        refine ⟨by omega_using [h.stackFit216, ySpNat], h.st216Ws.sub_left sub, ?_,
          (pre216.sub_left sub).sub_right (Region.sub_prefix nLe),
          belowA_disjoint_from (by omega_using [h.stackFit216, ySpNat]) (by decide), fun _ ha => by cases ha⟩
        intro i
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 from by omega_using []) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact h.st216N.sub_left sub
        · exact (pre216.sub_left sub).sub_right (Region.sub_prefix nLe)
        · exact h.st216P.sub_left sub
        · exact h.st216Q.sub_left sub
        · exact h.st216P.sub_left sub
        · exact h.st216Q.sub_left sub
        · exact (pre216.sub_left sub).sub_right (Region.sub_prefix pLe) }
    · intro i
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 from by omega_using []) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · refine ⟨h.nFit, ⟨_, List.mem_append_left _ (by rw [rdY]; exact h.nR), Region.contains_self _ _⟩, ?_⟩
        exact (keptBytes (a := s.gpr .r2) (by omega_using []) nD preN).trans (ppBytes_other s 0 (by decide) (by decide)).symm
      · refine ⟨by change (s.gpr .r0).toNat + (s.gpr .r3).toNat ≤ _; omega_using [preFit, nLe],
          ⟨_, List.mem_append_right _ preMem, preCont _ nLe⟩, ?_⟩
        exact (zeroBytesY _ nLe).trans (ppBytes_zero s 1 (Or.inl rfl)).symm
      · refine ⟨h.pFit, ⟨_, List.mem_append_left _ (by rw [rdY]; exact h.pR), Region.contains_self _ _⟩, ?_⟩
        exact (keptBytes (a := stackArg s 0) (by omega_using []) pD preP').trans (ppBytes_other s 2 (by decide) (by decide)).symm
      · refine ⟨h.qFit, ⟨_, List.mem_append_left _ (by rw [rdY]; exact h.qR), Region.contains_self _ _⟩, ?_⟩
        exact (keptBytes (a := stackArg s 2) (by omega_using []) qD preQ').trans (ppBytes_other s 3 (by decide) (by decide)).symm
      · refine ⟨h.pFit, ⟨_, List.mem_append_left _ (by rw [rdY]; exact h.pR), Region.contains_self _ _⟩, ?_⟩
        exact (keptBytes (a := stackArg s 0) (by omega_using []) pD preP').trans (ppBytes_other s 4 (by decide) (by decide)).symm
      · refine ⟨h.qFit, ⟨_, List.mem_append_left _ (by rw [rdY]; exact h.qR), Region.contains_self _ _⟩, ?_⟩
        exact (keptBytes (a := stackArg s 2) (by omega_using []) qD preQ').trans (ppBytes_other s 5 (by decide) (by decide)).symm
      · refine ⟨by change (s.gpr .r0).toNat + (stackArg s 1).toNat ≤ _; omega_using [preFit, pLe],
          ⟨_, List.mem_append_right _ preMem, preCont _ pLe⟩, ?_⟩
        exact (zeroBytesY _ pLe).trans (ppBytes_zero s 6 (Or.inr rfl)).symm
    · intro i
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 from by omega_using []) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact h.nWs
      · exact preWs'.sub_left (Region.sub_prefix nLe)
      · exact h.pWs
      · exact h.qWs
      · exact h.pWs
      · exact h.qWs
      · exact preWs'.sub_left (Region.sub_prefix pLe)
    · intro i
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 from by omega_using []) with
        rfl | rfl | rfl | rfl | rfl | rfl
      · change y.mem.readW (off (State.addr y.sp) 0) 32 = _
        rw [slotY .r0 0 (by decide), hx.r0]; rfl
      · change y.mem.readW (off (State.addr y.sp) 8) 32 = _
        rw [slotY .r2 8 (by decide), hx.r2]; rfl
      · change y.mem.readW (off (State.addr y.sp) 16) 32 = _
        rw [slotY .r4 16 (by decide), hx.r4]; rfl
      · change y.mem.readW (off (State.addr y.sp) 24) 32 = _
        rw [slotY .r6 24 (by decide), hx.r6]; rfl
      · change y.mem.readW (off (State.addr y.sp) 32) 32 = _
        rw [slotY .r8 32 (by decide), hx.r8]; rfl
      · change y.mem.readW (off (State.addr y.sp) 40) 32 = _
        rw [slotY .r10 40 (by decide), hx.r10]; rfl
    · intro i
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 from by omega_using []) with
        rfl | rfl | rfl | rfl | rfl | rfl
      · change y.mem.readW (off (State.addr y.sp) 4) 32 = _
        rw [slotY .r1 4 (by decide), hx.r1]; simp [ppGeometry, CrtGeometry.sourceLength]
      · change y.mem.readW (off (State.addr y.sp) 12) 32 = _
        rw [slotY .r3 12 (by decide), hx.r3]; simp [ppGeometry, CrtGeometry.sourceLength]
      · change y.mem.readW (off (State.addr y.sp) 20) 32 = _
        rw [slotY .r5 20 (by decide), hx.r5]
        change _ = BitVec.ofNat 32 (stackArg s 3).toNat; simp
      · change y.mem.readW (off (State.addr y.sp) 28) 32 = _
        rw [slotY .r7 28 (by decide), hx.r7]; simp [ppGeometry, CrtGeometry.sourceLength]
      · change y.mem.readW (off (State.addr y.sp) 36) 32 = _
        rw [slotY .r9 36 (by decide), hx.r9]
        change _ = BitVec.ofNat 32 (stackArg s 3).toNat; simp
      · change y.mem.readW (off (State.addr y.sp) 44) 32 = _
        rw [slotY .r11 44 (by decide), hx.r11]; simp [ppGeometry, CrtGeometry.sourceLength]
    · intro i
      rw [belowY]
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 from by omega_using []) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact nD.sub_left (Region.sub_prefix (by decide))
      · exact (preD.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix nLe)
      · exact pD.sub_left (Region.sub_prefix (by decide))
      · exact qD.sub_left (Region.sub_prefix (by decide))
      · exact pD.sub_left (Region.sub_prefix (by decide))
      · exact qD.sub_left (Region.sub_prefix (by decide))
      · exact (preD.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix pLe)
  obtain hCall : PpCall (ppGeometry s) y := by
    refine ⟨by rw [hPw]; exact preFit, by rw [hPw]; exact ⟨_, preMem, Region.contains_self _ _⟩,
      by rw [hPw]; exact preWs'.symm, by rw [hPw, belowY]; exact preD.sub_left (Region.sub_prefix (by decide)),
      by rw [hPw, addrY]; exact preD.sub_left (stackSub 56 (by decide)), ?_, rfl, rfl, ?_, rfl⟩
    · intro i h1 h6
      rw [hPw]
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 from by omega_using []) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact preN.symm
      · exact absurd rfl h1
      · exact preP'.symm
      · exact preQ'.symm
      · exact preP'.symm
      · exact preQ'.symm
      · exact absurd rfl h6
    · rw [hPw, memY, Proof.Rsa.wordsAt_frame frameY0 (by omega_using [preFit])
        (fun r hr => by simp only [List.mem_singleton] at hr; subst r; exact (preD.sub_left (stackSub 56 (by decide))).symm)]
      exact VG.Proof.Bignum.wordsAt_zero_read hx.zero
  refine ⟨hIn, hCall, spY', wrY, ?_⟩
  rw [memY]
  exact (hx.frame.mono (by simp)).trans (frameY0.mono (by simp))

/-- The callable precomputation: the caller's registers kept, and the CRT's result. -/
theorem ppFn_ok (s : State) (h : PpFnInput s) :
    WP isa code s fun t => abiPreserved s t ∧
      t.gpr .r0 = (if ppGood (ppGeometry s) (ppBytes s) then 1 else 0) ∧
      Spec.Rsa.wordsAt t.mem (State.addr (s.gpr .r0)) (ppPreWords (ppGeometry s)) =
        (if ppGood (ppGeometry s) (ppBytes s) then ppValues (ppGeometry s) (ppBytes s)
         else List.replicate (ppPreWords (ppGeometry s)) 0) := by
  obtain L := pp_layout s h
  generalize hP : ppPreWords (ppGeometry s) = P at L ⊢
  generalize hB : State.addr s.sp - BitVec.ofNat 64 168 = B at L
  have stackFit := h.stackFit
  have argFit := h.argFit
  have Bnat := L.Bnat
  have preD := L.preD
  have wsD := L.wsD
  have stackSub := L.stackSub
  unfold code
  refine WP.frame (by decide) (by show 56 ≤ _; omega_using [stackFit]) (by decide) ?_
  rw [WP.seq_iff]
  refine WP.mono (pp_zeroArgs_ok s L) fun v hv => ?_
  rw [WP.seq_iff]
  refine WP.mono (pp_zero_ok s h L v hv) fun w hw => ?_
  rw [WP.seq_iff]
  refine WP.mono (pp_load_ok s h L w hw) fun x hx => ?_
  obtain spX : x.sp = s.sp - BitVec.ofNat 32 56 := by rw [hx.rest.sp]; rfl
  rw [WP.seq_iff]
  unfold argsFrame
  refine WP.frame (by decide) (by show 56 ≤ _; rw [spX, FrameStack.sub_toNat' (by omega_using [stackFit])]; omega_using [stackFit]) (by decide) ?_
  change WP isa _ (pcPushed x) _
  rw [WP.seq_iff]
  refine WP.mono (pp_call_ok s h L x hx) fun y hy => ?_
  obtain belowY : FrameStack.belowA y.sp 56 = ⟨B, 56⟩ := by
    unfold FrameStack.belowA; rw [hy.sp, L.a3]
  refine WP.mono (pp_crtFrame_ok y hy.input hy.call) ?_
  rintro z ⟨r0z, wordsz, spz, wrz, _, frameZ⟩ m₁ u₁ h₁
  rw [L.hPw] at wordsz frameZ
  change Frame [⟨State.addr (x.sp - BitVec.ofNat 32 56), 56⟩] z.mem m₁ at h₁
  rw [spX, L.a2] at h₁
  -- The CRT's arguments popped, and the caller's registers restored.
  obtain zsp : ({ popped .r12 56 z with mem := m₁, unknowns := u₁ } : State).sp = s.sp - BitVec.ofNat 32 56 := by
    show (popped .r12 56 z).sp = _
    rw [popped_sp, spz, hy.sp]; exact BitVec.sub_add_cancel _ _
  obtain saved : Spill.Saved ({ popped .r12 56 z with mem := m₁, unknowns := u₁ } : State).mem (State.addr ({ popped .r12 56 z with mem := m₁, unknowns := u₁ } : State).sp) s.gpr pcCalleeSaved := by
    rw [zsp]
    show Spill.Saved m₁ _ _ _
    obtain base := pc_push_callee_saved s (by omega_using [stackFit])
    obtain outer : (⟨State.addr (s.sp - 56) + BitVec.ofNat 64 0, 56 - 0⟩ : Region) = ⟨B + BitVec.ofNat 64 112, 56⟩ := by
      rw [BitVec.add_zero]; exact congrArg (Region.mk · 56) L.a1
    obtain f1 : Frame [⟨State.addr (s.gpr .r0), 8 * P⟩, ⟨B + BitVec.ofNat 64 56, 56⟩, ⟨B, 56⟩,
        ⟨State.addr (stackArg s 4), (stackArg s 5).toNat * 8⟩] (pcPushed s).mem m₁ := by
      obtain g1 : Frame [⟨State.addr (s.gpr .r0), 8 * P⟩, ⟨B + BitVec.ofNat 64 56, 56⟩, ⟨B, 56⟩,
          ⟨State.addr (stackArg s 4), (stackArg s 5).toNat * 8⟩] (pcPushed s).mem y.mem := hy.frame.mono (by simp)
      obtain g3 : Frame [⟨State.addr (s.gpr .r0), 8 * P⟩, ⟨B + BitVec.ofNat 64 56, 56⟩, ⟨B, 56⟩,
          ⟨State.addr (stackArg s 4), (stackArg s 5).toNat * 8⟩] y.mem z.mem := by
        rw [belowY] at frameZ
        refine frameZ.mono ?_
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl
        · simp
        · simp [ppGeometry]
        · simp [ppGeometry]
      exact (g1.trans g3).trans (h₁.mono fun r hr => by
        simp only [List.mem_singleton] at hr; subst r; exact List.mem_cons_of_mem _ List.mem_cons_self)
    refine base.frame (lo := 0) (hi := 56) (by decide) f1 ?_
    rw [outer]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact preD.sub_left (stackSub 112 (by decide))
    · exact Offset.disjoint _ (Or.inr (by omega_using [])) (by omega_using []) (by omega_using [])
    · exact Offset.disjoint_base _ (by omega_using []) (by omega_using [])
    · exact wsD.sub_left (stackSub 112 (by decide))
  obtain fitR : ({ popped .r12 56 z with mem := m₁, unknowns := u₁ } : State).sp.toNat + 56 ≤ 2 ^ 32 := by
    rw [zsp, FrameStack.sub_toNat' (by omega_using [stackFit])]; omega_using []
  obtain readR : InRegions (({ popped .r12 56 z with mem := m₁, unknowns := u₁ } : State).rd ++ ({ popped .r12 56 z with mem := m₁, unknowns := u₁ } : State).wr) (State.addr ({ popped .r12 56 z with mem := m₁, unknowns := u₁ } : State).sp) 56 := by
    refine ⟨⟨State.addr ({ popped .r12 56 z with mem := m₁, unknowns := u₁ } : State).sp, 56⟩, List.mem_append_right _ ?_, Region.contains_self _ _⟩
    rw [zsp]; show _ ∈ (popped .r12 56 z).wr
    rw [popped_wr, wrz, hy.wr]; exact List.mem_cons_self
  refine WP.mono (pc_restore_ok ({ popped .r12 56 z with mem := m₁, unknowns := u₁ } : State) s.gpr fitR readR saved) ?_
  rintro t ⟨restored, memT, restT⟩ m₂ u₂ h₂
  change Frame [⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩] t.mem m₂ at h₂
  rw [L.a1] at h₂
  obtain ret : t.gpr .r0 = z.gpr .r0 := by
    rw [restT.gpr .r0 (by decide)]; exact popped_gpr (r := .r12) (q := .r0) (by decide) 56 z
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro r hr
    obtain ne : r ≠ .r12 := by intro he; subst r; simp [preserved] at hr
    rw [popped_gpr ne]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact restored (.r4, 16) (by decide)
    · exact restored (.r5, 20) (by decide)
    · exact restored (.r6, 24) (by decide)
    · exact restored (.r7, 28) (by decide)
    · exact restored (.r8, 32) (by decide)
    · exact restored (.r9, 36) (by decide)
    · exact restored (.r10, 40) (by decide)
    · exact restored (.r11, 44) (by decide)
    · exact restored (.lr, 52) (by decide)
  · rw [popped_sp, restT.sp, zsp]; exact BitVec.sub_add_cancel _ _
  · rw [popped_gpr (by decide : Reg.r0 ≠ .r12), ret, r0z]
  · dsimp only
    rw [Proof.Rsa.wordsAt_frame h₂ (by omega_using [L.preFit])
        (fun r hr => by simp only [List.mem_singleton] at hr; subst r; exact (preD.sub_left (stackSub 112 (by decide))).symm),
      memT]
    show Spec.Rsa.wordsAt m₁ _ _ = _
    rw [Proof.Rsa.wordsAt_frame h₁ (by omega_using [L.preFit])
        (fun r hr => by simp only [List.mem_singleton] at hr; subst r; exact (preD.sub_left (stackSub 56 (by decide))).symm)]
    exact wordsz

/-! ## Against the specification -/

theorem os2ip_replicate_zero : ∀ k, Spec.Rsa.os2ip (List.replicate k 0) = 0
  | 0 => rfl
  | k + 1 => by
    rw [List.replicate_succ', Spec.Rsa.os2ip, List.foldl_append, ← Spec.Rsa.os2ip, os2ip_replicate_zero k]
    rfl

theorem pp_result (s : State) (h : PpFnInput s) :
    Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
      (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2)) (stackArg s 3).toNat) =
    if ppGood (ppGeometry s) (ppBytes s) then some (ppValues (ppGeometry s) (ppBytes s)) else none := by
  obtain b0 : ppBytes s 0 = Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat :=
    ppBytes_other s 0 (by decide) (by decide)
  obtain b1 : ppBytes s 1 = List.replicate (s.gpr .r3).toNat 0 := ppBytes_zero s 1 (Or.inl rfl)
  obtain b2 : ppBytes s 2 = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat :=
    ppBytes_other s 2 (by decide) (by decide)
  obtain b3 : ppBytes s 3 = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2)) (stackArg s 3).toNat :=
    ppBytes_other s 3 (by decide) (by decide)
  obtain b6 : ppBytes s 6 = List.replicate (stackArg s 1).toNat 0 := ppBytes_zero s 6 (Or.inr rfl)
  obtain ln := bytesAt_length s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat
  obtain lp := bytesAt_length s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat
  obtain lq := bytesAt_length s.mem (State.addr (stackArg s 2)) (stackArg s 3).toNat
  generalize Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat = nb at b0 ln
  generalize Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat = pb at b2 lp
  generalize Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2)) (stackArg s 3).toNat = qb at b3 lq
  simp only [ppGood, crtAccepted, ppValues, b0, b1, b2, b3, b6, os2ip_replicate_zero]
  unfold Spec.Rsa.privatePrecompute
  by_cases hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) (s.gpr .r3).toNat = true
  · obtain ⟨_, gt, _⟩ := valid_facts hv h.valid.1
    by_cases hpq : Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb = Spec.Rsa.os2ip nb
    · have pPos : 0 < Spec.Rsa.os2ip pb := by
        rcases Nat.eq_zero_or_pos (Spec.Rsa.os2ip pb) with h0 | h0
        · rw [h0, Nat.zero_mul] at hpq; omega
        · exact h0
      rw [VG.Proof.Bignum.publicPrecompute_some ln hv]
      obtain ne : Spec.Rsa.os2ip nb ≠ 0 := by omega_arith
      simp [hpq, hv, ne, pPos, Spec.Rsa.primeR2, lp, lq, ppWords, Spec.Rsa.primeWords, ppGeometry,
        CrtGeometry.words, Spec.Rsa.modulusWords]
    · simp [hpq]
  · have none : Spec.Rsa.publicPrecompute nb = none := by simp [Spec.Rsa.publicPrecompute, ln, hv]
    simp only [none, Option.map_none, ite_self]
    split
    · next hg => exact absurd hg.1 hv
    · rfl

theorem pp_contract_correct (s : State) (h : (Spec.Rsa.privatePrecomputeContract abi 216).pre s) :
    ∃ tr t, Exec isa code s tr t ∧ abiPreserved s t ∧ (Spec.Rsa.privatePrecomputeContract abi 216).post s t := by
  obtain hi := pp_contract_pre s h
  obtain ⟨tr, t, run, preserved, r0, words⟩ := ppFn_ok s hi
  refine ⟨tr, t, run, preserved, ?_⟩
  sig_post [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs, reduceClassify, Loc.val]
  obtain e := pp_result s hi
  simp only [State.addr] at e words
  rw [e, pp_preWords hi, BitVec.setWidth_append_eq_right]
  by_cases good : ppGood (ppGeometry s) (ppBytes s)
  · simp only [good, ite_true] at r0 words ⊢
    exact ⟨r0, words⟩
  · simp only [good, ite_false] at r0 words ⊢
    exact ⟨r0, words⟩

end VG.Proof.Bignum.Arm

end

end

/-! # ARMv7 `vg_rsa_private_precompute` is verified against its contract

Timing depends on the stack pointer, the pointers and lengths of the
arguments, and the modulus' bytes: the factors and whether `p q = n` stay
secret.
-/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.PrivPreFn

theorem pp_loadArgs_ct : RelCT isa (fun s t => s.sp = t.sp) (.block loadArgs) (fun s t => s.sp = t.sp) := by
  have loads : RelCT isa (fun s t => s.sp = t.sp)
      (.block [.ldrSp .r0 0, .ldrSp .r1 12, .ldrSp .r2 56, .ldrSp .r3 60, .ldrSp .r4 64, .ldrSp .r5 68])
      (fun s t => s.sp = t.sp) :=
    stackLoads_ct [(.r0, 0), (.r1, 12), (.r2, 56), (.r3, 60), (.r4, 64), (.r5, 68)]
  have movs : RelCT isa (fun s t => s.sp = t.sp)
      (.block [.mov .r6 (.reg .r2), .mov .r7 (.reg .r3), .mov .r8 (.reg .r4), .mov .r9 (.reg .r5),
        .mov .r10 (.reg .r0), .mov .r11 (.reg .r3)]) (fun s t => s.sp = t.sp) := by
    apply relCT_keep_sp (sp := fun _ _ h => h)
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  exact RelCT.block_append (M := isa)
    (l₁ := ([.ldrSp .r0 0, .ldrSp .r1 12, .ldrSp .r2 56, .ldrSp .r3 60, .ldrSp .r4 64, .ldrSp .r5 68] : List Instr))
    (loads.seq (RelCT.block_append (M := isa)
      (l₁ := ([.mov .r6 (.reg .r2), .mov .r7 (.reg .r3), .mov .r8 (.reg .r4), .mov .r9 (.reg .r5),
        .mov .r10 (.reg .r0), .mov .r11 (.reg .r3)] : List Instr)) (movs.seq (loadStack_ct .r12 72))))

theorem pp_argsFrame_ct (s0 t0 : State) (hs : PpFnInput s0) (ht : PpFnInput t0) {B : Addr} {P : Nat}
    (Ls : PpLayout s0 B P) (Lt : PpLayout t0 B P) (geo : ppGeometry s0 = ppGeometry t0)
    (bytes : ppBytes s0 0 = ppBytes t0 0) :
    RelCT isa (fun a b => PpLoaded s0 P a ∧ PpLoaded t0 P b ∧ a.sp = b.sp) argsFrame (fun _ _ => True) := by
  unfold argsFrame
  apply RelCT.frame (fun _ _ h => h.2.2)
  intro a b tr1 tr2 u v hp e1 e2
  obtain ⟨x, y, ⟨hx, hy, sp⟩, px, py⟩ := hp
  have fitX : 56 ≤ x.sp.toNat := by
    rw [hx.rest.sp]; change 56 ≤ (s0.sp - BitVec.ofNat 32 56).toNat
    rw [FrameStack.sub_toNat' (by have := hs.stackFit; omega_using [this])]; have := hs.stackFit; omega_using [this]
  have fitY : 56 ≤ y.sp.toNat := by
    rw [hy.rest.sp]; change 56 ≤ (t0.sp - BitVec.ofNat 32 56).toNat
    rw [FrameStack.sub_toNat' (by have := ht.stackFit; omega_using [this])]; have := ht.stackFit; omega_using [this]
  have ex : pcPushed x = a := Option.some.inj ((push_pushed
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) (by decide) fitX).symm.trans px)
  have ey : pcPushed y = b := Option.some.inj ((push_pushed
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) (by decide) fitY).symm.trans py)
  subst ex; subst ey
  have callCT : RelCT isa (fun a b => a = pcPushed x ∧ b = pcPushed y ∧ a.sp = b.sp) (.block callArgs)
      (fun _ _ => True) :=
    (stackLoads_ct [(.r0, 56), (.r2, 64), (.r3, 68)]).mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  have frameCT : RelCT isa (fun a b => PpCalled s0 B P a ∧ PpCalled t0 B P b ∧ a.sp = b.sp) crtFrame
      (fun _ _ => True) := by
    refine (pp_crtFrame_ct (g := ppGeometry s0) bytes).mono ?_ (fun _ _ _ => trivial)
    intro a b h
    have i2 := h.2.1.input
    have c2 := h.2.1.call
    rw [← geo] at i2 c2
    exact ⟨⟨h.1.input, h.1.call⟩, ⟨i2, c2⟩, h.2.2⟩
  exact crt_seq_ct callCT (fun a h => h ▸ pp_call_ok s0 hs Ls x hx) (fun b h => h ▸ pp_call_ok t0 ht Lt y hy) frameCT
    _ _ _ _ _ _ ⟨rfl, rfl, by simp only [pcPushed, pushed_sp, sp]⟩ e1 e2

theorem ppFn_ct (s0 t0 : State) (hs : PpFnInput s0) (ht : PpFnInput t0) (sp : s0.sp = t0.sp)
    (geo : ppGeometry s0 = ppGeometry t0) (bytes : ppBytes s0 0 = ppBytes t0 0) :
    RelCT isa (fun s t => s = s0 ∧ t = t0) code (fun _ _ => True) := by
  have Ls := pp_layout s0 hs
  have Lt := pp_layout t0 ht
  rw [← sp, ← geo] at Lt
  generalize ppPreWords (ppGeometry s0) = P at Ls Lt
  generalize State.addr s0.sp - BitVec.ofNat 64 168 = B at Ls Lt
  have out : s0.gpr .r0 = t0.gpr .r0 := congrArg CrtGeometry.output geo
  unfold code
  apply RelCT.frame (fun _ _ h => by rw [h.1, h.2]; exact sp)
  intro a b tr1 tr2 u v hp e1 e2
  obtain ⟨x, y, ⟨rfl, rfl⟩, px, py⟩ := hp
  have ex : pcPushed x = a := Option.some.inj ((push_pushed
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) (by decide)
    (by show 56 ≤ _; have := hs.stackFit; omega_using [this])).symm.trans px)
  have ey : pcPushed y = b := Option.some.inj ((push_pushed
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) (by decide)
    (by show 56 ≤ _; have := ht.stackFit; omega_using [this])).symm.trans py)
  subst ex; subst ey
  have zaCT : RelCT isa (fun a b => a = pcPushed x ∧ b = pcPushed y ∧ a.sp = b.sp) (.block zeroArgs)
      (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro _ _ _
    exact Taint.agree_ofRegs (by simp)
  have zCT : RelCT isa (fun a b => PpZeroReady x P a ∧ PpZeroReady y P b ∧ a.sp = b.sp) zero (fun _ _ => True) := by
    intro a b tr1 tr2 u v h e1 e2
    exact ⟨zero_ct a b tr1 tr2 u v trivial trivial ⟨h.1.1.trans (out.trans h.2.1.1.symm), h.1.2.1.trans h.2.1.2.1.symm⟩
      e1 e2, trivial⟩
  have lCT : RelCT isa (fun a b => PpZeroed x P a ∧ PpZeroed y P b ∧ a.sp = b.sp) (.block loadArgs)
      (fun s t => s.sp = t.sp) := pp_loadArgs_ct.mono (fun _ _ h => h.2.2) (fun _ _ h => h)
  have argsCT := relCT_keep_sp (pp_argsFrame_ct x y hs ht Ls Lt geo bytes) (fun _ _ h => h.2.2)
  have restore : RelCT isa (fun s t => s.sp = t.sp) (.block PcFn.restore) (fun s t => s.sp = t.sp) :=
    stackLoads_ct pcCalleeSaved
  have tail := (lCT.wp (F₁ := PpLoaded x P) (F₂ := PpLoaded y P)
      (fun a b h => ⟨pp_load_ok x hs Ls a h.1, pp_load_ok y ht Lt b h.2.1⟩)).seq
    ((argsCT.mono (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ h => h)).seq restore)
  have tail' : RelCT isa (fun a b => PpZeroed x P a ∧ PpZeroed y P b ∧ a.sp = b.sp)
      (.seq (.block loadArgs) (.seq argsFrame (.block PcFn.restore))) (fun _ _ => True) :=
    tail.mono (fun _ _ h => h) (fun _ _ _ => trivial)
  exact crt_seq_ct zaCT (fun a h => h ▸ pp_zeroArgs_ok x Ls) (fun b h => h ▸ pp_zeroArgs_ok y Lt)
    (crt_seq_ct zCT (fun a h => pp_zero_ok x hs Ls a h) (fun b h => pp_zero_ok y ht Lt b h) tail')
    _ _ _ _ _ _ ⟨rfl, rfl, by simp only [pcPushed, pushed_sp, sp]⟩ e1 e2

theorem pp_contract_ct : ConstantTime isa (Spec.Rsa.privatePrecomputeContract abi 216).pre
    (Spec.Rsa.privatePrecomputeContract abi 216).pub code := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  have is := pp_contract_pre s hs
  have it := pp_contract_pre t ht
  sig_pub [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs, reduceClassify, Loc.val,
    State.addr] at hp
  obtain ⟨sp, bytes, p0, p1, p2, p3, a0, a1, a2, a3, a4, a5⟩ := hp
  have byteEq := congrArg (List.map (BitVec.ofNat 8)) bytes
  simp only [List.map_map, Function.comp_def, BitVec.ofNat_toNat, BitVec.setWidth_eq, List.map_id'] at byteEq
  have geo : ppGeometry s = ppGeometry t := by
    simp only [ppGeometry, p0, p2, p3, a0, a1, a2, a3, a4, a5]
  have nb : ppBytes s 0 = ppBytes t 0 := by
    rw [ppBytes_other s 0 (by decide) (by decide), ppBytes_other t 0 (by decide) (by decide)]
    exact byteEq
  exact (ppFn_ct s t is it sp geo nb s t tr1 tr2 u v ⟨rfl, rfl⟩ e1 e2).1

/-- A 64-byte modulus, 32-byte factors, and separate buffers. -/
def ppSatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 24 | .r2 => 0x2000 | .r3 => 64 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x30 else
    if a = 0x8004 then 0x20 else
    if a = 0x8009 then 0x31 else
    if a = 0x800c then 0x20 else
    if a = 0x8011 then 0x40 else
    if a = 0x8014 then 0x20 else
    if a = 0x8015 then 0x4 else
    0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 32⟩, ⟨0x3100, 32⟩, ⟨0x8000, 24⟩]
  wr := [⟨0x1000, 192⟩, ⟨0x4000, 8448⟩]

theorem pp_contract_sat : ∃ s, (Spec.Rsa.privatePrecomputeContract abi 216).pre s := by
  sig_implies_sat [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs, reduceClassify,
    Loc.val, State.addr]
    [ppSatState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid, Spec.Rsa.scratchWords,
      Spec.Rsa.privatePrecomputedWords, Spec.Rsa.precomputedWords, Spec.Rsa.primeWords, Spec.Rsa.modulusWords]
    using ppSatState

theorem privPre_verified : Verified target code (Spec.Rsa.privatePrecomputeContract abi 216) :=
  ⟨pp_contract_correct, pp_contract_ct, pp_contract_sat⟩

/-- `vg_rsa_private_precompute_umaal`. -/
theorem privPre_umaal_verified : Verified target codeU (Spec.Rsa.privatePrecomputeContract abi 216) :=
  umaalArithmetic_verified privPre_verified

end VG.Proof.Bignum.Arm
