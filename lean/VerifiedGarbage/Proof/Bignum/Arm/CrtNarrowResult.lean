module

import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowShared
public import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowReduce
public import VerifiedGarbage.Proof.Bignum.Arm.CrtPoweredState
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedState
import VerifiedGarbage.Proof.Bignum.Arm.TransferPadded
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedWorkspace
import VerifiedGarbage.Proof.Bignum.Arm.CrtSelectWorkspace
import VerifiedGarbage.Proof.Bignum.Arm.ActivateWorkspace
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Bignum.Layout

/-! # Return the narrow power to the factor's full-width workspace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt Operand)
open VG.Proof.X25519.Arm (Rest wp_ldr wp_mov op2_reg)

theorem crt_leaveNarrow_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32} {slot : Nat}
    (h : CrtShared g bs s) (slotFit : slot + 4 ≤ 8 * workspaceWords g.words) (hs : slot < 4096)
    (link : s.mem.readW (off (State.addr g.base) slot) 32 = child) :
    WP isa (.block (leaveNarrow slot)) s fun t =>
      t.gpr .r1 = s.gpr .r0 ∧ t.gpr .r0 = child ∧ t.mem = s.mem ∧ Rest [.r0, .r1] s t := by
  have main := h.buffers.context.main
  unfold leaveNarrow
  refine wp_mov (op2_reg _ _) fun u a => ?_
  refine wp_loadStack (a := off (State.addr s.sp) 8) (by decide)
    (by rw [a.sp]; exact addr_add (by have := h.stack.nowrap; omega))
    (by rw [a.rd, a.wr]; exact h.stack.read (by decide)) fun z b => ?_
  refine wp_ldr (a := off (State.addr g.base) slot) hs
    (by rw [b.gpr, a.mem, h.savedMain]; exact addr_add (by have := main.nowrap; omega))
    (by rw [b.rd, b.wr, a.rd, a.wr]; exact main.read slotFit) fun t c => WP.block_nil ?_
  exact ⟨by rw [c.other .r1 (by decide), b.other .r1 (by decide), a.gpr],
    by rw [c.gpr, b.mem, a.mem, link], c.mem.trans (b.mem.trans a.mem),
    (a.rest (by decide)).trans ((b.rest (by decide)).trans (c.rest (by decide)))⟩

theorem crt_narrowResult_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32}
    {slot v M x value : Nat} (h : CrtShared g bs s)
    (childKind : child = crtP g.base g.words ∨ child = crtQ g.base g.words)
    (ready : ArithmeticReady (crtN g.base g.words) (workspaceWords g.words) v s)
    (result : numAt s.mem (State.addr (crtN g.base g.words)) v 6 = value)
    (le : v ≤ g.words)
    (slotFit : slot + 4 ≤ 8 * workspaceWords g.words) (hs : slot < 4096)
    (link : s.mem.readW (off (State.addr g.base) slot) 32 = child)
    (reduced : CrtReducedState child (workspaceWords g.words) g.words M x s.mem) :
    WP isa (narrowResult slot) s fun t =>
      CrtShared g bs t ∧ LayoutFrameReady child (workspaceWords g.words) g.words t ∧
      CrtPoweredState child (workspaceWords g.words) g.words M value t.mem ∧
      t.mem.readW (off (State.addr t.sp) 48) 32 = s.mem.readW (off (State.addr s.sp) 48) 32 ∧
      Frame [⟨State.addr child, 8 * workspaceWords g.words⟩, ⟨State.addr s.sp, 4⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  have member : (⟨State.addr child, 8 * workspaceWords g.words⟩ : Region) ∈
      crtRegions g.base (workspaceWords g.words) g.words := by
    rcases childKind with rfl | rfl <;> simp [crtRegions]
  have childWs : Workspace s child (8 * workspaceWords g.words) := by
    rcases childKind with rfl | rfl
    · exact h.buffers.context.p
    · exact h.buffers.context.q
  have sepCN : Region.Disjoint ⟨State.addr child, 8 * workspaceWords g.words⟩
      ⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩ := by
    rcases childKind with rfl | rfl
    · exact h.buffers.context.sepPN
    · exact h.buffers.context.sepQN
  have fits : arrAt g.words 8 ≤ 8 * workspaceWords g.words := h.buffers.context.arraysFit
  rw [narrowResult, WP.seq_iff]
  refine WP.mono (crt_leaveNarrow_ok s h slotFit hs link) ?_
  rintro u ⟨narrowU, childU, memU, restU⟩
  have sharedU := h.of_mem memU restU
  rw [WP.seq_iff]
  refine WP.mono (activateWorkspace_ok u (by simpa only [off, BitVec.add_zero] using sharedU.stack.write (d := 0) (by decide))) ?_
  rintro z ⟨memZ, frameZ, restZ⟩
  rw [childU] at memZ
  have childWsU := childWs.congr restU.wr
  have reducedU : CrtReducedState child (workspaceWords g.words) g.words M x u.mem := by rw [memU]; exact reduced
  obtain ⟨sharedZ, selected⟩ := crt_selectedWidth_ready sharedU childWsU reducedU.layout member
    ((restZ.gpr .r0 (by decide)).trans childU) memZ frameZ restZ
  have eqC := sharedU.workspace_eq_after_base childWsU member frameZ
  have eqN := sharedU.workspace_eq_after_base (sharedU.buffers.context.narrow) sharedU.narrow_member frameZ
  have reducedZ := reducedU.congr eqC
  have narrowLayout : CrtLayoutState (crtN g.base g.words) (workspaceWords g.words) v z.mem :=
    (show CrtLayoutState (crtN g.base g.words) (workspaceWords g.words) v u.mem by
      rw [memU]; exact ⟨ready.layout, ready.width⟩).congr eqN
  have fitsN : arrAt v 8 ≤ 8 * workspaceWords g.words := ready.width ▸ ready.layout.2.2.1
  have resultZ : numAt z.mem (State.addr (crtN g.base g.words)) v 6 = value := by
    rw [← result, ← memU]; exact eqN.number fitsN (by decide)
  have narrowR1 : z.gpr .r1 = crtN g.base g.words := by
    rw [restZ.gpr .r1 (by decide), narrowU, ready.ptr]
  have arith : ArithmeticReady child (workspaceWords g.words) g.words z :=
    ⟨selected.workspace, reducedZ.layout.layout, reducedZ.layout.width, selected.ptr, reducedZ.inverse,
      by rw [reducedZ.modulus]; exact reducedZ.positive, selected.stackRead, selected.stackSep, selected.saved⟩
  refine WP.mono (transferPadded_ok z (o := 6) (a := 6)
    ⟨⟨selected, sharedZ.buffers.context.narrow, narrowLayout, narrowR1, sepCN.symm, le⟩, reducedZ.cleared⟩
    (by decide) (by decide)) ?_
  rintro t ⟨selectedT, valueT, keepsT, frameT, restT⟩
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op7 : Operand 7 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  obtain ⟨arithT, modT⟩ := arith.after_array (o := 6) (by decide) keepsT frameT restT selectedT.ptr
  have powered := CrtPoweredState.of_ready arithT (modT.trans reducedZ.modulus) (valueT.trans resultZ)
    ((keeps_array_num keepsT fits op4 (by decide)).trans reducedZ.r2)
    ((keeps_array_num keepsT fits op7 (by decide)).trans reducedZ.one)
  have frameT' : Frame [⟨State.addr child, 8 * workspaceWords g.words⟩, ⟨off (State.addr z.sp) 48, 4⟩] z.mem t.mem :=
    frameT.mono (by simp)
  have sharedT : CrtShared g bs t := by
    rcases childKind with rfl | rfl
    · exact sharedZ.after_p frameT' restT ⟨arithT.layout, arithT.width⟩
    · exact sharedZ.after_q frameT' restT ⟨arithT.layout, arithT.width⟩
  have flag := (sharedZ.acceptance_after_workspace member frameT restT).trans
    ((acceptance_after_base_save frameZ restZ).trans (by rw [restU.sp, memU]))
  rw [restU.sp, memU] at frameZ
  have restUZ : Rest roundClobbers s z := (restU.mono (by decide)).trans (restZ.mono (by decide))
  exact ⟨sharedT, selectedT, powered, flag, (frameZ.mono (by simp)).trans (frameT.mono (by simp)),
    restUZ.trans restT⟩

end VG.Proof.Bignum.Arm
