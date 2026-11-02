module
public import VerifiedGarbage.Impl.Bignum.Arm.CrtNarrowPower
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowShared

import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowResult
import VerifiedGarbage.Proof.Bignum.Arm.TransferPaddedCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.ActivateWorkspaceCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtSelectWorkspace
import VerifiedGarbage.Proof.Bignum.Arm.ActivateWorkspace
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Framework.Arm.TaintErase
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Bignum.Arm.CrtNarrowPower
meta import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowShared
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowResult
meta import VerifiedGarbage.Proof.Bignum.Arm.TransferPaddedCT
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Bignum.Arm.ActivateWorkspaceCT
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtSelectWorkspace
meta import VerifiedGarbage.Proof.Bignum.Arm.ActivateWorkspace
meta import VerifiedGarbage.Proof.Bignum.Arm.Stack
meta import VerifiedGarbage.Proof.Framework.Arm.TaintErase
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Returning the narrow power reveals only the public workspace addresses -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt)
open VG.Proof.X25519.Arm (wp_mov op2_reg)

theorem crt_narrowResult_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} {child : BitVec 32} {slot v : Nat}
    (kind : CrtChild g child slot) (le : v ≤ g.words) :
    RelCT isa (fun s t => (CrtShared g bs1 s ∧ ArithmeticReady (crtN g.base g.words) (workspaceWords g.words) v s) ∧
      (CrtShared g bs2 t ∧ ArithmeticReady (crtN g.base g.words) (workspaceWords g.words) v t) ∧ s.sp = t.sp)
      (narrowResult slot) (fun _ _ => True) := by
  let Ready := fun (bs : Fin 7 → List Byte) (s : State) =>
    CrtShared g bs s ∧ ArithmeticReady (crtN g.base g.words) (workspaceWords g.words) v s
  -- Reselect the factor's workspace.
  have move : RelCT isa (fun s t => Ready bs1 s ∧ Ready bs2 t ∧ s.sp = t.sp) (.block [.mov .r1 (.reg .r0)])
      (fun s t => s.sp = t.sp) := by
    refine relCT_keep_sp ?_ (fun _ _ h => h.2.2)
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  let Based := fun (bs : Fin 7 → List Byte) (s : State) => s.gpr .r0 = g.base
  have prefixWP (s : State) {bs : Fin 7 → List Byte} (h : Ready bs s) :
      WP isa (.block [.mov .r1 (.reg .r0), .ldrSp .r0 8]) s (Based bs) := by
    refine wp_mov (op2_reg _ _) fun u a => ?_
    refine wp_loadStack (a := off (State.addr s.sp) 8) (by decide)
      (by rw [a.sp]; exact addr_add (by have := h.1.stack.nowrap; omega))
      (by rw [a.rd, a.wr]; exact h.1.stack.read (by decide)) fun t b => WP.block_nil ?_
    show t.gpr .r0 = g.base
    rw [b.gpr, a.mem]
    exact h.1.savedMain
  have prefixCT := (RelCT.block_append (M := isa) (l₁ := [.mov .r1 (.reg .r0)]) (l₂ := [.ldrSp .r0 8])
    (move.seq (loadStack_ct .r0 8))).wp (fun s t h => ⟨prefixWP s h.1, prefixWP t h.2.1⟩)
  have link : RelCT isa (fun s t => s.sp = t.sp ∧ Based bs1 s ∧ Based bs2 t) (.block [.ldr .r0 .r0 slot])
      (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (hc := .block []) (by
      rw [← Taint.check_eraseOff _ _ (Taint.noBase_ofRegs [.r0])]
      rfl)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.2.1.trans h.2.2.symm
  have leave : RelCT isa (fun s t => Ready bs1 s ∧ Ready bs2 t ∧ s.sp = t.sp) (.block (leaveNarrow slot))
      (fun _ _ => True) :=
    RelCT.block_append (M := isa) (l₁ := [.mov .r1 (.reg .r0), .ldrSp .r0 8]) (l₂ := [.ldr .r0 .r0 slot])
      (prefixCT.seq link)
  -- The workspaces around the transfer.
  let Left := fun (bs : Fin 7 → List Byte) (s : State) => CrtShared g bs s ∧ s.gpr .r0 = child ∧
    s.gpr .r1 = crtN g.base g.words ∧ CrtLayoutState (crtN g.base g.words) (workspaceWords g.words) v s.mem
  have leaveWP (s : State) {bs : Fin 7 → List Byte} (h : Ready bs s) :
      WP isa (.block (leaveNarrow slot)) s (Left bs) := by
    obtain ⟨_, _, _, _, slotFit, hs, link⟩ := h.1.child kind
    refine WP.mono (crt_leaveNarrow_ok s h.1 slotFit hs link) ?_
    rintro t ⟨narrow, childT, mem, rest⟩
    exact ⟨h.1.of_mem mem rest, childT, narrow.trans h.2.ptr, by rw [mem]; exact ⟨h.2.layout, h.2.width⟩⟩
  let Moving := TransferPaddedCtx child (crtN g.base g.words) (workspaceWords g.words) (workspaceWords g.words) g.words v
  have activateWP (s : State) {bs : Fin 7 → List Byte} (h : Left bs s) :
      WP isa (.block activateWorkspace) s Moving := by
    obtain ⟨member, ws, layout, sepCN, _, _, _⟩ := h.1.child kind
    refine WP.mono (activateWorkspace_ok s (by simpa only [off, BitVec.add_zero] using h.1.stack.write (d := 0) (by decide))) ?_
    rintro t ⟨mem, frame, rest⟩
    rw [h.2.1] at mem
    obtain ⟨shared, selected⟩ := crt_selectedWidth_ready h.1 ws layout member
      ((rest.gpr .r0 (by simp)).trans h.2.1) mem frame rest
    have eqN := h.1.workspace_eq_after_base h.1.buffers.context.narrow h.1.narrow_member frame
    exact ⟨selected, shared.buffers.context.narrow, h.2.2.2.congr eqN, (rest.gpr .r1 (by simp)).trans h.2.2.1,
      sepCN.symm, le⟩
  have activate : RelCT isa (fun s t => Left bs1 s ∧ Left bs2 t ∧ s.sp = t.sp) (.block activateWorkspace)
      (fun _ _ => True) :=
    activateWorkspace_ct.mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  rw [narrowResult]
  exact crt_seq_ct leave (fun s h => leaveWP s h) (fun s h => leaveWP s h)
    (crt_seq_ct activate (fun s h => activateWP s h) (fun s h => activateWP s h)
      (transferPadded_ct (by decide) (by decide)))

end VG.Proof.Bignum.Arm
