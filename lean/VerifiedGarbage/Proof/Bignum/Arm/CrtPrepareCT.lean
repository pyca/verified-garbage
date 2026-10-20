module
public import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
public import VerifiedGarbage.Proof.Bignum.Arm.CrtPrepareState

import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupAllCT
import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandLayoutCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtWorkspaceCallCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtInitialize
import VerifiedGarbage.Proof.Bignum.Arm.PcHead
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtPrepareState
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupAllCT
meta import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandLayoutCT
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtWorkspaceCallCT
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtInitialize
meta import VerifiedGarbage.Proof.Bignum.Arm.PcHead
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # CRT workspace preparation reveals only public geometry -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt

theorem crt_initialize_ct {base np : BitVec 32} {size w k : Nat} {nb1 nb2 : List Byte} :
    RelCT isa (fun s t => CrtPrepareInput base np size w k nb1 s ∧ CrtPrepareInput base np size w k nb2 t)
      (.seq (.block PcFn.head) setupAll) (fun _ _ => True) := by
  let P := fun s t => CrtPrepareInput base np size w k nb1 s ∧ CrtPrepareInput base np size w k nb2 t
  have head : RelCT isa P (.block PcFn.head) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro _ _ _
    exact Taint.agree_ofRegs (by simp)
  have wp (s : State) {nb : List Byte} (h : CrtPrepareInput base np size w k nb s) :
      WP isa (.block PcFn.head) s (CrtSetupInput base (workspaceWords w) w) := by
    refine WP.mono (pcHead_ok s h.lengthValid.2 h.count) ?_
    rintro t ⟨count, zero, _, rest⟩
    rw [h.width] at count
    exact ⟨h.context.congr rest.wr, (rest.gpr .r0 (by simp)).trans h.ptr, count, zero⟩
  have args := head.wp (fun s t h => ⟨wp s h.1, wp t h.2⟩)
  have setup : RelCT isa (fun s t => True ∧ CrtSetupInput base (workspaceWords w) w s ∧
      CrtSetupInput base (workspaceWords w) w t) setupAll (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    exact crt_setupAll_ct h.2.1.context.width h.2.1.context.widthFit h.2.1.context.arraysFit
      s t tr1 tr2 u v ⟨h.2.1, h.2.2⟩ e1 e2
  exact args.seq setup

theorem crt_prepare_ct {base np : BitVec 32} {size w k : Nat} {nb1 nb2 : List Byte} :
    RelCT isa (fun s t => CrtPrepareInput base np size w k nb1 s ∧
      CrtPrepareInput base np size w k nb2 t ∧ s.sp = t.sp) CrtFn.prepare (fun _ _ => True) := by
  let P := fun s t => CrtPrepareInput base np size w k nb1 s ∧
    CrtPrepareInput base np size w k nb2 t ∧ s.sp = t.sp
  have initCT : RelCT isa P (.seq (.block PcFn.head) setupAll) (fun _ _ => True) :=
    crt_initialize_ct.mono (fun _ _ h => ⟨h.1, h.2.1⟩) (fun _ _ _ => trivial)
  have first := (relCT_keep_sp initCT (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨WP.mono (crt_initialize_ok s h.1) (fun _ j => j.1),
      WP.mono (crt_initialize_ok t h.2.1) (fun _ j => j.1)⟩)
  have load : RelCT isa (fun s t => s.sp = t.sp ∧ CrtInitialized base np size w k nb1 s ∧
      CrtInitialized base np size w k nb2 t) (savedOperand 0 8 12) (fun _ _ => True) :=
    (savedOperandLayout_ct (by decide : 0 < 8)).mono
      (fun _ _ h => ⟨⟨h.2.1.ready, h.2.1.source⟩, ⟨h.2.2.ready, h.2.2.source⟩, h.1⟩) (fun _ _ _ => trivial)
  exact (first.seq ((relCT_keep_sp load (fun _ _ h => h.1)).seq crt_saveMain_ct)).assoc

end VG.Proof.Bignum.Arm
