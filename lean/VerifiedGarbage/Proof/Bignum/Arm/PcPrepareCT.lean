module

public import VerifiedGarbage.Proof.Bignum.Arm.PcPrepare
import VerifiedGarbage.Proof.Bignum.Arm.SetupCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.PcHead
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.Arm.PcPrepare
meta import VerifiedGarbage.Proof.Bignum.Arm.SetupCT
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Bignum.Arm.PcHead
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Workspace preparation has a public trace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem pcPrepare_ct {base dst src : BitVec 32} {len k : Nat} :
    RelCT isa (fun s t => PcValidInput base dst src len k s ∧ PcValidInput base dst src len k t ∧ s.sp = t.sp)
      (.seq (.block PcFn.head) (.seq setup (.block PcFn.inputs)))
      (fun s t => PcPrepared base dst src len k s ∧ PcPrepared base dst src len k t ∧ s.sp = t.sp) := by
  let P := fun (s t : State) => PcValidInput base dst src len k s ∧ PcValidInput base dst src len k t ∧ s.sp = t.sp
  have head : RelCT isa P (.block PcFn.head) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  have wp (s : State) (h : PcValidInput base dst src len k s) :
      WP isa (.block PcFn.head) s (fun t => t.gpr .r0 = base) :=
    WP.mono (pcHead_ok s h.maxLength h.count) (fun _ j => (j.2.2.2.gpr .r0 (by simp)).trans h.ptr)
  have headReady := (relCT_keep_sp head (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨wp s h.1, wp t h.2.1⟩)
  have setupTrace : RelCT isa (fun s t => s.sp = t.sp ∧ s.gpr .r0 = base ∧ t.gpr .r0 = base)
      setup (fun s t => s.sp = t.sp) := by
    apply relCT_keep_sp (sp := fun _ _ h => h.1)
    intro s t tr1 tr2 u v h e1 e2
    exact ⟨setup_ct s t tr1 tr2 u v trivial trivial (h.2.1.trans h.2.2.symm) e1 e2, trivial⟩
  have inputs : RelCT isa (fun s t => s.sp = t.sp) (.block PcFn.inputs) (fun s t => s.sp = t.sp) :=
    stackLoads_ct [(.r4, 8), (.r6, 12)]
  have trace := headReady.seq (setupTrace.seq inputs)
  exact (trace.wp (fun s t h => ⟨pcPrepare_ready s h.1, pcPrepare_ready t h.2.1⟩)).mono
    (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩)

end VG.Proof.Bignum.Arm
