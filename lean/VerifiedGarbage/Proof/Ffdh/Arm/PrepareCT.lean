module

public import VerifiedGarbage.Proof.Ffdh.Arm.Prepare
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Bignum.Arm.PcHead
import VerifiedGarbage.Proof.Bignum.Arm.SetupCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.Arm.Taint

meta import VerifiedGarbage.Proof.Ffdh.Arm.Prepare
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Bignum.Arm.PcHead
meta import VerifiedGarbage.Proof.Bignum.Arm.SetupCT
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeCT
meta import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
meta import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! Modulus setup and precomputation reuse RSA's constant-trace preparation. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem prepareInput_ct {base src : BitVec 32} {len k : Nat} :
    RelCT isa (fun s t => PrepareInput base src len k s ∧ PrepareInput base src len k t ∧ s.sp = t.sp)
      VG.Impl.Bignum.Arm.PublicFn.prepare (fun _ _ => True) := by
  let P := fun (s t : State) => PrepareInput base src len k s ∧ PrepareInput base src len k t ∧ s.sp = t.sp
  have head : RelCT isa P (.block VG.Impl.Bignum.Arm.PcFn.head) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  have wp (s : State) (h : PrepareInput base src len k s) :
      WP isa (.block VG.Impl.Bignum.Arm.PcFn.head) s (fun t => t.gpr .r0 = base) :=
    WP.mono (pcHead_ok s h.maxLength h.count) (fun _ j => (j.2.2.2.gpr .r0 (by simp)).trans h.ptr)
  have headReady := (relCT_keep_sp head (fun _ _ h => h.2.2)).wp (fun s t h => ⟨wp s h.1, wp t h.2.1⟩)
  have setupTrace : RelCT isa (fun s t => s.sp = t.sp ∧ s.gpr .r0 = base ∧ t.gpr .r0 = base)
      VG.Impl.Bignum.Arm.setup (fun s t => s.sp = t.sp) := by
    apply relCT_keep_sp (sp := fun _ _ h => h.1)
    intro s t tr1 tr2 u v h e1 e2
    exact ⟨setup_ct s t tr1 tr2 u v trivial trivial (h.2.1.trans h.2.2.symm) e1 e2, trivial⟩
  have inputs := stackLoads_ct [(.r4, 8), (.r6, 12)]
  unfold VG.Impl.Bignum.Arm.PublicFn.prepare
  exact (headReady.seq (setupTrace.seq inputs)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem prepare_ct {base src : BitVec 32} {len k : Nat} (countFits : 128 * Spec.Rsa.modulusWords k < 2 ^ 32) :
    RelCT isa (fun s t => PrepareInput base src len k s ∧ PrepareInput base src len k t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.prepare (fun _ _ => True) := by
  unfold VG.Impl.Ffdh.Arm.prepare
  exact relCT_chain prepareInput_ct
    (fun s h => WP.mono (prepare_input s h) fun _ j => j.1)
    (fun s h => WP.mono (prepare_input s h) fun _ j => j.1)
    (precompute_ct countFits)

end VG.Proof.Ffdh.Arm
