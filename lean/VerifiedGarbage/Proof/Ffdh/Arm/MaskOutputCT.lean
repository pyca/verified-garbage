module

public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Proof.Ffdh.Arm.MaskOutput
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.MaskBytesCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.Ffdh.Arm.Domain
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Ffdh.Arm.Context

/-! Shared-value rejection changes output bytes and status but never the masking trace. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem maskOutputArgs_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block [.ldrSp .r0 4, .ldrSp .lr 32, .ldrSp .r2 64,
      .mov .r3 (.imm 0), .dp .sub .r2 .r3 (.reg .r2)]) (fun _ _ => True) := by
  have tail : RelCT isa (fun _ _ => True)
      (.block [.mov .r3 (.imm 0), .dp .sub .r2 .r3 (.reg .r2)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  exact RelCT.block_append ((stackLoads_ct [(.r0, 4), (.lr, 32), (.r2, 64)]).seq
    (tail.mono (fun _ _ _ => trivial) (fun _ _ h => h)))

theorem maskOutput_ct {p : Inputs} {flag1 flag2 : BitVec 32} :
    RelCT isa (fun s t => MaskOutputInput p flag1 s ∧ MaskOutputInput p flag2 t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.Exchange.maskOutput (fun _ _ => True) := by
  let Q := fun s : State => s.gpr .r0 = p.output ∧ s.gpr .lr = BitVec.ofNat 32 p.k
  have args := maskOutputArgs_ct.mono
    (P' := fun (s t : State) => MaskOutputInput p flag1 s ∧ MaskOutputInput p flag2 t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ h => h)
  have wp (s : State) {flag : BitVec 32} (h : MaskOutputInput p flag s) :
      WP isa (.block [.ldrSp .r0 4, .ldrSp .lr 32, .ldrSp .r2 64,
        .mov .r3 (.imm 0), .dp .sub .r2 .r3 (.reg .r2)]) s Q :=
    WP.mono (maskOutputArgs_ok s h) fun _ j => ⟨j.1.1, j.1.2.1⟩
  have loop : RelCT isa (fun s t => Q s ∧ Q t ∧ s.sp = t.sp) VG.Impl.Bignum.Arm.maskBytes
      (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    exact ⟨maskBytes_ct s t tr1 tr2 u v trivial trivial
      ⟨h.1.1.trans h.2.1.1.symm, h.1.2.trans h.2.1.2.symm⟩ e1 e2, trivial⟩
  have finish := ((relCT_keep_sp loop (fun _ _ h => h.2.2)).seq (loadStack_ct .r0 64)).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)
  unfold VG.Impl.Ffdh.Arm.Domain.Exchange.maskOutput
  exact relCT_chain args (fun s h => wp s h) (fun s h => wp s h) finish

end VG.Proof.Ffdh.Arm
