module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTKeyRegisters
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTPolicy
import VerifiedGarbage.Proof.Bignum.Arm.StackOnlyCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTKeyRegisters
meta import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
meta import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! Native exponent halving uses public array addresses and fixed stack slots. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm

private theorem half27_taint : CandidateCert keyRegs (VG.Impl.Rsa.Arm.Keys.half 27) := ⟨_, by taint_decide⟩

theorem exponentHalf_ct : RelCT isa KeyRegEq VG.Impl.Ffdh.Arm.ParameterCandidate.exponentHalf KeyRegEq :=
  (keyRegs_stack_ct (stackOnly_ct [.mov .r11 (.imm 0)] rfl) (by decide) (by decide)).seq
    ((keyRegs_taint_ct half27_taint (by decide) (by decide)).seq
      ((keyRegs_stack_ct
        (RelCT.block_append ((stackOnly_ct [.ldrSp .r1 64, .subs .r1 .r1 (.imm 1)] rfl).seq (save_ct .r1 64)))
        (by decide) (by decide)).seq (RelCT.block_nil (fun _ _ h => h))))

end VG.Proof.Ffdh.Arm.ParameterCandidate
