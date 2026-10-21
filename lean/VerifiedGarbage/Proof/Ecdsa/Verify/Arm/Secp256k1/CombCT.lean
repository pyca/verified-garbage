module

public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Secp256k1.Contract
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Secp256k1.CombMain
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.TaintSym
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Impl.Ecdsa.Secp256k1.ArmComb
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.TaintSym
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore

/-! Verification's generator comb is constant time for secret input contents too. -/

@[expose] public section
namespace VG
materialize_code Impl.Ecdsa.Arm.verifySecp256k1Comb
end VG

namespace VG.Proof.Ecdsa.Verify.Arm.Secp256k1
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm

def combVerifyPub (s t : State) : Prop := verifyArm.pub s t ∧ s.syms secp256k1Comb.tsym=t.syms secp256k1Comb.tsym

theorem combVerify_ct : ConstantTime isa combVerifyPre combVerifyPub verifySecp256k1Comb := by
  refine VG.Taint.constantTime (A := taintSym [secp256k1Comb.tsym]) (Taint.ofRegs [.r0,.r1,.r2,.r3]) ?_
    (by native_taint_decide)
  intro s t _ _ ⟨⟨_,h0,h1,h2,h3⟩,sy⟩
  refine ⟨Taint.agree_ofRegs (fun r hr => ?_),fun n hn => ?_⟩
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl
    exacts [h0,h1,h2,h3]
  · obtain rfl := List.mem_singleton.mp hn
    exact sy

end VG.Proof.Ecdsa.Verify.Arm.Secp256k1
