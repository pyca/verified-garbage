module

public import VerifiedGarbage.Proof.EcKey.Arm.Secp256k1.Contract
public import VerifiedGarbage.Proof.EcKey.Arm.Secp256k1.CombMain
import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.CombLit
import VerifiedGarbage.Proof.Framework.Arm.TaintSym
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.CombLit
meta import VerifiedGarbage.Proof.Framework.Arm.TaintSym
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Impl.Ecdsa.Secp256k1.ArmComb

/-! Key generation's comb depends only on public pointers and counters. -/

@[expose] public section
namespace VG.Proof.EcKey.Arm.Secp256k1
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm

def combPkPub (s t : State) : Prop := pkArm.pub s t ∧ s.syms secp256k1Comb.tsym=t.syms secp256k1Comb.tsym

theorem combPk_ct : ConstantTime isa combPkPre combPkPub publicKeySecp256k1Comb := by
  refine VG.Taint.constantTime (A := taintSym [secp256k1Comb.tsym]) (Taint.ofRegs [.r0,.r1,.r2]) ?_
    (by native_taint_decide)
  intro s t _ _ ⟨⟨_,h0,h1,h2⟩,sy⟩
  refine ⟨Taint.agree_ofRegs (fun r hr => ?_),fun n hn => ?_⟩
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    exacts [h0,h1,h2]
  · obtain rfl := List.mem_singleton.mp hn
    exact sy

end VG.Proof.EcKey.Arm.Secp256k1
