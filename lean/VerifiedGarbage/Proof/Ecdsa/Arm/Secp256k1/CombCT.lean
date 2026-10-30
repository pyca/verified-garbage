module

public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.ArmComb
public import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.Contract
public import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.CombContract
import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.CombLit
import VerifiedGarbage.Proof.Framework.Arm.TaintSym
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.Verified
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.CombLit
meta import VerifiedGarbage.Proof.Framework.Arm.TaintSym
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Impl.Ecdsa.Secp256k1.ArmComb
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData

/-! The generator comb remains constant time inside the complete signing function. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Arm.Secp256k1
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm

def combSignPub (s t : State) : Prop := signArm.pub s t ∧ s.syms secp256k1Comb.tsym=t.syms secp256k1Comb.tsym

theorem combSign_ct : ConstantTime isa combSignPre combSignPub signSecp256k1Comb := by
  refine VG.Taint.constantTime (A := taintSym [secp256k1Comb.tsym]) τ₀ ?_ (by native_taint_decide)
  intro s t hs ht pub
  exact ⟨agree₀ hs.1 ht.1 pub.1,fun n hn => by
    obtain rfl := List.mem_singleton.mp hn
    exact pub.2⟩

end VG.Proof.Ecdsa.Arm.Secp256k1
