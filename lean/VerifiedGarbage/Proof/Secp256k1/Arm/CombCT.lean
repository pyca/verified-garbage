module

public import VerifiedGarbage.Impl.Weierstrass.Arm.TCombSecp256k1
import VerifiedGarbage.Proof.Framework.Arm.TaintSym
import VerifiedGarbage.Proof.Secp256k1.Arm.CombLit
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Impl.Weierstrass.Arm.TCombSecp256k1
meta import VerifiedGarbage.Proof.Framework.Arm.TaintSym
meta import VerifiedGarbage.Proof.Secp256k1.Arm.CombLit
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
public import Init.Prelude
meta import Init.Prelude
public import VerifiedGarbage.TCB.Arm.Isa
meta import VerifiedGarbage.TCB.Arm.Isa

/-! The comb's scalar and table contents remain secret throughout the scan. -/

@[expose] public section
namespace VG.Proof.Secp256k1.Arm
open VG VG.Arm VG.Impl.Weierstrass.Arm

def combPub (s t : State) : Prop :=
  s.gpr .r12=t.gpr .r12 ∧ s.syms secp256k1Comb.tsym=t.syms secp256k1Comb.tsym

theorem comb_ct : ConstantTime isa (fun _ => True) combPub mulGeneratorSecp256k1 :=
  VG.Taint.constantTime (A := taintSym [secp256k1Comb.tsym]) (Taint.ofRegs [.r12])
    (fun _ _ _ _ hp => ⟨Taint.agree_ofRegs (fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact hp.1),fun n hn => by
        simp only [List.mem_singleton] at hn
        subst hn
        exact hp.2⟩) (by native_taint_decide)

end VG.Proof.Secp256k1.Arm
