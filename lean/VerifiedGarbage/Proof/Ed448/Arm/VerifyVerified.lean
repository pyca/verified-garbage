module

public import VerifiedGarbage.Proof.Ed448.Arm.VerifyMain
public import VerifiedGarbage.Proof.Ed448.Arm.VerifyLocal
import VerifiedGarbage.Proof.Ed448.Arm.VerifyLit
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Ed448.Arm.VerifyMain
meta import VerifiedGarbage.Proof.Ed448.Arm.VerifyLocal
meta import VerifiedGarbage.Proof.Ed448.Arm.VerifyLit
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
public import VerifiedGarbage.Spec.Ed448.Contract

/-!
# Ed448 verification's equation on ARMv7: `Verified`

Correctness including the ABI, given the reference computations' agreement
with the specification (`RecoverOk`, `VerifyEqOk`, which the registration
file passes in, from `Proof/Ed448/Facts.lean`), constant time (by taint
tracking: the only branches are on the loop counters, and every address is
an argument plus a constant or a counter), and a concrete state satisfying
the signature's contract. The contract lets timing depend on the inputs; the
code's depends on the pointers alone.
-/

@[expose] public section

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm
open VG.Proof.Ed448 (RecoverOk VerifyEqOk)

theorem VerifyPre.of {s : State} (h : verifyEquationLocal.pre s) : VerifyPre s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2⟩

theorem verifyEquation_ok (hR : RecoverOk) (hE : VerifyEqOk) (s : State) (hs : verifyEquationLocal.pre s) :
    ∃ t s', Exec isa verifyEquation s t s' ∧ abiPreserved s s' ∧ verifyEquationLocal.post s s' := by
  obtain ⟨t, s', he, h⟩ := verifyEquation_main hR hE (VerifyPre.of hs)
  exact ⟨t, s', he, ⟨h.1, Exec.sp he⟩, h.2⟩

theorem verifyEquation_ct :
    ConstantTime isa verifyEquationLocal.pre verifyEquationLocal.pub verifyEquation := by
  refine Taint.constantTime_eraseOff_of_eq (Taint.ofRegs [.r0, .r1, .r2, .r3]) (Taint.noBase_ofRegs _) ?_
    (c' := verifyEquationErased) rfl (by native_taint_decide)
  intro s₁ s₂ _ _ ⟨h0, h1, h2, h3, _⟩
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3]

end VG.Proof.Ed448.Arm
