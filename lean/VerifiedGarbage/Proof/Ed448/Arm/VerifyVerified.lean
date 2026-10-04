import VerifiedGarbage.Proof.Ed448.Arm.VerifyMain
import VerifiedGarbage.Proof.Ed448.Arm.VerifyLocal
import VerifiedGarbage.Proof.Ed448.Arm.VerifyLit
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Ed448.Contract

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

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm
open VG.Proof.Ed448 (RecoverOk VerifyEqOk)

theorem VerifyPre.of {s : State} (h : verifyEquationLocal.pre s) : VerifyPre s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2⟩

def verifyEquationSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 0x4000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 57⟩, ⟨0x2000, 114⟩, ⟨0x3000, 57⟩]
  wr := [⟨0x4000, 8192⟩]

theorem verifyEquation_ok (hR : RecoverOk) (hE : VerifyEqOk) (s : State) (hs : verifyEquationLocal.pre s) :
    ∃ t s', Exec isa verifyEquation s t s' ∧ abiPreserved s s' ∧ verifyEquationLocal.post s s' := by
  obtain ⟨t, s', he, h⟩ := verifyEquation_main hR hE (VerifyPre.of hs)
  exact ⟨t, s', he, ⟨h.1, Exec.sp he⟩, h.2⟩

theorem verifyEquation_ct :
    ConstantTime isa verifyEquationLocal.pre verifyEquationLocal.pub verifyEquation := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h0, h1, h2, h3, _⟩
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3]

theorem verifyEquation_implies :
    verifyEquationLocal.Implies (Spec.Ed448.verifyEquationContract Arm.abi) where
  pre := by
    sig_implies_pre [Spec.Ed448.verifyEquationContract, Spec.Ed448.verifyEquationSig,
      Spec.Ed448.scratchWords, verifyEquationLocal, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
  post := by
    intro s t _ h
    sig_post [Spec.Ed448.verifyEquationContract, Spec.Ed448.verifyEquationSig,
      Spec.Ed448.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    have e : ∀ x y : BitVec 32, (x ++ y).setWidth 32 = y := fun _ _ => BitVec.setWidth_append_eq_right
    exact (e _ _).trans h
  pub := by
    sig_implies_pub [Spec.Ed448.verifyEquationContract, Spec.Ed448.verifyEquationSig,
      Spec.Ed448.scratchWords, verifyEquationLocal, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
  sat := by
    sig_implies_sat [Spec.Ed448.verifyEquationContract, Spec.Ed448.verifyEquationSig,
      Spec.Ed448.scratchWords, verifyEquationLocal, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [verifyEquationSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using verifyEquationSat

theorem verifyEquation_verified (hR : RecoverOk) (hE : VerifyEqOk) :
    Verified Arm.target verifyEquation (Spec.Ed448.verifyEquationContract Arm.abi) :=
  Verified.of_correct (verifyEquation_ok hR hE) verifyEquation_ct verifyEquation_implies

end VG.Proof.Ed448.Arm
