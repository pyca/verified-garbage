module

public import VerifiedGarbage.Proof.Ed448.Arm.VerifyMain
meta import VerifiedGarbage.Proof.Ed448.Arm.VerifyMain
public import VerifiedGarbage.Proof.Ed448.Arm.VerifyLocal
meta import VerifiedGarbage.Proof.Ed448.Arm.VerifyLocal
import VerifiedGarbage.Proof.Ed448.Arm.VerifyLit
meta import VerifiedGarbage.Proof.Ed448.Arm.VerifyLit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.TaintSum
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Ed448.Arm.BaseEncode
import VerifiedGarbage.Proof.Ed448.Arm.BaseMain
import VerifiedGarbage.Proof.Ed448.Arm.VerifyDecode
import VerifiedGarbage.Proof.Ed448.Arm.VerifyDecodeY
import VerifiedGarbage.Proof.Ed448.Arm.VerifyFinish
import VerifiedGarbage.Proof.Ed448.Arm.VerifyS
import VerifiedGarbage.Proof.Ed448.Arm.VerifySign
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
import VerifiedGarbage.Proof.Framework.Arm.NativeTaint
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.X25519.Arm.Pass
import VerifiedGarbage.Proof.X448.Arm.Carry
import VerifiedGarbage.Proof.X448.Arm.Copy
import VerifiedGarbage.Proof.X448.Arm.Counters
import VerifiedGarbage.Proof.X448.Arm.Decode
import VerifiedGarbage.Proof.X448.Arm.DecodeAll
import VerifiedGarbage.Proof.X448.Arm.Fill
import VerifiedGarbage.Proof.X448.Arm.Finish
import VerifiedGarbage.Proof.X448.Arm.Initial
import VerifiedGarbage.Proof.X448.Arm.Normalize
import VerifiedGarbage.Proof.X448.Arm.Restore
import VerifiedGarbage.Proof.X448.Arm.Setup
import VerifiedGarbage.Proof.X448.Arm.Step
import VerifiedGarbage.Proof.X448.Bytes
meta import VerifiedGarbage.Proof.Ed448.Arm.BaseEncode
meta import VerifiedGarbage.Proof.Ed448.Arm.BaseMain
meta import VerifiedGarbage.Proof.Ed448.Arm.VerifyDecode
meta import VerifiedGarbage.Proof.Ed448.Arm.VerifyDecodeY
meta import VerifiedGarbage.Proof.Ed448.Arm.VerifyFinish
meta import VerifiedGarbage.Proof.Ed448.Arm.VerifyS
meta import VerifiedGarbage.Proof.Ed448.Arm.VerifySign
meta import VerifiedGarbage.Proof.Ed448.Scalar
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Call
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
meta import VerifiedGarbage.Proof.Framework.Arm.NativeTaint
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.X25519.Arm.Pass
meta import VerifiedGarbage.Proof.X448.Arm.Carry
meta import VerifiedGarbage.Proof.X448.Arm.Copy
meta import VerifiedGarbage.Proof.X448.Arm.Counters
meta import VerifiedGarbage.Proof.X448.Arm.Decode
meta import VerifiedGarbage.Proof.X448.Arm.DecodeAll
meta import VerifiedGarbage.Proof.X448.Arm.Fill
meta import VerifiedGarbage.Proof.X448.Arm.Finish
meta import VerifiedGarbage.Proof.X448.Arm.Initial
meta import VerifiedGarbage.Proof.X448.Arm.Normalize
meta import VerifiedGarbage.Proof.X448.Arm.Restore
meta import VerifiedGarbage.Proof.X448.Arm.Setup
meta import VerifiedGarbage.Proof.X448.Arm.Step
meta import VerifiedGarbage.Proof.X448.Bytes

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
  refine Taint.constantTime_eraseOff_of_eq (Taint.ofRegs [.r0, .r1, .r2, .r3]) (Taint.noBase_ofRegs _) ?_
    (c' := verifyEquationErased) rfl (by native_taint_decide)
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
