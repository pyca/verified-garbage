module

public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleResult
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Ffdh.Arm.SampleSpec
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
public import Init.Prelude
public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.TCB.Artifact

/-! Cached attempts return the reviewed vetted scalar and public power. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem cachedKeyGenerate_post (s t : State) {p : Inputs} {rb : List Byte}
    (privateValue : s.gpr .r0=p.privateValue) (publicValue : s.gpr .r2=p.publicValue)
    (domain : stackArg s 0=p.domain) (count : (stackArg s 2).toNat=p.k)
    (entropy : stackArg s 3=p.entropy)
    (domainBytes : Spec.Rsa.bytesAt s.mem (State.addr p.domain) (stackArg s 1).toNat=p.dom)
    (entropyBytes : Spec.Rsa.bytesAt s.mem (State.addr p.entropy) p.k=rb)
    (randLength : (stackArg s 4).toNat=(stackArg s 2).toNat) (size : rb.length=p.k)
    (valid : Spec.Ffdh.domainValid p.k p.dom=true)
    (result : sampleResult p (ScalarLayout.vetted p) rb t) :
    (Spec.Ffdh.cachedGenerateKeyContract abi 176).post s t := by
  sig_post [Spec.Ffdh.cachedGenerateKeyContract,Spec.Ffdh.cachedGenerateKeySig,
    Spec.Ffdh.generateKeySig,abi,argRegs,reduceClassify,Loc.val,State.addr]
  rw [BitVec.setWidth_append_eq_right]
  simp only [State.addr] at domainBytes entropyBytes
  simp only [randLength,count,domain,entropy,domainBytes,entropyBytes,privateValue,publicValue]
  have output := sampleResult_spec size valid result
  rwa [ScalarLayout.vetted_value size] at output

end VG.Proof.Ffdh.Arm
