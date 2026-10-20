module

import VerifiedGarbage.Proof.Ffdh.Arm.SampleSpec
public import VerifiedGarbage.Spec.Ffdh.VettedKeyGenerationContract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicSpec
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleResult

/-! The selected scalar layout satisfies the separately reviewed vetted policy. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem vettedKeyGenerate_post (s t : State) {p : Inputs} {rb : List Byte}
    (privateValue : s.gpr .r0 = p.privateValue) (publicValue : s.gpr .r2 = p.publicValue)
    (domain : stackArg s 0 = p.domain) (count : (stackArg s 2).toNat = p.k)
    (entropy : stackArg s 3 = p.entropy)
    (domainBytes : Spec.Rsa.bytesAt s.mem (State.addr p.domain) (stackArg s 1).toNat = p.dom)
    (entropyBytes : Spec.Rsa.bytesAt s.mem (State.addr p.entropy) p.k = rb)
    (randLength : (stackArg s 4).toNat = (stackArg s 2).toNat) (size : rb.length = p.k)
    (result : Spec.Rsa.modulusValid p.P p.k = true → sampleResult p (ScalarLayout.vetted p) rb t) :
    (Spec.Ffdh.vettedGenerateKeyContract abi 176).post s t := by
  sig_post [Spec.Ffdh.vettedGenerateKeyContract, Spec.Ffdh.generateKeySig, abi,
    argRegs, reduceClassify, Loc.val, State.addr]
  rw [BitVec.setWidth_append_eq_right]
  simp only [State.addr] at domainBytes entropyBytes
  simp only [randLength, count, domain, entropy, domainBytes, entropyBytes, privateValue, publicValue]
  intro valid
  have modValid := VG.Proof.Ffdh.domainValid_mod valid
  rw [p.domainP] at modValid
  have output := sampleResult_spec size valid (result modValid)
  rwa [ScalarLayout.vetted_value size] at output

end VG.Proof.Ffdh.Arm
