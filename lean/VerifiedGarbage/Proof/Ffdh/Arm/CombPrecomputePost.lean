module

import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeInput
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract

/-! The canonical native result has the reviewed public-precomputation postcondition. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem combPrecompute_post (s t : State) {p : Inputs}
    (output : s.gpr .r0=p.output) (domain : s.gpr .r2=p.domain)
    (count : (stackArg s 0).toNat=p.k)
    (domainBytes : Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r3).toNat=p.dom)
    (ctxLen : (s.gpr .r1).toNat=Spec.Ffdh.generationPrecomputedWords p.k)
    (status : t.gpr .r0=1)
    (result : Spec.Ffdh.generationPrecompute p.k p.dom=some
      (Spec.Rsa.wordsAt t.mem (State.addr p.output) (Spec.Ffdh.generationPrecomputedWords p.k))) :
    (Spec.Ffdh.generationPrecomputeContract abi 176).post s t := by
  sig_post [Spec.Ffdh.generationPrecomputeContract,Spec.Ffdh.generationPrecomputeSig,
    abi,argRegs,reduceClassify,Loc.val,State.addr]
  rw [BitVec.setWidth_append_eq_right]
  change t.gpr .r0=1 ∧ Spec.Ffdh.generationPrecompute (stackArg s 0).toNat
    (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)=
      some (Spec.Rsa.wordsAt t.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat)
  rw [status,count,domain,domainBytes,output,ctxLen]
  exact ⟨rfl,result⟩

end VG.Proof.Ffdh.Arm
