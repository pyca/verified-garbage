module

import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputePre
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeEnvironment
import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeInput
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract

/-! Package the reviewed public ABI arguments for the native writer. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Impl.Ffdh.Arm.VettedGroups (tableConsts)

theorem combPrecompute_data (s : State)
    (pre : (Spec.Ffdh.generationPrecomputeContract (abi.withConsts tableConsts) 176).pre s) :
    ∃ p : Inputs, stackArg s 1 = p.base ∧ s.gpr .r0 = p.output ∧
      s.gpr .r2 = p.domain ∧ (stackArg s 0).toNat = p.k ∧
      (stackArg s 2).toNat = p.len ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r3).toNat = p.dom ∧
      (s.gpr .r1).toNat = Spec.Ffdh.generationPrecomputedWords p.k ∧
      p.privateValue=p.output ∧ p.publicValue=p.output ∧ p.entropy=p.output ∧
      CombPrecomputeFnInput p s := by
  have original := pre
  have plain := (pre_consts.mp pre).1
  sig_pre [Spec.Ffdh.generationPrecomputeContract,Spec.Ffdh.generationPrecomputeSig,
    abi,argRegs,reduceClassify,Loc.val,State.addr] at plain
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,bounds,domainLen,ctxLen,space,_⟩ := plain
  change Spec.Ffdh.pLenValid (stackArg s 0).toNat at bounds
  change Spec.Ffdh.domainLenValid (stackArg s 0).toNat (s.gpr .r3).toNat at domainLen
  change Spec.Rsa.scratchWords (stackArg s 0).toNat ≤ (stackArg s 2).toNat at space
  change (s.gpr .r1).toNat = Spec.Ffdh.generationPrecomputedWords (stackArg s 0).toNat at ctxLen
  let dom := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat
  have domLength : dom.length = (s.gpr .r3).toNat := VG.Proof.Bignum.bytesAt_length _ _ _
  let p : Inputs := {
    base := stackArg s 1
    domain := s.gpr .r2
    publicValue := s.gpr .r0
    privateValue := s.gpr .r0
    output := s.gpr .r0
    entropy := s.gpr .r0
    len := (stackArg s 2).toNat
    k := (stackArg s 0).toNat
    privateLength := (stackArg s 0).toNat
    hasQ := decide ((s.gpr .r3).toNat = 3*(stackArg s 0).toNat)
    dom := dom
    minLength := bounds.1
    maxLength := bounds.2
    space := space
    domainLength := by
      rw [domLength]
      simp only [decide_eq_true_eq]
      split
      · assumption
      · rename_i different
        rcases domainLen with h | h
        · exact h
        · exact False.elim (different h) }
  have environment := combPrecompute_environment s original (p:=p) rfl rfl rfl rfl rfl rfl
  exact ⟨p,rfl,rfl,rfl,rfl,rfl,rfl,ctxLen,rfl,rfl,rfl,
    combPrecompute_input s original rfl rfl rfl rfl rfl rfl rfl rfl rfl environment⟩

end VG.Proof.Ffdh.Arm
