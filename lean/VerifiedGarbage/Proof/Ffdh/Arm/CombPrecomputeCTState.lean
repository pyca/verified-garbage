module

import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeInput
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeState
public import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsEnvironment

/-! Public geometry retained by the comb-builder timing composition. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm

structure EnterInput (p : Inputs) (sp : BitVec 32) (s : State) : Prop where
  context : Context p slots s
  environment : VettedGroups.environment.holds p s
  calls : KeyCallMemory p s
  output : OutputBuffer p.output (bytes p) s
  workspaceSeparate : Region.Disjoint ⟨State.addr p.base,8*p.len⟩ ⟨State.addr p.output,bytes p⟩
  domainSeparate : Region.Disjoint ⟨State.addr p.domain,p.dom.length⟩ ⟨State.addr p.output,bytes p⟩
  localSeparate : Region.Disjoint ⟨State.addr sp,72⟩ ⟨State.addr p.output,bytes p⟩
  callSeparate : Region.Disjoint ⟨State.addr p.output,bytes p⟩ (FrameStack.belowA sp 48)
  fixed : s.sp=sp
  valid : Spec.Ffdh.domainValid p.k p.dom=true

end VG.Proof.Ffdh.Arm.CombBuilder
