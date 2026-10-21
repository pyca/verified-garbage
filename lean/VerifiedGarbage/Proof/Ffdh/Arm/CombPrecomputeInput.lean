module

public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeState
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeEntry
public import VerifiedGarbage.Proof.Ffdh.Arm.Frame
public import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsEnvironment
import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.Proof.Ffdh.Arm.IncomingWord
public import VerifiedGarbage.Spec.Ffdh.Contract

/-! Native ABI inputs for initializing one public comb context. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

def combPrecomputeWrites (p : Inputs) (s : State) : List Region :=
  [⟨State.addr p.base,8*p.len⟩,⟨State.addr p.output,CombBuilder.bytes p⟩,
    ⟨State.addr s.sp,72⟩,FrameStack.belowA s.sp 48]

structure CombPrecomputeFnInput (p : Inputs) (s : State) : Prop where
  stackFits : 176 ≤ s.sp.toNat
  args : ArgumentMemory p [] (entered s)
  incomingCount : IncomingWord (BitVec.ofNat 32 p.k) 128 (entered s)
  incomingBase : IncomingWord p.base 132 (entered s)
  outputReg : s.gpr .r0 = p.output
  domainReg : s.gpr .r2 = p.domain
  domainLengthReg : s.gpr .r3 = BitVec.ofNat 32 p.dom.length
  calls : KeyCallMemory p (entered s)
  output : OutputBuffer p.output (CombBuilder.bytes p) (entered s)
  workspaceSeparate : Region.Disjoint ⟨State.addr p.base,8*p.len⟩ ⟨State.addr p.output,CombBuilder.bytes p⟩
  domainSeparate : Region.Disjoint ⟨State.addr p.domain,p.dom.length⟩ ⟨State.addr p.output,CombBuilder.bytes p⟩
  localSeparate : Region.Disjoint ⟨State.addr (entered s).sp,72⟩ ⟨State.addr p.output,CombBuilder.bytes p⟩
  callSeparate : Region.Disjoint ⟨State.addr p.output,CombBuilder.bytes p⟩ (FrameStack.belowA (entered s).sp 48)
  valid : Spec.Ffdh.domainValid p.k p.dom
  environment : VettedGroups.environment.holds p (entered s)
  saved : ∀ r ∈ combPrecomputeWrites p (entered s),
    (⟨State.addr (pcPushed s).sp,56⟩ : Region).Disjoint r

end VG.Proof.Ffdh.Arm
