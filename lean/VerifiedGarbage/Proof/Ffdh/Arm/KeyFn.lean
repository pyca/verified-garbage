module

public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyEntry
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyOutputs
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyTail
public import VerifiedGarbage.Proof.Ffdh.Arm.Frame
import VerifiedGarbage.Proof.Ffdh.Arm.Block

/-! AAPCS key generation from caller-provided entropy with native rejection. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

structure KeyFnInput (p : Inputs) (rb : List Byte) (s : State) : Prop where
  stackFits : 128 ≤ s.sp.toNat
  args : ArgumentMemory p [] (entered s)
  incoming : KeyIncoming p (entered s)
  privateValue : s.gpr .r0 = p.privateValue
  publicValue : s.gpr .r2 = p.publicValue
  outputY : p.output = p.publicValue
  privateLength : p.privateLength = p.k
  entropy : Octets p.base p.entropy p.len rb (entered s)
  size : rb.length = p.k
  entropyStack : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr (entered s).sp, 72⟩
  outputs : KeyOutputs p (entered s)
  entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩
  saved : ∀ r ∈ keyWrites p (entered s), (⟨State.addr (pcPushed s).sp, 56⟩ : Region).Disjoint r

end VG.Proof.Ffdh.Arm
