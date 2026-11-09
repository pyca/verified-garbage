module

import VerifiedGarbage.Proof.Ffdh.Arm.DomainEntry
public import VerifiedGarbage.Proof.Ffdh.Arm.DomainBody
public import VerifiedGarbage.Proof.Ffdh.Arm.Frame
import VerifiedGarbage.Proof.Ffdh.Arm.Block
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain

/-! The native domain check, from its entry through AAPCS restoration. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont

structure DomainFnInput (p : Inputs) (s : State) : Prop where
  stackFits : 128 ≤ s.sp.toNat
  args : ArgumentMemory p [] (entered s)
  domain : s.gpr .r0 = p.domain
  domainLength : s.gpr .r1 = BitVec.ofNat 32 p.dom.length
  count : s.gpr .r2 = BitVec.ofNat 32 p.k
  scratch : s.gpr .r3 = p.base
  saved : ∀ r ∈ bodyWrites p (entered s), (⟨State.addr (pcPushed s).sp, 56⟩ : Region).Disjoint r

end VG.Proof.Ffdh.Arm
