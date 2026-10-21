module

import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicEntry
public import VerifiedGarbage.Proof.Ffdh.Arm.SharedCheckPublicBody
public import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicFn
public import VerifiedGarbage.Proof.Ffdh.Arm.Frame
import VerifiedGarbage.Proof.Ffdh.Arm.Block
public import VerifiedGarbage.Proof.Ffdh.Arm.EntryStore
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain

/-! The native public-value check, from its entry through AAPCS restoration. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont

theorem sharedCheckPublicEntered_ok (backend : MontBackend) (s : State) {p : Inputs} {yb : List Byte}
    (h : ArgumentMemory p [] s) (incoming : IncomingScratch p s) (calls : DomainCallMemory p s)
    (domain : s.gpr .r0 = p.domain) (domainLength : s.gpr .r1 = BitVec.ofNat 32 p.dom.length)
    (count : s.gpr .r2 = BitVec.ofNat 32 p.k) (publicValue : s.gpr .r3 = p.publicValue)
    (value : Octets p.base p.publicValue p.len yb s) (length : yb.length = p.k)
    (valueStack : Region.Disjoint ⟨State.addr p.publicValue, yb.length⟩ ⟨State.addr s.sp, 72⟩) :
    WP isa (.seq (.block VG.Impl.Ffdh.Arm.Domain.CheckPublic.entry)
      (VG.Impl.Ffdh.Arm.Domain.head (VG.Impl.Ffdh.Arm.SharedCheckPublic.main (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)))) s fun t =>
      t.gpr .r0 = checkedPublicFlag p (Spec.Rsa.os2ip yb) ∧ Frame (sharedPublicBodyWrites p s) s.mem t.mem := by
  rw [WP.seq_iff]
  refine WP.mono (withAllRest (checkPublicEntry_ok s h incoming domain domainLength count publicValue)) ?_
  rintro u ⟨⟨contextU, frameU⟩, restU⟩
  have valueU := value.after_frame frameU restU (by
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact valueStack)
  have valueStackU : Region.Disjoint ⟨State.addr p.publicValue, yb.length⟩ ⟨State.addr u.sp, 72⟩ := by
    rw [restU.sp]; exact valueStack
  refine WP.mono (sharedCheckPublicBody_ok backend u contextU (calls.after restU) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) valueU length valueStackU) ?_
  rintro t ⟨result, frameT⟩
  refine ⟨result, ?_⟩
  have entryFrame : Frame (sharedPublicBodyWrites p s) s.mem u.mem := frameU.mono (by simp [sharedPublicBodyWrites, bodyWrites])
  change Frame [⟨State.addr p.base, 8 * p.len⟩, ⟨State.addr u.sp, 72⟩, FrameStack.belowA u.sp 48] u.mem t.mem at frameT
  rw [restU.sp] at frameT
  exact entryFrame.trans frameT

structure SharedCheckPublicFnInput (p : Inputs) (yb : List Byte) (s : State) : Prop where
  input : CheckPublicFnInput p yb s
  calls : DomainCallMemory p (entered s)
  saved : ∀ r ∈ sharedPublicBodyWrites p (entered s),
    (⟨State.addr (pcPushed s).sp, 56⟩ : Region).Disjoint r

theorem sharedCheckPublicFn_ok (backend : MontBackend) (s : State) {p : Inputs} {yb : List Byte} (h : SharedCheckPublicFnInput p yb s) :
    WP isa (VG.Impl.Ffdh.Arm.SharedCheckPublic.code (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) s fun t =>
      abiPreserved s t ∧ t.gpr .r0 = checkedPublicFlag p (Spec.Rsa.os2ip yb) := by
  unfold VG.Impl.Ffdh.Arm.SharedCheckPublic.code
  refine framed_of_separate _ s h.input.stackFits (sharedPublicBodyWrites p (entered s))
    (fun _ status => status = checkedPublicFlag p (Spec.Rsa.os2ip yb)) h.saved ?_
  refine WP.mono (sharedCheckPublicEntered_ok backend (entered s) h.input.args h.input.incoming h.calls h.input.domain h.input.domainLength
    h.input.count h.input.publicValue h.input.value h.input.length h.input.valueStack) ?_
  rintro t ⟨result, frame⟩
  exact ⟨frame, result⟩

end VG.Proof.Ffdh.Arm
