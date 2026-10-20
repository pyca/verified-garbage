module

import VerifiedGarbage.Proof.Ffdh.Arm.DomainEntry
public import VerifiedGarbage.Proof.Ffdh.Arm.DomainBody
public import VerifiedGarbage.Proof.Ffdh.Arm.Frame
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
import VerifiedGarbage.Impl.Ffdh.Arm.Domain

/-! The native domain check, from its entry through AAPCS restoration. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont

theorem domainEntered_ok (s : State) {p : Inputs}
    (h : ArgumentMemory p [] s)
    (domain : s.gpr .r0 = p.domain) (domainLength : s.gpr .r1 = BitVec.ofNat 32 p.dom.length)
    (count : s.gpr .r2 = BitVec.ofNat 32 p.k) (scratch : s.gpr .r3 = p.base)
 :
    WP isa (.seq (.block VG.Impl.Ffdh.Arm.Domain.CheckDomain.entry)
      (VG.Impl.Ffdh.Arm.Domain.head VG.Impl.Ffdh.Arm.Domain.CheckDomain.main)) s fun t =>
      t.gpr .r0 = checkedDomainFlag p ∧ Frame (bodyWrites p s) s.mem t.mem := by
  rw [WP.seq_iff]
  refine WP.mono (withAllRest (domainEntry_ok s h domain domainLength count scratch)) ?_
  rintro u ⟨⟨contextU, frameU⟩, restU⟩
  refine WP.mono (domainBody_ok u contextU (by decide) (by decide) (by decide) (by decide) (by decide)) ?_
  rintro t ⟨result, frameT⟩
  refine ⟨result, ?_⟩
  have entryFrame : Frame (bodyWrites p s) s.mem u.mem := frameU.mono (by simp [bodyWrites])
  change Frame [⟨State.addr p.base, 8 * p.len⟩, ⟨State.addr u.sp, 72⟩] u.mem t.mem at frameT
  rw [restU.sp] at frameT
  exact entryFrame.trans frameT

structure DomainFnInput (p : Inputs) (s : State) : Prop where
  stackFits : 128 ≤ s.sp.toNat
  args : ArgumentMemory p [] (entered s)
  domain : s.gpr .r0 = p.domain
  domainLength : s.gpr .r1 = BitVec.ofNat 32 p.dom.length
  count : s.gpr .r2 = BitVec.ofNat 32 p.k
  scratch : s.gpr .r3 = p.base
  saved : ∀ r ∈ bodyWrites p (entered s), (⟨State.addr (pcPushed s).sp, 56⟩ : Region).Disjoint r

theorem domainFn_ok (s : State) {p : Inputs} (h : DomainFnInput p s) :
    WP isa VG.Impl.Ffdh.Arm.Domain.CheckDomain.code s fun t =>
      abiPreserved s t ∧ t.gpr .r0 = checkedDomainFlag p := by
  unfold VG.Impl.Ffdh.Arm.Domain.CheckDomain.code
  refine framed_of_separate _ s h.stackFits (bodyWrites p (entered s))
    (fun _ status => status = checkedDomainFlag p) h.saved ?_
  refine WP.mono (domainEntered_ok (entered s) h.args h.domain h.domainLength
    h.count h.scratch) ?_
  rintro t ⟨result, frame⟩
  exact ⟨frame, result⟩

end VG.Proof.Ffdh.Arm
