module

import VerifiedGarbage.Proof.Ffdh.Arm.VettedValidation.Body
public import VerifiedGarbage.Proof.Ffdh.Arm.DomainFn
public import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsEnvironment
import VerifiedGarbage.Proof.Ffdh.Arm.DomainEntry
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Syms
public import VerifiedGarbage.Impl.Ffdh.Arm.VettedValidation
public import VerifiedGarbage.Proof.Ffdh.Arm.DomainBody
public import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsState

/-! The recognized-domain checker uses the existing 128-byte AAPCS frame. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.VettedValidation
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Impl.Ffdh.Arm.VettedGroups (tableSym groups)

structure Input (p : Inputs) (s : State) : Prop extends DomainFnInput p s where
  table : VettedGroups.TableAt ((entered s).syms tableSym) groups (entered s)
  safe : VettedGroups.TableSafe ((entered s).syms tableSym) groups
    [⟨State.addr (entered s).sp, 72⟩]

theorem entered_ok (s : State) {p : Inputs}
    (h : ArgumentMemory p [] s)
    (domain : s.gpr .r0 = p.domain) (domainLength : s.gpr .r1 = BitVec.ofNat 32 p.dom.length)
    (count : s.gpr .r2 = BitVec.ofNat 32 p.k) (scratch : s.gpr .r3 = p.base)
    (table : VettedGroups.TableAt (s.syms tableSym) groups s)
    (safe : VettedGroups.TableSafe (s.syms tableSym) groups [⟨State.addr s.sp, 72⟩]) :
    WP isa (.seq (.block VG.Impl.Ffdh.Arm.Domain.CheckDomain.entry)
      VG.Impl.Ffdh.Arm.VettedValidation.body) s fun t =>
      t.gpr .r0 = checkedDomainFlag p ∧ Frame (bodyWrites p s) s.mem t.mem := by
  rw [WP.seq_iff]
  refine WP.mono_syms (withAllRest (domainEntry_ok s h domain domainLength count scratch)) ?_
  rintro u ⟨⟨context, frameU⟩, restU⟩ syms
  have tableU := table.after_frame safe frameU restU
  rw [← syms] at tableU
  refine WP.mono (body_ok u context (by decide) (by decide) (by decide)
    (by decide) (by decide) tableU) ?_
  rintro t ⟨result, frameT⟩
  have entryFrame : Frame (bodyWrites p s) s.mem u.mem := frameU.mono (by simp [bodyWrites])
  change Frame [⟨State.addr p.base, 8 * p.len⟩, ⟨State.addr u.sp, 72⟩] u.mem t.mem at frameT
  rw [restU.sp] at frameT
  exact ⟨result, entryFrame.trans frameT⟩

theorem fn_ok (s : State) {p : Inputs} (h : Input p s) :
    WP isa VG.Impl.Ffdh.Arm.VettedValidation.code s fun t =>
      abiPreserved s t ∧ t.gpr .r0 = checkedDomainFlag p := by
  unfold VG.Impl.Ffdh.Arm.VettedValidation.code
  refine framed_of_separate _ s h.stackFits (bodyWrites p (entered s))
    (fun _ status => status = checkedDomainFlag p) h.saved ?_
  refine WP.mono (entered_ok (entered s) h.args h.domain h.domainLength
    h.count h.scratch h.table h.safe) ?_
  rintro t ⟨result, frame⟩
  exact ⟨frame, result⟩

end VG.Proof.Ffdh.Arm.VettedValidation
