module

import VerifiedGarbage.Proof.Ffdh.Arm.VettedValidation.RecognitionTiming
public import VerifiedGarbage.Impl.Ffdh.Arm.VettedValidation
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroups
import VerifiedGarbage.Proof.Ffdh.Arm.DomainBodyCT
import VerifiedGarbage.Proof.Ffdh.Arm.BranchCT
import VerifiedGarbage.Proof.Ffdh.Arm.Branch
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleEnvironment
public import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsState
public import VerifiedGarbage.Proof.Framework.RelCT

/-! The recognition decision depends only on public domain bytes. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.VettedValidation
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Impl.Ffdh.Arm.VettedGroups (groups recognize tableSym)

theorem body_ct {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots)
    (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) :
    RelCT isa (fun s t =>
      (Context p slots s ∧ VettedGroups.TableAt (s.syms tableSym) groups s) ∧
      (Context p slots t ∧ VettedGroups.TableAt (t.syms tableSym) groups t) ∧
      s.sp = t.sp ∧ s.syms tableSym = t.syms tableSym)
      VG.Impl.Ffdh.Arm.VettedValidation.body (fun _ _ => True) := by
  let P := fun s : State => Context p slots s ∧ VettedGroups.TableAt (s.syms tableSym) groups s
  let Q := fun s : State => Context p slots s ∧
    s.gpr .r11 = BitVec.ofNat 32 (recognize groups p.k p.dom)
  let R := fun s : State => Context p slots s ∧
    s.z = (BitVec.ofNat 32 (recognize groups p.k p.dom) == 0)
  have scan (s : State) (h : P s) : WP isa VG.Impl.Ffdh.Arm.VettedGroups.code s Q :=
    WP.mono (VettedGroups.code_ok s h.1 h24 h28 h32 h.2) fun _ out => ⟨out.1, out.2.1⟩
  have stage := (relCT_keep_sp (VettedGroups.recognition_ct h24 h28 h32)
    (fun _ _ h => h.2.2.1)).wp (fun s t h => ⟨scan s h.1, scan t h.2.1⟩)
  have test (s : State) (h : Q s) : WP isa VG.Impl.Ffdh.Arm.Domain.testFlag s R := by
    refine WP.mono (testFlag_ok s) ?_
    rintro t ⟨⟨zero, mem⟩, rest⟩
    exact ⟨h.1.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.1.ptr),
      by rw [zero, h.2]⟩
  have branches : RelCT isa (fun s t => R s ∧ R t ∧ s.sp = t.sp)
      (.ite .ne (VG.Impl.Ffdh.Arm.Domain.ret 1)
        (VG.Impl.Ffdh.Arm.Domain.head VG.Impl.Ffdh.Arm.Domain.CheckDomain.main)) (fun _ _ => True) := by
    apply iteKnown_ct (!(BitVec.ofNat 32 (recognize groups p.k p.dom) == 0))
      (fun s h => by change some (!s.z) = _; rw [h.2])
    · intro _
      exact (ret_ct 1).mono (fun _ _ _ => trivial) (fun _ _ h => h)
    · intro _
      exact (domainBody_ct stable h0 h24 h28 h32).mono
        (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h)
  have tail := relCT_chain (testFlag_ct.mono (P' := fun (s t : State) => Q s ∧ Q t ∧ s.sp = t.sp)
    (fun _ _ _ => trivial) (fun _ _ h => h)) test test branches
  unfold VG.Impl.Ffdh.Arm.VettedValidation.body
  exact stage.seq (tail.mono (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ h => h))

end VG.Proof.Ffdh.Arm.VettedValidation
