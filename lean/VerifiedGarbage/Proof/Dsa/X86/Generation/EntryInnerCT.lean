module
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Proof.Dsa.X86.Generation.OuterSetup
public import Aesop.BuiltinRules
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Hashes
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PublicCT
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckCall
import VerifiedGarbage.Proof.Dsa.X86.Generation.AllocationCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.EntryNarrow
import VerifiedGarbage.Proof.Dsa.X86.Generation.EntryNarrowCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameAllocation
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Framing the inner generator adds no data-dependent accesses -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem afterSave_room {s a : State} (A : ParameterABI s) (K : Keeps [] (allocated 16 s) a) :
    148 ≤ (a.gpr .esp).toNat := by
  rw [K.1 _ (by decide), allocated_esp, sub_toNat (by have := A.stackLow; omega)]
  have := A.stackLow
  omega

theorem entryInner_sp (H : GenerationHashes) (F : KeyRandom.CheckCall.CheckFn)
    {s a : State} (A : ParameterABI s)
    (O : Frame [⟨outerBase s, 16⟩] (allocated 16 s).mem a.mem) (K : Keeps [] (allocated 16 s) a) :
    WP isa (.frame (.alloc 148) (entryBody H.sha1 H.sha256 F.name F.code) (.free 148)) a
      (fun t => t.gpr .esp = a.gpr .esp) := by
  apply alloc_restored (by decide) (afterSave_room A K)
  refine WP.mono (entryBody_narrow_ok H F (afterSave_start A O K)) fun t result => ?_
  exact ⟨result.2.2.2.2.2, by rw [freed_esp, result.2.2.2.2.2, allocated_esp, BitVec.sub_add_cancel]⟩

theorem entryInner_ct (H : GenerationHashes) (F : KeyRandom.CheckCall.CheckFn)
    {s t a b u v : State} {tsa tsb : List Leak} (A : ParameterABI s) (B : ParameterABI t)
    (pub : GenerationPublicAgree s t)
    (Oa : Frame [⟨outerBase s, 16⟩] (allocated 16 s).mem a.mem) (Ka : Keeps [] (allocated 16 s) a)
    (Ob : Frame [⟨outerBase t, 16⟩] (allocated 16 t).mem b.mem) (Kb : Keeps [] (allocated 16 t) b)
    (ea : Exec isa (.frame (.alloc 148) (entryBody H.sha1 H.sha256 F.name F.code) (.free 148)) a tsa u)
    (eb : Exec isa (.frame (.alloc 148) (entryBody H.sha1 H.sha256 F.name F.code) (.free 148)) b tsb v) :
    tsa = tsb ∧ u.gpr .esp = v.gpr .esp := by
  have spa := wp_result (entryInner_sp H F A Oa Ka) ea
  have spb := wp_result (entryInner_sp H F B Ob Kb) eb
  refine ⟨?_, ?_⟩
  · cases ea with
    | frame pa ba _ =>
      cases eb with
      | frame pb bb _ =>
        rw [allocated_push (by decide) (afterSave_room A Ka), Option.some.injEq] at pa
        rw [allocated_push (by decide) (afterSave_room B Kb), Option.some.injEq] at pb
        subst pa pb
        have trace := (entryNarrow_ct H F pub (afterSave_start A Oa Ka) (afterSave_start B Ob Kb) ba bb).1
        simpa only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] using trace
  · rw [spa, spb, Ka.1 _ (by decide), Kb.1 _ (by decide), allocated_esp, allocated_esp, pub.sp]
end VG.Proof.Dsa.X86.Generation
