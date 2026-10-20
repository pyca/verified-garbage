module
public import Aesop.BuiltinRules
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass.Point
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.X86.Generation.EntryResult
public import VerifiedGarbage.Proof.Dsa.X86.Generation.EntryStart
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Hashes
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PublicCT
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Dsa.X86.Generation.EntryBody
import VerifiedGarbage.Proof.Dsa.X86.Generation.EntryBodyCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.EntryNarrow
import VerifiedGarbage.Proof.Dsa.X86.Generation.EntryPermissions
import VerifiedGarbage.Proof.Dsa.X86.Generation.EntryPublicCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.EntryReady
import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameCT

/-! # Timing proofs under precise arena permissions lift to the caller's execution -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem entryNarrow_run (H : GenerationHashes) (F : KeyRandom.CheckCall.CheckFn)
    {s a : State} {A : ParameterABI s} (R : EntryStart A a) :
    WP isa (entryBody H.sha1 H.sha256 F.name F.code) (a.withRegions s.rd (bodyWrites A))
      (EntryResult s (a.withRegions s.rd (bodyWrites A))) := by
  have run := entryBody_ok H F R.resources
    (observedWords_rep A.geometry.frameBase (a.withRegions s.rd (bodyWrites A))) (by
      intro i hi
      exact ⟨argRegion s 0 (arg s 1).toNat, by simp [bodyWrites],
        Offset.contains_base _ (by omega) (by have := (arg s 1).isLt; omega)⟩)
  exact WP.mono run fun _ h => generationResult_external h

theorem entryNarrow_ct (H : GenerationHashes) (F : KeyRandom.CheckCall.CheckFn)
    {s t a b u v : State} {A : ParameterABI s} {B : ParameterABI t} {tsa tsb : List Leak}
    (pub : GenerationPublicAgree s t) (Ra : EntryStart A a) (Rb : EntryStart B b)
    (ea : Exec isa (entryBody H.sha1 H.sha256 F.name F.code) a tsa u)
    (eb : Exec isa (entryBody H.sha1 H.sha256 F.name F.code) b tsb v) :
    tsa = tsb ∧ u.gpr .esp = v.gpr .esp := by
  obtain ⟨ta, ua, runA, _⟩ := entryNarrow_run H F Ra
  obtain ⟨tb, ub, runB, _⟩ := entryNarrow_run H F Rb
  have wideA := VG.X86.Exec.widen runA Ra.covers.1 Ra.covers.2
  have wideB := VG.X86.Exec.widen runB Rb.covers.1 Rb.covers.2
  rw [State.withRegions_withRegions, State.withRegions_self] at wideA wideB
  have traceA := (Exec.det ea wideA).1
  have traceB := (Exec.det eb wideB).1
  have trace := (entryBody_ct H F _ _ _ _ _ _ ⟨⟨s, A⟩, Ra.resources, entryResources_public pub Rb.resources⟩ runA runB).1
  refine ⟨by rw [traceA, traceB]; exact trace, ?_⟩
  have postA := wp_result (entryBody_narrow_ok H F Ra) ea
  have postB := wp_result (entryBody_narrow_ok H F Rb) eb
  rw [postA.2.2.2.2.2, postB.2.2.2.2.2, Ra.esp, Rb.esp]
  exact congrArg GenerationGeometry.frame pub.geometry
end VG.Proof.Dsa.X86.Generation
