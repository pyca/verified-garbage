module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinAfterDraw
import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinControl
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedDataGap

/-! # Too little entropy terminates the primality test with its specified failure -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MillerRabinLoop
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen
open VG.Impl.RsaKeyGen.X86.MillerRabinLoop

theorem exhausted_again_ok {P : Parameters} (v : P.Valid) {s : State} {k n : Nat} (S : StateAt P k n s)
    (short : ¬ P.start + P.bytes * k + P.bytes ≤ P.randLen) :
    WP isa (.seq (.block exhausted) (.block again)) s fun t =>
      Prepare.Data P.g P.candidate P.capacity P.p t ∧ Outcome P k n t ∧
      WorkspaceFrame P.g (WitnessStep.ranges P.g) s.mem t.mem ∧
      Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 108]) s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  have failed := S.noEntropy v short
  refine WP.seq (WP.mono (exhausted_ok v.geometry S.prepared) fun a ⟨A, statusA, Oa, Ka⟩ => ?_)
  refine WP.mono (again_ok v.geometry A.ready.scratch) fun t ⟨Z, mem, Kt⟩ => ?_
  have K : Keeps WitnessStep.clob s t := (Ka.mono (by unfold WitnessStep.clob; decide)).widen Kt
  have T := A.keepHeader v.geometry (d := 128) (bytes := 0) (by decide) (by decide)
    (show Outside P.g.W 128 0 a.mem t.mem from by rw [mem]; exact Outside.refl _ _ _ _) Kt (by decide) (by decide)
  have Ot : Outside P.g.W 168 4 s.mem t.mem := by rw [mem]; exact Oa
  have W : WorkspaceFrame P.g (WitnessStep.ranges P.g) s.mem t.mem :=
    WorkspaceFrame.of_outs S.prepared.ready.scratch.nowrap (Outs.of_outside Ot
      (by simp [WitnessStep.ranges, WitnessCount.ranges, VG.Impl.RsaKeyGen.X86.WitnessCount.statusOffset]))
  have F : Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 108]) s.mem t.mem :=
    (workspaceGlobalFrame (Outs.of_outside Ot (List.mem_singleton_self _))
      (fun r mem => by obtain rfl := List.mem_singleton.mp mem; have := v.geometry.headerFit; omega)).mono
      (fun r mem => List.mem_append_left _ mem)
  refine ⟨T, Or.inl ⟨?_, failed.1, ?_⟩, W, F, K⟩
  · change t.zf = some false
    rw [Z, statusA]; rfl
  · unfold Result
    rw [failed.2, mem]
    exact statusA

end VG.Proof.RsaKeyGen.X86.MillerRabinLoop
