module

import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinOutcome
public import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessStep
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinState
public import VerifiedGarbage.Proof.RsaKeyGen.MrCounts

/-! # A native witness draw advances the reviewed loop's exact counters and status -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MillerRabinLoop
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen

theorem draw_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Spec.Rsa.Mont.mulContract abi 16))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 16)
    (roundVerified : Verified target round (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact 56))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 56)
    {P : Parameters} (v : P.Valid) {s : State} {k n : Nat} (S : StateAt P k n s)
    (enough : P.start + P.bytes * k + P.bytes ≤ P.randLen) :
    WP isa (VG.Impl.RsaKeyGen.X86.WitnessStep.code P.g.w montName mont roundName round) s fun t =>
      Prepare.Data P.g P.candidate P.capacity P.p t ∧
      w32 t.mem P.g.W 152 = P.start + P.bytes * k + P.bytes ∧ w32 t.mem P.g.W 176 = k + 1 ∧
      w32 t.mem P.g.W 192 = (mrSB P.candidate P.bytes P.start P.entropy (k + 1)).2 ∧
      w32 t.mem P.g.W 168 =
        (if Spec.RsaKeyGen.mrIteration P.candidate P.twos.1 P.twos.2
            (wit P.candidate P.bytes P.entropy (P.start + P.bytes * k)).1 then
          if goS P.checks (mrSB P.candidate P.bytes P.start P.entropy (k + 1)) then 4 else 1
        else 3) ∧
      WorkspaceFrame P.g (WitnessStep.ranges P.g) s.mem t.mem ∧
      Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 68]) s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  have counts := S.countFit v
  refine WP.mono (WitnessStep.code_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v.geometry
    v.length S.prepared S.randPtr S.used v.randFit v.randLenFit enough S.readable v.randSeparate v.odd (by have := v.large; omega)
    v.shape counts.1 counts.2 v.low v.stackFar v.lengthFar) fun t ⟨T, used, rounds, uniform, status, W, F, K⟩ => ?_
  rw [show 8 * P.g.w = P.bytes from rfl] at uniform status
  rw [S.rounds] at rounds
  rw [S.sample enough, S.uniform, ← mrSB_uniform_next] at uniform
  rw [S.sample enough, S.rounds, S.uniform, S.checks, count_policy] at status
  exact ⟨T, used, rounds, uniform, status, W, F, K⟩

end VG.Proof.RsaKeyGen.X86.MillerRabinLoop
