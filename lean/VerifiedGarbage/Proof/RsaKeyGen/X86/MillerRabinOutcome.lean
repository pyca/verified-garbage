module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinState
public import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessStatus
public import VerifiedGarbage.Spec.RsaKeyGen
public import VerifiedGarbage.Proof.RsaKeyGen.MrCounts

/-! # Match native loop status with the reviewed primality result -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MillerRabinLoop
open VG VG.X86 VG.Proof.Mont VG.Proof.RsaKeyGen

def Result (P : Parameters) (s : State) : Prop :=
  match P.test with
  | none => w32 s.mem P.g.W 168 = 0
  | some (prime, rest) => w32 s.mem P.g.W 168 = (if prime then 1 else 3) ∧
      w32 s.mem P.g.W 152 = P.entropy.length - rest.length

theorem count_policy (P : Parameters) (k : Nat) :
    WitnessStatus.status
      (Proof.MillerRabin.Round.round P.candidate (wit P.candidate P.bytes P.entropy (P.start + P.bytes * k)).1)
      (k + 1) ((mrSB P.candidate P.bytes P.start P.entropy k).2 +
        (wit P.candidate P.bytes P.entropy (P.start + P.bytes * k)).2.toNat) P.checks =
      if Spec.RsaKeyGen.mrIteration P.candidate P.twos.1 P.twos.2
          (wit P.candidate P.bytes P.entropy (P.start + P.bytes * k)).1 then
        if goS P.checks (mrSB P.candidate P.bytes P.start P.entropy (k + 1)) then 4 else 1
      else 3 := by
  have counts : (k + 1 < 16 ∨ (mrSB P.candidate P.bytes P.start P.entropy k).2 +
      (wit P.candidate P.bytes P.entropy (P.start + P.bytes * k)).2.toNat < P.checks) ↔
      goS P.checks (mrSB P.candidate P.bytes P.start P.entropy (k + 1)) := by
    unfold goS
    rw [mrSB_first, mrSB_uniform_next]
    unfold Spec.RsaKeyGen.blindedChecks
    omega
  unfold WitnessStatus.status
  simp only [counts]
  rfl

theorem StateAt.noEntropy {P : Parameters} (v : P.Valid) {s : State} {k n : Nat} (S : StateAt P k n s)
    (short : ¬ P.start + P.bytes * k + P.bytes ≤ P.randLen) :
    n = 0 ∧ P.test = none :=
  mrLoopAt_short S.atLoop v.witnessBytes (by have := v.narrow; have := v.two; omega)
    (by rw [v.entropyLength]; exact short)

theorem StateAt.failed {P : Parameters} (v : P.Valid) {s : State} {k n : Nat} (S : StateAt P k n s)
    (enough : P.start + P.bytes * k + P.bytes ≤ P.randLen)
    (failed : Spec.RsaKeyGen.mrIteration P.candidate P.twos.1 P.twos.2
      (wit P.candidate P.bytes P.entropy (P.start + P.bytes * k)).1 = false) :
    n = 0 ∧ P.test =
      some (false, P.entropy.drop (P.start + P.bytes * k + P.bytes)) :=
  mrLoopAt_fail S.atLoop v.witnessBytes (by have := v.narrow; have := v.two; omega)
    (by rw [v.entropyLength]; exact enough) failed

theorem StateAt.accepted {P : Parameters} (v : P.Valid) {s : State} {k n : Nat} (S : StateAt P k n s)
    (enough : P.start + P.bytes * k + P.bytes ≤ P.randLen)
    (passed : Spec.RsaKeyGen.mrIteration P.candidate P.twos.1 P.twos.2
      (wit P.candidate P.bytes P.entropy (P.start + P.bytes * k)).1 = true)
    (done : ¬ goS P.checks (mrSB P.candidate P.bytes P.start P.entropy (k + 1))) :
    n = 0 ∧ P.test =
      some (true, P.entropy.drop (P.start + P.bytes * k + P.bytes)) :=
  mrLoopAt_done S.atLoop v.witnessBytes (by have := v.narrow; have := v.two; omega)
    (by rw [v.entropyLength]; exact enough) passed done

end VG.Proof.RsaKeyGen.X86.MillerRabinLoop
