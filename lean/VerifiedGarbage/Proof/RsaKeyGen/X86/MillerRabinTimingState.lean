module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinState
public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessAvailable
public import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessStepTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessAvailable
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessAdvanceTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # The blinded loop's public pointers and shared number of remaining iterations -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MillerRabinLoop
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen VG.Proof.Dsa.X86

def Parameters.withSecret (P : Parameters) (c : Nat) (r : Spec.RsaKeyGen.Rand) : Parameters :=
  { P with candidate := c, entropy := r }

def LoopPair (P : Parameters) (other : Nat) (entropy : Spec.RsaKeyGen.Rand) (k n : Nat) (s t : State) : Prop :=
  Pair P.g [.edi] s t ∧ StateAt P k n s ∧ StateAt (P.withSecret other entropy) k n t

theorem StateAt.stepInitial {P : Parameters} (v : P.Valid) {s : State} {k n : Nat} (S : StateAt P k n s) :
    WitnessStep.Initial P.g P.capacity P.p P.rand (P.start + P.bytes * k) P.randLen s :=
  ⟨P.candidate, S.prepared, S.randPtr, S.used, v.odd, by have := v.large; omega, v.shape,
    (S.countFit v).1, (S.countFit v).2, S.readable⟩

theorem StateAt.available {P : Parameters} (v : P.Valid) {s : State} {k n : Nat} (S : StateAt P k n s) :
    WP isa (.block (VG.Impl.RsaKeyGen.X86.WitnessAvailable.code P.g.w)) s fun t =>
      StateAt P k n t ∧ isa.eval .b t = some (decide (P.randLen - (P.start + P.bytes * k) < P.bytes)) := by
  have usedBound : P.start + P.bytes * k ≤ P.randLen := by
    have := S.atLoop.used; rw [v.entropyLength] at this; exact this
  refine WP.mono (WitnessAvailable.code_ok (w := P.g.w) S.prepared.ready.scratch v.geometry.headerFit
    (by have := v.geometry.maxWidth; omega) S.randLength S.used usedBound) fun t ⟨CF, mem, K⟩ => ?_
  exact ⟨S.keepMem v mem K (by decide) (by decide), CF⟩

def AvailablePair (P : Parameters) (other : Nat) (entropy : Spec.RsaKeyGen.Rand) (k n : Nat) (s t : State) : Prop :=
  LoopPair P other entropy k n s t ∧
    isa.eval .b s = some (decide (P.randLen - (P.start + P.bytes * k) < P.bytes)) ∧
    isa.eval .b t = some (decide (P.randLen - (P.start + P.bytes * k) < P.bytes))

theorem available_pair {P : Parameters} (v : P.Valid) {other : Nat} {entropy : Spec.RsaKeyGen.Rand}
    (w : (P.withSecret other entropy).Valid) (k n : Nat) :
    RelCT isa (LoopPair P other entropy k n) (.block (VG.Impl.RsaKeyGen.X86.WitnessAvailable.code P.g.w))
      (AvailablePair P other entropy k n) := by
  intro s t tr ur u z H E G
  obtain ⟨trace, agree⟩ := WitnessAvailable.code_trace P.g.w _ _ _ _ _ _ H.1.2.2 E G
  obtain ⟨U, Cu⟩ := wp_result (H.2.1.available v) E
  obtain ⟨Z, Cz⟩ := wp_result (H.2.2.available w) G
  exact ⟨trace, ⟨⟨U.prepared.ready.context, Z.prepared.ready.context, agree⟩, U, Z⟩, Cu, Cz⟩

end VG.Proof.RsaKeyGen.X86.MillerRabinLoop
