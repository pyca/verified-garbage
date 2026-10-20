module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PrimeLoop
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PrimeLoop
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawCopyCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SampleCT
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Kernel
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.TapeSlice
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawCopyCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SampleRoundCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SampleRoundCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawBuffer
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawBuffer

/-! A complete entropy draw and shared primality round have a public trace. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MillerRabin.AArch64

def DrawSized (len drawBytes : Nat) (p : DrawPublic) (s : State) : Prop :=
  DrawBefore len drawBytes p s ∧ p.used + p.prime.drawBytes ≤ p.prime.rand.length

def DrawPublic.sample (p : DrawPublic) (h : p.used + p.prime.drawBytes ≤ p.prime.rand.length) : SamplePublic :=
  ⟨p.prime, p.prime.drawSlice p.used, p.prime.slice_length h⟩

theorem drawSample_state {len drawBytes : Nat} {p : DrawPublic} {s : State} (h : DrawSized len drawBytes p s) :
    WP isa (Impl.Dsa.AArch64.Generation.drawCopy len drawBytes) s (SampleSized len (p.sample h.2)) := by
  have hw := drawBuffer_ok h.1.1 h.2
  rw [h.1.2.1, h.1.2.2] at hw
  exact WP.mono hw fun _ ⟨_, ht, _, _⟩ => ⟨ht, (p.prime.slice_length h.2).trans h.1.2.1⟩

theorem drawRound_ct (M : Mont) (K : Kernel) (len drawBytes : Nat) {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0])
      (.block (Impl.Dsa.AArch64.Generation.drawCopyArgs len drawBytes)) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.x1])
      (.block (Impl.Dsa.AArch64.Generation.forceWitness len)) hc₂).isSome = true) :
    RelCT isa (Two (DrawSized len drawBytes)) (Impl.Dsa.AArch64.Generation.drawRound M.mm K.run len drawBytes) (fun _ _ => True) := by
  unfold Impl.Dsa.AArch64.Generation.drawRound
  refine RelCT.seq (two_post (Ψ := fun p s => ∃ h, SampleSized len (p.sample h) s)
    (two_map id (fun _ _ h => h.1) (drawCopy_ct len drawBytes ht₁))
    (fun _ _ h => WP.mono (drawSample_state h) fun _ ht => ⟨h.2, ht⟩)) ?_
  apply (sampleRound_ct M K len ht₂).mono
  · rintro s t ⟨p, ⟨hs, h⟩, ⟨ht, h'⟩, hsp⟩
    exact ⟨p.sample hs, h, h', hsp⟩
  · exact fun _ _ h => h

end VG.Proof.Dsa.AArch64.Generation
