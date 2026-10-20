module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawCopyCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawCopyCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SampleRoundCT
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PrimeLoop
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TapeSlice
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SampleRoundCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawBuffer
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawBuffer

/-! # Timing of a complete entropy draw and shared primality round -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64

def DrawSized (len drawBytes : Nat) (p : DrawPublic) (s : State) : Prop :=
  DrawBefore len drawBytes p s ∧ p.used + p.prime.drawBytes ≤ p.prime.rand.length

def DrawPublic.sample (p : DrawPublic) (h : p.used + p.prime.drawBytes ≤ p.prime.rand.length) : SamplePublic :=
  ⟨p.prime, p.prime.drawSlice p.used, p.prime.slice_length h⟩

theorem drawSample_state {len drawBytes : Nat} {p : DrawPublic} {s : State}
    (h : DrawSized len drawBytes p s) :
    WP isa (Impl.Dsa.X86_64.Generation.drawCopy len drawBytes) s
      (SampleRoundBefore len (p.sample h.2)) := by
  obtain ⟨mi, hs⟩ := h.1.1
  have hw := drawBuffer_ok hs h.2
  rw [h.1.2.1, h.1.2.2] at hw
  exact WP.mono hw fun _ ht =>
    ⟨⟨⟨mi, ht.2.1⟩, (p.prime.slice_length h.2).trans h.1.2.1⟩, ht.1.stack⟩

theorem drawRound_ct (M : Mont) (K : Kernel) (len drawBytes : Nat)
    {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rdi])
      (.block (Impl.Dsa.X86_64.Generation.drawCopyArgs len drawBytes)) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.rdi])
      (.block (Impl.Dsa.X86_64.Generation.forceWitness len)) hc₂).isSome = true) :
    RelCT isa (Two (DrawSized len drawBytes))
      (Impl.Dsa.X86_64.Generation.drawRound M.mm K.run len drawBytes) (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Generation.drawRound
  refine RelCT.seq (two_post (Ψ := fun p s => ∃ h, SampleRoundBefore len (p.sample h) s)
    (two_map id (fun _ _ h => h.1) (drawCopy_ct len drawBytes ht₁))
    (fun _ _ h => WP.mono (drawSample_state h) fun _ ht => ⟨h.2, ht⟩)) ?_
  apply (sampleRound_ct M K len ht₂).mono
  · rintro s t ⟨p, ⟨hs, h⟩, ⟨ht, h'⟩⟩
    exact ⟨p.sample hs, h, h'⟩
  · exact fun _ _ h => h

end VG.Proof.Dsa.X86_64.Generation
