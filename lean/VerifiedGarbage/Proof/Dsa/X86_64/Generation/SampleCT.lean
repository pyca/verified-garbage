module
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TestWitnessCT
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Sample

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.StoredWitnessCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.StoredWitnessCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TestWitness
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TestWitness
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerStages

/-! # DSA witness selection branches only on the public sampled candidate -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def SampleSized (len : Nat) (p : SamplePublic) (s : State) : Prop :=
  SampleBefore p s ∧ p.bytes.length = len

def SampleTested (len : Nat) (p : SamplePublic) (s : State) : Prop :=
  SampleSized len p s ∧
    s.zf = some (!decide (2 ≤ Spec.Rsa.os2ip p.bytes ∧ Spec.Rsa.os2ip p.bytes < p.prime.N - 1))

theorem sampleTest_state {len : Nat} {p : SamplePublic} {s : State} (h : SampleSized len p s) :
    WP isa Impl.Dsa.X86_64.Generation.testWitness s (SampleTested len p) := by
  obtain ⟨⟨mi, hs⟩, hl⟩ := h
  refine WP.mono (testWitness_ok hs p.prime.dims p.prime.odd
    (by rw [p.length]; have := p.prime.len2; omega)
    (by rw [p.length]; have := p.prime.lenDraw; have := p.prime.drawMax; omega)
    (by rw [p.length]; exact p.prime.lenWords)) fun t ht => ?_
  exact ⟨⟨⟨mi, ht.1⟩, hl⟩, ht.2.2.2.1⟩

theorem sampleWitness_ct (len : Nat) : RelCT isa (Two (SampleSized len))
    (Impl.Dsa.X86_64.Generation.sampleWitness) (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Generation.sampleWitness
  refine RelCT.seq (two_post
    (two_map id (fun _ _ h => h.1) testWitness_ct)
    (fun _ _ h => sampleTest_state h)) ?_
  refine two_ite (fun _ _ _ hs ht => by simp only [eval, hs.2, ht.2]) ?_ ?_
  · refine RelCT.seq (two_post (Ψ := fun p s => SampleBefore p.forced s)
      (two_map id (fun _ _ h => h.1.1.1) forceStoredWitness_ct) ?_) ?_
    · exact fun p s h => forceSample_state h.1.1.1
    · exact two_map SamplePublic.forced (fun _ _ h => h) sampleLoad_ct
  · exact RelCT.block_nil (fun _ _ _ => True.intro)

end VG.Proof.Dsa.X86_64.Generation
