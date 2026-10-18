module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.StoredWitnessCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.StoredWitnessCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Sample
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Sample

/-! Witness selection branches only on the public sampled candidate. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def SampleSized (len : Nat) (p : SamplePublic) (s : State) : Prop :=
  SampleBefore p s ∧ p.bytes.length = len

def SampleTested (len : Nat) (p : SamplePublic) (s : State) : Prop :=
  SampleSized len p s ∧ s.gpr .x9 = VG.Proof.Bignum.mask
    (decide (2 ≤ Spec.Rsa.os2ip p.bytes ∧ Spec.Rsa.os2ip p.bytes < p.prime.N - 1))

theorem sampleTest_state {len : Nat} {p : SamplePublic} {s : State} (h : SampleSized len p s) :
    WP isa Impl.Dsa.AArch64.Generation.testWitness s (SampleTested len p) :=
  WP.mono (testWitness_ok h.1 p.prime.exponentRoom p.prime.odd
    (by rw [p.length]; have := p.prime.len2; omega) (by rw [p.length]; exact p.prime.lenWords))
    (fun _ ⟨ht, _, _, hr, _, _⟩ => ⟨⟨ht, h.2⟩, hr⟩)

theorem sampleWitness_ct (len : Nat) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x1])
      (.block (Impl.Dsa.AArch64.Generation.forceWitness len)) hc).isSome = true) :
    RelCT isa (Two (SampleSized len)) (Impl.Dsa.AArch64.Generation.sampleWitness len) (fun _ _ => True) := by
  unfold Impl.Dsa.AArch64.Generation.sampleWitness
  refine RelCT.seq (two_post (two_map id (fun _ _ h => h.1) testWitness_ct)
    (fun _ _ h => sampleTest_state h)) ?_
  refine two_ite (fun _ _ _ hs ht => by simp only [eval, State.read, hs.2, ht.2]) ?_ ?_
  · refine RelCT.seq (two_post (Ψ := fun p s => SampleBefore p.forced s)
      (two_map id (fun _ _ h => h.1.1.1) (forceStoredWitness_ct len ht)) ?_) ?_
    · intro p s h
      rw [← h.1.1.2]
      exact forceSample_state h.1.1.1
    · exact two_map SamplePublic.forced (fun _ _ h => h) sampleLoad_ct
  · exact RelCT.block_nil (fun _ _ _ => True.intro)

end VG.Proof.Dsa.AArch64.Generation
