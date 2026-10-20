module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeState
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PaddedLoadCT
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.TestWitness
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SampleState
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessRangeCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessRange
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoadWitness
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeState
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PaddedLoadCT
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.TestWitness
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SampleState
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessRangeCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessRange
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoadWitness
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Timing of the DSA witness interval test -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Proof.Ffdh.X86_64.ParameterCandidate

structure SamplePublic where
  prime : PrimeParams
  bytes : List Byte
  length : bytes.length = prime.len

def SampleBefore (p : SamplePublic) (s : State) : Prop :=
  ∃ mi, SampleState p.prime.B p.prime.p p.prime.Z p.prime.w p.prime.N mi p.bytes s

def SamplePublic.padded (p : SamplePublic) : PaddedPublic :=
  ⟨p.prime.B, p.prime.Z, p.prime.w, p.prime.p, p.bytes.length⟩

def SampleLoaded (p : SamplePublic) (s : State) : Prop :=
  ∃ mi, ModulusReady s p.prime.B p.prime.Z p.prime.w mi p.prime.N ∧
    wv s.mem p.prime.B (slot p.prime.w aXm) p.prime.w = Spec.Rsa.os2ip p.bytes

theorem sampleLoad_ct : RelCT isa (Two SampleBefore)
    (Impl.Dsa.X86_64.Generation.loadPadded aXm kOut kUsedP) (fun _ _ => True) := by
  refine two_map SamplePublic.padded (fun p s h => ?_)
    (loadPadded_ct (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide))
  obtain ⟨mi, h⟩ := h
  exact ⟨⟨mi, h.ready.good⟩, p.prime.dims.z,
    by have := p.prime.dims.w4; dsimp [SamplePublic.padded]; omega,
    by have := p.prime.dims.w128; dsimp [SamplePublic.padded]; omega, h.ptr, h.len⟩

theorem sampleLoad_state {p : SamplePublic} {s : State} (h : SampleBefore p s) :
    WP isa (Impl.Dsa.X86_64.Generation.loadPadded aXm kOut kUsedP) s (SampleLoaded p) := by
  obtain ⟨mi, h⟩ := h
  have hl : 1 ≤ p.bytes.length := by rw [p.length]; have := p.prime.len2; omega
  have hb : p.bytes.length < 2 ^ 31 := by
    rw [p.length]; have := p.prime.lenDraw; have := p.prime.drawMax; omega
  exact WP.mono (loadWitness_ok h.ready p.prime.dims (by decide) (by decide) h.ptr h.len h.source
    hl hb (by rw [p.length]; exact p.prime.lenWords)) fun _ ht => ⟨mi, ht.1, ht.2.1⟩

theorem sampleRange_ct : RelCT isa (Two SampleLoaded)
    Impl.Ffdh.X86_64.ParameterCandidate.witnessRange (fun _ _ => True) := by
  refine two_map (fun p : SamplePublic => p.padded.workspace) (fun p s h => ?_) witnessRange_ct
  obtain ⟨mi, h, _⟩ := h
  exact ⟨⟨mi, h.good, p.prime.dims.z⟩,
    by have := p.prime.dims.w4; dsimp [SamplePublic.padded, PaddedPublic.workspace]; omega,
    by have := p.prime.dims.w128; dsimp [SamplePublic.padded, PaddedPublic.workspace]; omega⟩

theorem sampleRange_state {p : SamplePublic} {s : State} (h : SampleLoaded p s) :
    WP isa Impl.Ffdh.X86_64.ParameterCandidate.witnessRange s
      (fun t => t.gpr .rdi = p.prime.B) := by
  obtain ⟨mi, h, hx⟩ := h
  exact WP.mono (witnessRange_ok h p.prime.dims p.prime.odd hx) fun _ ht => ht.2.2.1.good.rdi

theorem testWitness_ct : RelCT isa (Two SampleBefore)
    Impl.Dsa.X86_64.Generation.testWitness (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Generation.testWitness
  simp only [seqs]
  refine RelCT.seq (two_post sampleLoad_ct (fun _ _ h => sampleLoad_state h)) ?_
  refine RelCT.seq (two_post sampleRange_ct (fun _ _ h => sampleRange_state h)) ?_
  exact two_taint [.rdi] (by
    intro p s t hs ht r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact hs.trans ht.symm) (by taint_decide)

end VG.Proof.Dsa.X86_64.Generation
