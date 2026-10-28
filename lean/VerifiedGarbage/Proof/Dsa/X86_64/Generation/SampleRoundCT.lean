module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SampleCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SampleCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RoundTailCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RoundTailCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessRoundCT
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.SampleRound
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessRoundCT
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Round
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Round
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Sample
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Sample

/-! # Timing of witness selection, the shared round, and completion policy -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin.X86_64 VG.Proof.Ffdh.X86_64.ParameterCandidate

def SampleRoundBefore (len : Nat) (p : SamplePublic) (s : State) : Prop :=
  SampleSized len p s ∧ s.gpr .rsp = p.prime.sp

def SamplePublic.round (p : SamplePublic) : RoundPublic :=
  ⟨p.padded.workspace, p.prime.N,
    (Spec.RsaKeyGen.witness (p.prime.N - 1) (Spec.Rsa.os2ip p.bytes)).1, p.prime.sp⟩

theorem sampleRound_ready {len : Nat} {p : SamplePublic} {s : State}
    (h : SampleRoundBefore len p s) :
    WP isa (Impl.Dsa.X86_64.Generation.sampleWitness) s (BeforeRound p.round) := by
  obtain ⟨⟨⟨mi, hs⟩, -⟩, hsp⟩ := h
  refine WP.mono (sampleWitness_ok hs p.prime.dims p.prime.odd
    (by rw [p.length]; exact p.prime.len2)
    (by rw [p.length]; have := p.prime.lenDraw; have := p.prime.drawMax; omega)
    (by rw [p.length]; exact p.prime.lenWords)
    (by rw [p.length]; exact p.prime.predBits)) fun t ht => ?_
  have hst : t.gpr .rsp = p.prime.sp := (ht.2.2.2.2.gpr (by decide)).trans hsp
  exact ⟨mi, ht.1, p.prime.dims, p.prime.room,
    ⟨by rw [hst]; exact p.prime.stackSize, by rw [hst]; exact p.prime.stackSeparate⟩,
    hst, p.prime.odd, p.prime.n3, ht.2.1⟩

def roundTailPublic (p : RoundPublic) : RoundTailPublic :=
  ⟨p.ws.B, p.ws.Z, p.ws.w, Spec.RsaKeyGen.mrIteration p.N
    (Spec.Rsa.splitTwos (p.N - 1)).1 (Spec.Rsa.splitTwos (p.N - 1)).2 p.a⟩

theorem roundTail_ready (M : Mont) (K : Kernel) {p : RoundPublic} {s : State}
    (h : BeforeRound p s) :
    WP isa (Impl.Ffdh.X86_64.ParameterCandidate.witnessRound M.mm K.run) s
      (RoundTailState (roundTailPublic p)) := by
  obtain ⟨mi, h, hd, hz, hr, _, ho, hn, ha⟩ := h
  exact WP.mono (round_ok M K h hd hz hr ho hn ha) fun _ ht =>
    ⟨⟨mi, ht.1.good⟩, hd.z, ht.2.1⟩

theorem sampleRound_ct (M : Mont) (K : Kernel) (len : Nat) :
    RelCT isa (Two (SampleRoundBefore len))
      (Impl.Dsa.X86_64.Generation.sampleRound M.mm K.run) (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Generation.sampleRound
  refine RelCT.seq (two_post (two_map id (fun _ _ h => h.1) (sampleWitness_ct len))
    (fun _ _ h => sampleRound_ready h)) ?_
  refine RelCT.seq (two_post
    (two_map SamplePublic.round (fun _ _ h => h) (witnessRound_ct M K))
    (fun _ _ h => roundTail_ready M K h)) ?_
  exact two_map (fun p : SamplePublic => roundTailPublic p.round) (fun _ _ h => h) roundTail_ct

end VG.Proof.Dsa.X86_64.Generation
