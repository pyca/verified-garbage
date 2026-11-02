module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SampleCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SampleCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.WitnessRound
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.WitnessRound
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RoundTailCT
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.SampleRound
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Kernel
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RoundTailCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeFrame
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeFrame
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Sample
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Sample
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMrRound

/-! Witness selection, the shared callable round, and its completion policy. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MillerRabin.AArch64

structure RoundPublic where
  prime : PrimeParams
  witness : Nat

def BeforeRound (p : RoundPublic) (s : State) : Prop :=
  ModulusReady s p.prime.B p.prime.Z p.prime.w p.prime.N ∧
    wv s.mem p.prime.B (slot p.prime.w aX) p.prime.w = p.witness

def SamplePublic.round (p : SamplePublic) : RoundPublic :=
  ⟨p.prime, (Spec.RsaKeyGen.witness (p.prime.N - 1) (Spec.Rsa.os2ip p.bytes)).1⟩

theorem sampleRound_ready {len : Nat} {p : SamplePublic} {s : State} (h : SampleSized len p s) :
    WP isa (Impl.Dsa.AArch64.Generation.sampleWitness len) s (BeforeRound p.round) := by
  rw [← h.2]
  exact WP.mono (sampleWitness_ok h.1 p.prime.exponentRoom p.prime.odd
    (by rw [p.length]; exact p.prime.len2)
    (by rw [p.length]; have := p.prime.lenDraw; have := p.prime.drawMax; omega)
    (by rw [p.length]; exact p.prime.lenWords) (by rw [p.length]; exact p.prime.predBits))
    (fun _ ⟨hr, hx, _, _, _⟩ => ⟨hr, hx⟩)

theorem witnessMont_ready (M : Mont) {p : RoundPublic} {s : State} (h : BeforeRound p s) :
    WP isa (M.mm aXm aX aR2) s (Caller.Before ⟨p.prime.B, p.prime.Z, p.prime.w⟩) := by
  refine WP.mono (witnessMont_ok M h.1 p.prime.exponentRoom p.prime.odd (by have := p.prime.n3; omega) h.2)
    fun t ⟨ht, hx, _, _⟩ => ?_
  refine ⟨p.prime.w4, p.prime.w128, p.prime.exponentRoom, p.prime.N,
    wv t.mem p.prime.B (slot p.prime.w aB) p.prime.w, p.witness,
    ⟨ht.ws, ht.inverse, ht.modulus, rfl, ht.r1, ht.rm1⟩, ht.exponent, p.prime.odd, p.prime.n3, ?_⟩
  simpa only [Nat.mod_mul_mod] using hx

theorem witnessRound_ct (M : Mont) (K : Kernel) :
    RelCT isa (Two BeforeRound) (Impl.Dsa.AArch64.Generation.witnessRound M.mm K.run) (fun _ _ => True) := by
  unfold Impl.Dsa.AArch64.Generation.witnessRound
  exact RelCT.seq (two_post
    (two_map (fun p : RoundPublic => (⟨p.prime.B, p.prime.Z, p.prime.w⟩ : VG.Proof.Bignum.AArch64.Ws))
      (fun _ _ h => ⟨_, h.1.ws.good⟩) (M.ct (o := aXm) (a := aX) (b := aR2) (by unfold MmUse; decide)))
    (fun _ _ h => witnessMont_ready M h))
    (two_map (fun p : RoundPublic => (⟨p.prime.B, p.prime.Z, p.prime.w⟩ : VG.Proof.Bignum.AArch64.Ws))
      (fun _ _ h => h) K.ct)

def roundTailPublic (p : RoundPublic) : RoundTailPublic :=
  ⟨p.prime, Proof.MillerRabin.Round.round p.prime.N p.witness⟩

theorem roundTail_ready (M : Mont) (K : Kernel) {p : RoundPublic} {s : State} (h : BeforeRound p s) :
    WP isa (Impl.Dsa.AArch64.Generation.witnessRound M.mm K.run) s (RoundTailState (roundTailPublic p)) :=
  WP.mono (witnessRound_ok M K h.1 p.prime.w4 p.prime.w128 p.prime.exponentRoom p.prime.odd p.prime.n3 h.2)
    (fun _ ⟨ht, flag, _, _⟩ => ⟨ht.ws, flag⟩)

theorem sampleRound_ct (M : Mont) (K : Kernel) (len : Nat) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x1])
      (.block (Impl.Dsa.AArch64.Generation.forceWitness len)) hc).isSome = true) :
    RelCT isa (Two (SampleSized len)) (Impl.Dsa.AArch64.Generation.sampleRound M.mm K.run len) (fun _ _ => True) := by
  unfold Impl.Dsa.AArch64.Generation.sampleRound
  refine RelCT.seq (two_post (sampleWitness_ct len ht) (fun _ _ h => sampleRound_ready h)) ?_
  exact RelCT.seq (two_post (two_map SamplePublic.round (fun _ _ h => h) (witnessRound_ct M K))
    (fun _ _ h => roundTail_ready M K h))
    (two_map (fun p : SamplePublic => roundTailPublic p.round) (fun _ _ h => h) roundTail_ct)

end VG.Proof.Dsa.AArch64.Generation
