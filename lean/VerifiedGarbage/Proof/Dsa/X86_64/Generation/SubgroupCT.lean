module

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SubgroupReadyCT
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Subgroup
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SubgroupCTState
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeCallCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.QBuildCT

/-! # Constant time of subgroup hashing, shaping and native primality testing -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.Dsa.X86_64.Generation

def SubgroupSized (n len : Nat) (p : SubgroupPublic) (s : State) : Prop :=
  SubgroupBefore n p s ∧ p.plan.prime.len = len

def SubgroupCall (len : Nat) (p : SubgroupPublic) (s : State) : Prop :=
  PrimeTestBefore (8 * p.plan.prime.len) p.primeCall s ∧ p.plan.prime.len = len

theorem subgroupCandidate_ct (H : GenerationHashes) (n : Nat) (hn : n = 2 ∨ n = 3) (len : Nat) :
    RelCT isa (Two (SubgroupSized n len)) (qCandidate H.sha1 H.sha256 len) (Two (SubgroupCall len)) := by
  refine two_post (two_map SubgroupPublic.hash (fun _ _ h => subgroup_hash h.1)
    (qCandidate_ct H n hn len)) ?_
  intro p s ⟨h, hl⟩
  subst hl
  exact WP.mono (subgroup_candidate_ready H h) fun _ ht => ⟨ht, rfl⟩

theorem subgroup_ct (H : GenerationHashes) (T : PrimeTest)
    (n : Nat) (hn : n = 2 ∨ n = 3) (len : Nat) (hlen : len = 20 ∨ len = 32) :
    RelCT isa (Two (SubgroupSized n len)) (subgroup H.sha1 H.sha256 T.run len)
      (fun _ _ => True) := by
  unfold subgroup
  refine RelCT.seq (subgroupCandidate_ct H n hn len) ?_
  refine (primeCall_ct T (bits := 8 * len) ?_).mono (fun s t ⟨p, ⟨hs, hl⟩, ⟨ht, _⟩⟩ => ?_) fun _ _ h => h
  · rcases hlen with rfl | rfl <;> unfold ProbablePrime.Supported <;> decide
  · subst hl
    exact ⟨p.primeCall, hs, ht⟩

end VG.Proof.Dsa.X86_64.Generation
