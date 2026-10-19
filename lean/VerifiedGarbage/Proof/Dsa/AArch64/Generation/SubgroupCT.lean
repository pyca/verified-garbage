module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SubgroupReadyCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.WorkspaceBaseCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Constant time of subgroup hashing, shaping and native primality testing -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MillerRabin.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.Dsa.AArch64.Generation
open VG.Impl.Bignum.AArch64 (seqs)

def SubgroupSized (len : Nat) (p : SubgroupPublic) (s : State) : Prop :=
  SubgroupBefore p s ∧ p.plan.prime.len = len

def SubgroupWorkspace (len : Nat) (p : SubgroupPublic) (s : State) : Prop :=
  WorkspaceBefore p.call s ∧ p.plan.prime.len = len

theorem subgroupCandidate_ct (H : GenerationHashes) (len : Nat) :
    RelCT isa (Two (SubgroupSized len)) (qCandidate H.sha1 H.sha256) (Two (SubgroupWorkspace len)) := by
  refine two_post (two_map SubgroupPublic.hash (fun _ _ h => subgroup_hash h.1)
    (qCandidate_ct H)) ?_
  intro p s h
  exact WP.mono (subgroup_candidate_ready H h.1) fun _ ht => ⟨ht, h.2⟩

theorem subgroupWorkspace_ct (len : Nat) :
    RelCT isa (Two (SubgroupWorkspace len)) (.block workspaceBase)
      (Two (CheckPrimeBefore 4 Impl.Dsa.Generation.Layout.q len (if len = 20 then 24 else 32) 64)) := by
  have ct : RelCT isa (Two (SubgroupWorkspace len)) (.block workspaceBase)
      (Two (fun (p : SubgroupPublic) s => WorkspaceReady p.call s ∧ p.plan.prime.len = len)) := by
    refine two_post ((two_map SubgroupPublic.call (fun _ _ h => h.1) workspaceBase_ct).mono
      (fun _ _ h => h) (fun _ _ _ => True.intro)) ?_
    intro p s h
    exact WP.mono (workspaceBase_ready h.1) fun _ ht => ⟨ht, h.2⟩
  apply ct.mono (fun _ _ h => h)
  intro s t h
  obtain ⟨p, hs, ht, hsp⟩ := h
  have convert : ∀ u, WorkspaceReady p.call u ∧ p.plan.prime.len = len →
      CheckPrimeBefore 4 Impl.Dsa.Generation.Layout.q len (if len = 20 then 24 else 32) 64 p.call u := by
    intro u hu
    exact ⟨hu.1.1.1, hu.1.1.2, hu.1.2, p.plan.words, rfl, hu.2,
      p.plan.draw.trans (by rw [hu.2]), p.plan.checks⟩
  exact ⟨p.call, convert s hs, convert t ht, hsp⟩

theorem subgroup_ct (H : GenerationHashes) (M : Mont) (K : Kernel)
    (len : Nat) (hlen : len = 20 ∨ len = 32) :
    RelCT isa (Two (SubgroupSized len)) (subgroup H.sha1 H.sha256 M.mm K.run len)
      (fun _ _ => True) := by
  unfold subgroup
  simp only [seqs]
  refine RelCT.seq (subgroupCandidate_ct H len)
    (RelCT.seq (subgroupWorkspace_ct len) ?_)
  apply primeCall_ct M K
  rcases hlen with rfl | rfl
  · exact Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩)

end VG.Proof.Dsa.AArch64.Generation
