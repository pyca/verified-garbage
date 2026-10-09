import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFlagsSemantic
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPrefix

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlDsa.Sample

/-- Parsing complete: this predicate does not require the optional sixth block to exist. -/
structure Done (v : Nat) (σ s : State) : Prop where
  env : Env v σ s
  length : ∀k<v,(prefixRow σ k 1008).length≤256
  counts : ∀k<v,(s.mem.readW (countP σ k) 64).toNat=256-(prefixRow σ k 1008).length
  stored : ∀k<v,Stored s.mem (polyP σ k) (prefixRow σ k 1008)
  flags : Flags v (fun k => prefixRow σ k 1008) s

theorem prefixRow_full (σ : State) (k : Nat)
    (h : (prefixRow σ k 840).length=256) : prefixRow σ k 1008=prefixRow σ k 840 := by
  change rnFold [] (streamBytes σ k 0 (840+168))=prefixRow σ k 840
  rw [streamBytes_append,rnFold_append _ _ _ (by rw [streamBytes_length])]
  exact rnFold_full h _

theorem Rows.done {v blocks : Nat} {σ s : State}
    (h : Rows v blocks σ (fun k => prefixRow σ k 1008) s)
    (hf : Flags v (fun k => prefixRow σ k 1008) s) : Done v σ s :=
  ⟨h.env,h.length,h.counts,h.stored,hf⟩

theorem Rows.early_done {v : Nat} {σ s : State}
    (h : Rows v 5 σ (fun k => prefixRow σ k 840) s)
    (hf : Flags v (fun k => prefixRow σ k 840) s) (hz : s.gpr .x27=0#64) : Done v σ s := by
  have hfull := hf.zero.mp hz
  have he (k : Nat) (hk : k<v) : prefixRow σ k 1008=prefixRow σ k 840 :=
    prefixRow_full σ k (hfull k hk)
  refine ⟨h.env,?_,?_,?_,hf.bound,?_⟩
  · intro k hk; rw [he k hk]; exact h.length k hk
  · intro k hk; rw [he k hk]; exact h.counts k hk
  · intro k hk; rw [he k hk]; exact h.stored k hk
  · constructor
    · intro _ k hk; rw [he k hk]; exact hfull k hk
    · intro _; exact hz

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
