import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFlags
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFlagValue
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPrefix

/-! ## From `ResidentRejFlagsSemantic.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Spec.MlDsa (Zq)

structure Flags (v : Nat) (L : Nat → List Zq) (s : State) : Prop where
  bound : (s.gpr .x27).toNat<512
  zero : s.gpr .x27=0#64 ↔ ∀k<v,(L k).length=256

theorem flagsSemantic_ok {v blocks : Nat} {σ s : State} {L : Nat → List Zq}
    (hp : Pre v σ) (h : Rows v blocks σ L s) :
    WP isa (.block (flagsCode (v-1))) s fun t => Rows v blocks σ L t ∧ Flags v L t := by
  refine WP.mono (flagsRows_ok hp h) fun t ⟨ht,hf⟩ => ⟨ht,?_,?_⟩
  · rw [hf]
    apply foldedFlags_bound
    intro k hk
    have hkv : k<v := by have:=hp.streams; omega
    rw [h.counts k hkv]
    omega
  · rw [hf,foldedFlags_zero]
    constructor
    · intro hz k hk
      have he := congrArg BitVec.toNat (hz k (by have:=hp.streams; omega))
      rw [h.counts k hk] at he
      have := h.length k hk
      change 256-(L k).length=0 at he
      omega
    · intro hz k hk
      have hkv : k<v := by have:=hp.streams; omega
      apply BitVec.eq_of_toNat_eq
      rw [h.counts k hkv,hz k hkv]
      rfl

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejDone.lean` -/

section

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

end
