module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPrefix
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejRows
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourFlags

import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFlagValue
/-! ## From `ResidentRejFlagsSemantic.lean` -/

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/ResidentRejFlags.lean`, which only this module imported.
section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Spec.MlDsa (Zq)
open VG.Proof.MlDsa.AArch64.Optimized.BoundedFour (foldedFlags flagStep flagsTailN_ok)

theorem Rows.of_control {v blocks : Nat} {σ s t : State} {L : Nat → List Zq} {rs : List Reg}
    (h : Rows v blocks σ L s) (ht : Only rs s t)
    (hregs : ∀r∈[Reg.x19,.x20,.x21,.x30],r∉rs) : Rows v blocks σ L t := by
  refine ⟨h.env.lowStep (rs := []) (by rw [ht.mem]; exact Frame.refl _ _) (by simp)
    ht.rd ht.wr ht.sp (fun r hr => ht.get r (hregs r hr)),h.blockBound,?_,?_,h.length,?_,?_⟩
  · simpa only [ht.mem] using h.pairs
  · simpa only [ht.mem] using h.bytes
  · simpa only [ht.mem] using h.counts
  · simpa only [ht.mem] using h.stored

def flagsCode (n : Nat) : List Instr :=
  .ldr .x .x27 .x19 7904::(List.range n).flatMap flagStep

theorem flagsRows_ok {v blocks : Nat} {σ s : State} {L : Nat → List Zq}
    (hp : Pre v σ) (h : Rows v blocks σ L s) :
    WP isa (.block (flagsCode (v-1))) s fun t => Rows v blocks σ L t ∧
      t.gpr .x27=foldedFlags (fun k => s.mem.readW (countP σ k) 64) (v-1) := by
  have hv : 0<v ∧ v≤4 := by have:=hp.streams; omega
  have hr (i : Nat) (hi : i<v) : InRegions (s.rd++s.wr) (countP σ i) 8 :=
    in_scr_rd hp h.env.wr (by unfold Impl.MlDsa.AArch64.Optimized.ResidentRej.counts; omega)
  unfold flagsCode
  refine wp_ldrx (a := countP σ 0) (by decide) (by rw [h.env.x19]; rfl)
    (hr 0 hv.1) fun a ha h27 => ?_
  refine WP.mono (flagsTailN_ok (n := v-1) (by omega) (s := a) (b := scr σ)
    (by rw [ha.get .x19]; exact h.env.x19)
    (C := fun k => s.mem.readW (countP σ k) 64)
    (fun i _ => by rw [ha.mem]; rfl) h27
    (fun i hi => by rw [ha.rd,ha.wr]; exact hr i (by omega))) fun t ⟨ht,he⟩ => ?_
  refine ⟨h.of_control ((ha.trans ht).mono (by decide :
    [Reg.x27]++[.x6,.x27] ⊆ [.x6,.x27])) ?_,he⟩
  intro r hrmem
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hrmem
  rcases hrmem with rfl | rfl | rfl | rfl <;> decide

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
end

end

@[expose] public section

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
