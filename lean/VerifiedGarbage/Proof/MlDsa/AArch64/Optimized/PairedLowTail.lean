import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowStore

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Response (StepKeep)

/-- Exact two-store suffix, including its accumulated rejection mask. -/
theorem lowTail_ok {a t h : VReg} {off : Nat}
    (hat : a≠t) (haq : a≠.v31) (hac : a≠.v8) (htq : t≠.v31)
    (hconst : ∀r∈[.v9,.v10,.v30],r∉[a,t])
    (hpres : ∀r∈preservedV,r∉[a,t,.v30])
    {s : State} {rest : List Instr} {Q : State → Prop}
    (ho : off%16=0 ∧ off<65536)
    (hr : InRegions s.wr (s.gpr .x15+BitVec.ofNat 64 off) 16)
    (hl : InRegions s.wr (s.gpr .x16+BitVec.ofNat 64 off) 16)
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v8) e=4194304#32)
    (k : ∀u low,StepKeep [a,t,.v30] s u →
      u.mem=(s.mem.write (s.gpr .x15+BitVec.ofNat 64 off) 16 (s.v h)).write
        (s.gpr .x16+BitVec.ofNat 64 off) 16 low →
      (∀e<4,vword low e=Response.reduceWord
        (vword (s.v a) e-vword (s.v h) e*vword (s.v .v15) e)) →
      (∀e<4,vword (u.v .v30) e=vword (s.v .v30) e |||
        Response.normMask (vword low e) (vword (s.v .v9) e) (vword (s.v .v10) e)) →
      WP isa (.block rest) u Q) :
    WP isa (.block (lowStoreMls a t h off++lowStoreNorm a t off++rest)) s Q := by
  rw [List.append_assoc]
  refine lowStoreMls_ok hat haq hac htq
    (by intro r hr hm; exact hpres r hr (by simp only [List.mem_cons,List.not_mem_nil,or_false] at *; grind only))
    ho hr hq hc fun u hu hm hw => ?_
  have h10 := hconst .v10 (by simp)
  have h30 := hconst .v30 (by simp)
  refine lowStoreNorm_ok
    (by intro he; subst t; exact h10 (by simp))
    (by intro he; subst t; exact h30 (by simp))
    (by intro r hr hm; exact hpres r hr (by simp only [List.mem_cons,List.not_mem_nil,or_false] at *; grind only))
    ho (by rw [hu.keep.wr,hu.keep.get .x16]; exact hl)
    fun v hv hmem hf => k v (u.v a) ((hu.trans hv).mono (by
      intro r hr; simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; grind only)) ?_ hw ?_
  · rw [hmem,hm,hu.keep.get .x16]
  · intro e he
    rw [hf e he,hu.vec .v30 h30,hu.vec .v9 (hconst .v9 (by simp)),hu.vec .v10 h10]
end VG.Proof.MlDsa.AArch64.Optimized.Paired
