import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedState

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_ldrq)
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase

/-- Read only the selected pair of immutable root vectors. -/
theorem rootLoads_ok (off : Nat) (ha : off%16=0) (hi : off+16<65536)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (hr : InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hb : InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 (off+16)) 16)
    (k : ∀t,VChg [.v28,.v29] s t →
      t.v .v28=s.mem.read (s.gpr .x1+BitVec.ofNat 64 off) 16 →
      t.v .v29=s.mem.read (s.gpr .x1+BitVec.ofNat 64 (off+16)) 16 → WP isa (.block rest) t Q) :
    WP isa (.block (rootPair off++rest)) s Q := by
  refine wp_ldrq (by omega) rfl hr fun a h₁ => ?_
  refine wp_ldrq (by omega) rfl ?_ fun t h₂ => ?_
  · simpa only [h₁.rd,h₁.wr,h₁.gpr] using hb
  · refine k t (h₁.chg.trans h₂.chg) ?_ ?_
    · rw [h₂.get .v28,h₁.v]
    · rw [h₂.v,h₁.mem,h₁.gpr]

theorem Banks.roots {s t : State} {v : Values} (h : Banks s v)
    (hc : VChg [.v28,.v29] s t) : Banks t v := by
  intro p j
  rw [hc.get _ ?_,h p j]
  have hs := bank_safe (j := 8*p.val+j.val) (by omega)
  simp only [bankRegs,Vector.getElem_ofFn,List.mem_cons,List.not_mem_nil,or_false] at *
  grind only

end VG.Proof.MlDsa.AArch64.Optimized.Paired
