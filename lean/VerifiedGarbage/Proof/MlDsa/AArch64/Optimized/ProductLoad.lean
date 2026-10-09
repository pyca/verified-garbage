import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductVec

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64 (VChg wp_ldrq)
open VG.Proof.MlDsa.Arith
open VG.Impl.MlDsa.AArch64.Optimized

structure ProductConstants (s : State) : Prop where
  qv : s.v .v31 = ofVWords (BitVec.ofNat 32 q) (BitVec.ofNat 32 q)
    (BitVec.ofNat 32 q) (BitVec.ofNat 32 q)
  qiv : s.v .v30 = ofVWords (BitVec.ofNat 32 montQInv) (BitVec.ofNat 32 montQInv)
    (BitVec.ofNat 32 montQInv) (BitVec.ofNat 32 montQInv)

theorem ProductConstants.chg {s t : State} (h : ProductConstants s)
    {rs : List VReg} (k : VChg rs s t) (h30 : VReg.v30 ∉ rs) (h31 : VReg.v31 ∉ rs) :
    ProductConstants t := ⟨by rw [k.get _ h31]; exact h.qv, by rw [k.get _ h30]; exact h.qiv⟩

/-- The two loads and exact selected product preserve all memory, pointer
registers, and constants; output lanes refer to the original input buffers. -/
theorem productLoad_ok {d : VReg} (h30 : d ≠ .v30) (h31 : d ≠ .v31)
    {s : State} (hc : ProductConstants s) {off : Nat}
    (ho : off%16=0 ∧ off<4096*16)
    (ha : InRegions (s.rd++s.wr) (s.gpr .x13+BitVec.ofNat 64 off) 16)
    (hb : InRegions (s.rd++s.wr) (s.gpr .x14+BitVec.ofNat 64 off) 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, VChg [.v16,.v17,.v18,.v19,.v20,d] s t → ProductConstants t →
      (∀ e<4, vword (t.v d) e = centeredProduct
        (vword (s.mem.read (s.gpr .x13+BitVec.ofNat 64 off) 16) e)
        (vword (s.mem.read (s.gpr .x14+BitVec.ofNat 64 off) 16) e)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (productLoad d off ++ rest)) s Q := by
  unfold productLoad
  simp only [List.cons_append, List.nil_append]
  refine wp_ldrq ho rfl ha fun a h1 => ?_
  have hb' : InRegions (a.rd++a.wr) (a.gpr .x14+BitVec.ofNat 64 off) 16 := by
    rw [h1.chg.rd,h1.chg.wr,h1.chg.gpr]; exact hb
  refine wp_ldrq ho rfl hb' fun b h2 => ?_
  have cb := (hc.chg h1.chg (by decide) (by decide)).chg h2.chg (by decide) (by decide)
  refine productCentered_ok h31 cb.qv cb.qiv fun t ht hv => ?_
  have h : VChg [.v16,.v17,.v18,.v19,.v20,d] s t :=
    ((h1.chg.trans h2.chg).trans ht).mono (by
      intro r hr
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
      grind only)
  refine k t h (hc.chg h (by simp [Ne.symm h30]) (by simp [Ne.symm h31])) ?_
  intro e he
  rw [hv e he,h2.get .v16,h1.v,h2.v,h1.chg.mem,h1.chg.gpr]

end VG.Proof.MlDsa.AArch64.Optimized
