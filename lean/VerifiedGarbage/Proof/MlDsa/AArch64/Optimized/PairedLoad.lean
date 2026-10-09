import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedProduct
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductLoad
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedShape

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_ldrq)
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase

/-- The common challenge vector remains resident while loading one secret
vector. This is the selected load-sharing optimization, without a reload. -/
theorem loaded_ok {d : VReg} (h30 : d≠.v30) (h31 : d≠.v31)
    {s : State} (hc : ProductConstants s) {off : Nat}
    (ho : off%16=0 ∧ off<4096*16)
    (hr : InRegions (s.rd++s.wr) (s.gpr .x14+BitVec.ofNat 64 off) 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀t,VChg [.v25,.v26,.v27,.v28,d] s t → ProductConstants t →
      (∀e<4,vword (t.v d) e=centeredProduct (vword (s.v .v24) e)
        (vword (s.mem.read (s.gpr .x14+BitVec.ofNat 64 off) 16) e)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (.ldrq .v25 .x14 off::productCentered d++rest)) s Q := by
  refine wp_ldrq ho rfl hr fun a ha => ?_
  have ca := hc.chg ha.chg (by decide) (by decide)
  refine productCentered_ok h31 ca.qv ca.qiv fun t ht hv => ?_
  have h : VChg [.v25,.v26,.v27,.v28,d] s t := (ha.chg.trans ht).mono (by
    intro r hr
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
    grind only)
  refine k t h (hc.chg h (by simp [Ne.symm h30]) (by simp [Ne.symm h31])) ?_
  intro e he
  rw [hv e he,ha.get .v24,ha.v]


theorem product_ok (j : Fin 8) {s : State} (hc : ProductConstants s)
    (hr : InRegions (s.rd++s.wr) (s.gpr .x13+BitVec.ofNat 64 (16*j.val)) 16)
    (hs : ∀p<2,InRegions (s.rd++s.wr) (s.gpr .x14+BitVec.ofNat 64 (1024*p+16*j.val)) 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀t,VChg [.v24,.v25,.v26,.v27,.v28,vr j.val,vr (8+j.val)] s t → ProductConstants t →
      (∀p<2,∀e<4,vword (t.v (vr (8*p+j.val))) e=centeredProduct
        (vword (s.mem.read (s.gpr .x13+BitVec.ofNat 64 (16*j.val)) 16) e)
        (vword (s.mem.read (s.gpr .x14+BitVec.ofNat 64 (1024*p+16*j.val)) 16) e)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (product j.val++rest)) s Q := by
  have safe : vr j.val≠vr (8+j.val) ∧
      vr j.val∉([.v24,.v25,.v26,.v27,.v28,.v30,.v31] : List VReg) ∧
      vr (8+j.val)∉([.v24,.v25,.v26,.v27,.v28,.v30,.v31] : List VReg) := by
    exact (show ∀j:Fin 8,vr j.val≠vr (8+j.val) ∧
      vr j.val∉([.v24,.v25,.v26,.v27,.v28,.v30,.v31] : List VReg) ∧
      vr (8+j.val)∉([.v24,.v25,.v26,.v27,.v28,.v30,.v31] : List VReg) by decide) j
  have d0 : vr j.val≠.v30 ∧ vr j.val≠.v31 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at safe
    grind only
  have d1 : vr (8+j.val)≠.v30 ∧ vr (8+j.val)≠.v31 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at safe
    grind only
  simp only [product,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.cons_append,List.nil_append,
    Nat.mul_zero,Nat.zero_add,Nat.mul_one,List.append_assoc]
  refine wp_ldrq (by omega) rfl hr fun a ha => ?_
  refine loaded_ok d0.1 d0.2 (hc.chg ha.chg (by decide) (by decide)) (by omega) ?_ fun b hb cb vb => ?_
  · rw [ha.chg.rd,ha.chg.wr,ha.chg.gpr]
    simpa using hs 0 (by decide)
  · refine loaded_ok d1.1 d1.2 cb (by omega) ?_ fun t ht ct vt => ?_
    · rw [hb.rd,hb.wr,hb.gpr,ha.chg.rd,ha.chg.wr,ha.chg.gpr]
      simpa using hs 1 (by decide)
    · refine k t (((ha.chg.trans hb).trans ht).mono ?_) ct ?_
      · intro r hr
        simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
        grind only
      · intro p hp e he
        have h0 : vr j.val∉[.v25,.v26,.v27,.v28,vr (8+j.val)] := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at *
          grind only
        have h24 : VReg.v24∉[.v25,.v26,.v27,.v28,vr j.val] := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at *
          grind only
        rcases (show p=0 ∨ p=1 by omega) with rfl | rfl
        · simp only [Nat.mul_zero,Nat.zero_add]
          rw [ht.get _ h0,vb e he,ha.v,ha.chg.mem,ha.chg.gpr]
        · simp only [Nat.mul_one]
          rw [vt e he,hb.get .v24 h24,ha.v,hb.mem,hb.gpr,ha.chg.mem,ha.chg.gpr]

end VG.Proof.MlDsa.AArch64.Optimized.Paired
