import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductBank
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFiveSlice

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg VMem)
open VG.Impl.MlDsa.AArch64.Optimized (inverseProductLoads)

/-- Raw product loads feed the inverse directly in registers. -/
def productFiveCode : List Instr := inverseProductLoads ++ fiveCode ++ firstStores

theorem productFive_ok (u : Nat) {s : State} {v : Vector (BitVec 128) 8}
    (hv : ∀ j : Fin 8, ∀ e<4, vword v[j.val] e=productInput s (16*j.val) e)
    (hc : ProductConstants s)
    (hp : PackedRoots s (packedRoot u)) (hl : TableRoots localOffset (localRoot u) s)
    (hr : ∀ j<8, InRegions (s.rd++s.wr) (s.gpr .x13+BitVec.ofNat 64 (16*j)) 16 ∧
      InRegions (s.rd++s.wr) (s.gpr .x14+BitVec.ofNat 64 (16*j)) 16)
    (hw : ∀ i : Fin 8, InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 (16*i.val)) 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, (∃ mid, VChg runRegs s mid ∧ VMem mid t
      (writeBank (fiveValues u v) (s.gpr .x0) 16 s.mem)) → WP isa (.block rest) t Q) :
    WP isa (.block (productFiveCode ++ rest)) s Q := by
  simp only [productFiveCode,List.append_assoc]
  refine inverseProductLoads_ok hc hr fun s₁ hc₁ _ hv₁ => ?_
  have hc₁' : VChg runRegs s s₁ := hc₁.mono (by decide)
  have hb : Bank s₁ (regs 0) v := by
    intro i
    apply vec_ext
    intro e he
    have hr : (regs 0)[i.val]=VG.Impl.MlDsa.AArch64.Optimized.Inverse.vr i.val := by
      decide +revert +kernel
    rw [hr,hv₁ i.val i.isLt e he,hv i e he]
  refine five_ok u hb (hp.frame (hc₁.mono (by decide))) (hl.frame hc₁' (by decide)) fun s₂ hc₂ hb₂ => ?_
  rw [firstStores_eq]
  refine storeBank_ok (regs 7) 16 .x0 (by intro i; omega) hb₂ ?_ fun t hm => ?_
  · intro i
    simpa only [hc₂.wr,hc₂.gpr,hc₁.wr,hc₁.gpr] using hw i
  · refine k t ⟨s₂,(hc₁'.trans hc₂).mono (by simp),?_⟩
    simpa only [hc₂.mem,hc₂.gpr,hc₁.mem,hc₁.gpr] using hm

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
