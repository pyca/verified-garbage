import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductBank
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFiveSlice
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductBankField
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseStaticCore

/-! ## From `ProductFive.lean` -/

section

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

end

/-! ## From `ProductPassMemory.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

def productValues (m : Mem) (a b : Addr) (u : Nat) : Vector (BitVec 128) 8 :=
  Vector.ofFn fun j => ofVWords
    (centeredProduct (coeffAt m a (32*u+4*j.val)) (coeffAt m b (32*u+4*j.val)))
    (centeredProduct (coeffAt m a (32*u+4*j.val+1)) (coeffAt m b (32*u+4*j.val+1)))
    (centeredProduct (coeffAt m a (32*u+4*j.val+2)) (coeffAt m b (32*u+4*j.val+2)))
    (centeredProduct (coeffAt m a (32*u+4*j.val+3)) (coeffAt m b (32*u+4*j.val+3)))

theorem productValues_word (m : Mem) (a b : Addr) (u : Nat) (j : Fin 8) {e : Nat} (he : e<4) :
    vword (productValues m a b u)[j.val] e=
      centeredProduct (coeffAt m a (32*u+4*j.val+e)) (coeffAt m b (32*u+4*j.val+e)) := by
  simp only [productValues,Vector.getElem_ofFn]
  rw [VG.Proof.MlKem.AArch64.vword_ofVWords _ _ _ _ he]
  have h : e=0 ∨ e=1 ∨ e=2 ∨ e=3 := by omega
  rcases h with rfl | rfl | rfl | rfl <;> rfl

def productPassMem (m : Mem) (p a b : Addr) : Nat → Mem
  | 0 => m
  | u+1 => writeBank (fiveValues u (productValues m a b u)) (p+BitVec.ofNat 64 (128*u)) 16 (productPassMem m p a b u)

theorem productPass_frame {m : Mem} {p a b : Addr} {u : Nat} (hu : u≤8) :
    Frame [outputRegion p] m (productPassMem m p a b u) := by
  induction u with
  | zero => exact Frame.refl _ _
  | succ u ih =>
    simp only [productPassMem]
    apply writeBank_frame _ _ _ (r := outputRegion p) (by simp) ?_ (ih (by omega))
    intro i
    rw [BitVec.add_assoc,← BitVec.ofNat_add]
    exact Offset.contains_base p (by omega) (by omega)

theorem productValues_input {m : Mem} {s : State} {p a b : Addr} {u : Nat} (hu : u<8)
    (hm : Frame [outputRegion p] m s.mem)
    (ha : (polyRegion a).Disjoint (outputRegion p)) (hb : (polyRegion b).Disjoint (outputRegion p))
    (h13 : s.gpr .x13=a+BitVec.ofNat 64 (128*u))
    (h14 : s.gpr .x14=b+BitVec.ofNat 64 (128*u))
    (j : Fin 8) {e : Nat} (he : e<4) :
    vword (productValues m a b u)[j.val] e=productInput s (16*j.val) e := by
  rw [productValues_word _ _ _ _ _ he,productInput_offset h13 h14 he]
  have hi : 32*u+4*j.val+e<n := by change 32*u+4*j.val+e<256; omega
  rw [coeffAt_frame hm (by intro r hr; have h := List.mem_singleton.mp hr; subst r; exact ha) hi,
    coeffAt_frame hm (by intro r hr; have h := List.mem_singleton.mp hr; subst r; exact hb) hi]

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end
