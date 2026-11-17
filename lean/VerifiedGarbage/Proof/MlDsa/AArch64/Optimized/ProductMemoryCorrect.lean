module

public import VerifiedGarbage.Proof.MlDsa.RawInverseContract
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Representation
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TraversalBank
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTraversal
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryBank
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseMemoryCorrect
public import VerifiedGarbage.Proof.MlDsa.Arith.Mem
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTraversalCorrect
public import VerifiedGarbage.Proof.MlDsa.Arith.Representation
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InnerBank
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductBank
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductBatch
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseStaticCore
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ProductBank
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.SliceFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseRawFinalSlice
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseCore
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic

/-! ### `MlDsa.AArch64.Optimized.InverseRawFinalLoop`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def rawFinalPassMem (m : Mem) (p : Addr) : Nat → Mem
  | 0 => m
  | u+1 => let prior := rawFinalPassMem m p u
           let base := p+BitVec.ofNat 64 (16*u)
           writeBank (rawFinalValues (readBank prior base 128)) base 128 prior

theorem rawFinalPass_frame {m : Mem} {p : Addr} {u : Nat} (hu : u≤8) :
    Frame [⟨p,1024⟩] m (rawFinalPassMem m p u) := by
  induction u with
  | zero => exact Frame.refl _ _
  | succ u ih =>
    simp only [rawFinalPassMem]
    apply writeBank_frame _ _ _ (r := ⟨p,1024⟩) (by simp) ?_ (ih (by omega_using [hu]))
    intro i
    rw [BitVec.add_assoc,← BitVec.ofNat_add]
    exact Offset.contains_base p (by omega_using [hu]) (by omega_using [hu])

theorem rawFinalLoop_ok {s : State} (hf : FinalRoots s) (hs : ScaleRoots s)
    (hc : s.gpr .x12=8)
    (hr : ∀ u<8, ∀ i : Fin 8, InRegions (s.rd++s.wr)
      ((s.gpr .x2+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (128*i.val)) 16)
    (hw : ∀ u<8, ∀ i : Fin 8, InRegions s.wr
      ((s.gpr .x2+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (128*i.val)) 16) :
    WP isa (.loop (.block (rawFinalSliceCode++finalAdvance)) (.nonzero .x .x12)) s fun t =>
      Keep [.x2,.x12] s t ∧ (∀ r∈finalConstants, t.v r=s.v r) ∧
      t.gpr .x2=s.gpr .x2+128 ∧ t.mem=rawFinalPassMem s.mem (s.gpr .x2) 8 := by
  let I := fun u t => Keep [.x2,.x12] s t ∧ (∀ r∈finalConstants, t.v r=s.v r) ∧
    t.gpr .x2=s.gpr .x2+BitVec.ofNat 64 (16*u) ∧
    t.mem=rawFinalPassMem s.mem (s.gpr .x2) u
  apply VG.Proof.MlDsa.AArch64.Arith.wp_countdown (N := 8) (by decide) (by decide) I ?_ ?_ hc
  · intro u hu t ht _
    rcases ht with ⟨hk,hv,hp,hm⟩
    have hft : FinalRoots t := by
      constructor
      · intro i
        rw [hv _ ((show ∀ i : Fin 7, finalRootReg i.val∈finalConstants by decide +kernel) i)]
        exact hf.root i
      · intro i
        rw [hv _ ((show ∀ i : Fin 7, finalRecipReg i.val∈finalConstants by decide +kernel) i)]
        exact hf.recip i
      · intro e he; rw [hv .v31 (by decide)]; exact hf.q e he
    have hst : ScaleRoots t := by simpa only [ScaleRoots,hv .v30 (by decide)] using hs
    refine rawFinalSlice_ok hft hst ?_ ?_ fun t₁ ⟨v,hvc,hvm⟩ => ?_
    · intro i; simpa only [hk.rd,hk.wr,hp] using hr u hu i
    · intro i; simpa only [hk.wr,hp] using hw u hu i
    · have hk₁ : Keep [] t t₁ := (hvc.keep.trans hvm.keep).mono
      refine WP.mono (finalAdvance_ok t₁) fun t₂ ⟨⟨⟨hp₂,hc₂,hm₂⟩,hk₂⟩,hv₂⟩ => ?_
      refine ⟨⟨((hk.trans hk₁).trans hk₂).mono,?_,?_,?_⟩,?_⟩
      · intro r hr
        rw [hv₂,hvm.v,hvc.get r ((show ∀ r∈finalConstants, r∉runRegs by decide) r hr)]
        exact hv r hr
      · rw [hp₂,hk₁.get .x2,hp]
        rw [show 16*(u+1)=16*u+16 by omega_using [],BitVec.ofNat_add,BitVec.add_assoc]
        rfl
      · rw [hm₂,hvm.mem]
        simp only [rawFinalSliceMem,hm,hp,rawFinalPassMem]
      · rw [hc₂,hk₁.get .x12]; rfl
  · exact ⟨Keep.refl _ _,fun _ _ => rfl,by simp,rfl⟩

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end

/-! ### `MlDsa.AArch64.Optimized.ProductMemoryField`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Optimized.ProductMemoryBankField`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Optimized.ProductPassMemory`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Optimized.ProductBankField`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith.Neon (vword_read16)

/-- Shifted input pointers select the corresponding global coefficient. -/
theorem productInput_offset {s : State} {a b : Addr} {u j e : Nat}
    (ha : s.gpr .x13=a+BitVec.ofNat 64 (128*u))
    (hb : s.gpr .x14=b+BitVec.ofNat 64 (128*u)) (he : e<4) :
    productInput s (16*j) e=centeredProduct
      (coeffAt s.mem a (32*u+4*j+e)) (coeffAt s.mem b (32*u+4*j+e)) := by
  unfold productInput
  rw [ha,hb,vword_read16 _ _ he,vword_read16 _ _ he]
  simp only [coeffAt,BitVec.add_assoc,← BitVec.ofNat_add]
  congr 3 <;> congr 1 <;> omega_using []

end VG.Proof.MlDsa.AArch64.Optimized

end

end


/-! ## From `ProductFive.lean` -/

@[expose] public section

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
  refine storeBank_ok (regs 7) 16 .x0 (by intro i; omega_using []) hb₂ ?_ fun t hm => ?_
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
  have h : e=0 ∨ e=1 ∨ e=2 ∨ e=3 := by omega_using [he]
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
    apply writeBank_frame _ _ _ (r := outputRegion p) (by simp) ?_ (ih (by omega_using [hu]))
    intro i
    rw [BitVec.add_assoc,← BitVec.ofNat_add]
    exact Offset.contains_base p (by omega_using [hu]) (by omega_using [hu])

theorem productValues_input {m : Mem} {s : State} {p a b : Addr} {u : Nat} (hu : u<8)
    (hm : Frame [outputRegion p] m s.mem)
    (ha : (polyRegion a).Disjoint (outputRegion p)) (hb : (polyRegion b).Disjoint (outputRegion p))
    (h13 : s.gpr .x13=a+BitVec.ofNat 64 (128*u))
    (h14 : s.gpr .x14=b+BitVec.ofNat 64 (128*u))
    (j : Fin 8) {e : Nat} (he : e<4) :
    vword (productValues m a b u)[j.val] e=productInput s (16*j.val) e := by
  rw [productValues_word _ _ _ _ _ he,productInput_offset h13 h14 he]
  have hi : 32*u+4*j.val+e<n := by change 32*u+4*j.val+e<256; omega_using [hu, he]
  rw [coeffAt_frame hm (by intro r hr; have h := List.mem_singleton.mp hr; subst r; exact ha) hi,
    coeffAt_frame hm (by intro r hr; have h := List.mem_singleton.mp hr; subst r; exact hb) hi]

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem productValues_bound {m : Mem} {a b : Addr} {f g : Poly}
    (hf : PosPolyIs m a f) (hg : PosPolyIs m b g) {u : Nat} (hu : u<8) :
    BankBound (productValues m a b u) 8380417 := by
  intro j e he
  rw [productValues_word _ _ _ _ _ he]
  have hi : 32*u+4*j.val+e<n := by change 32*u+4*j.val+e<256; omega_using [hu, he]
  have h := centeredProduct_bounds _ _ (hf.bound _ hi) (hg.bound _ hi)
  change -8380417≤_ ∧ _≤8380417
  change -8380417≤_ ∧ _≤147168 at h
  omega_using [h]

theorem productValues_field {m : Mem} {a b : Addr} {f g : Poly}
    (hf : PosPolyIs m a f) (hg : PosPolyIs m b g) {u : Nat} (hu : u<8) :
    InnerBankField u (productValues m a b u) (Representation.product true f g) := by
  intro j e he
  rw [productValues_word _ _ _ _ _ he]
  have hi : 32*u+4*j.val+e<n := by change 32*u+4*j.val+e<256; omega_using [hu, he]
  have hs := centeredProduct_scaled _ _ (hf.bound _ hi) (hg.bound _ hi)
  rw [ofInt_nat_eq,ofInt_nat_eq,← polyAt_get _ _ hi,← polyAt_get _ _ hi,hf.value,hg.value] at hs
  have hc : ofInt 4294967296 * montgomeryRInv = 1 := by decide +kernel
  have hv := congrArg (fun x : Zq => x * montgomeryRInv) hs
  rw [Fin.mul_assoc,hc,Fin.mul_one] at hv
  change _ = (Montgomery.scale montgomeryRInv (multiplyNTT f g))[32*u+4*j.val+e]!
  rw [Montgomery.scale_get,mul_get _ _ hi]
  exact hv

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end

/-! ## From `ProductMemoryValues.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

def productMemStep (initial current : Mem) (p a b : Addr) (u : Nat) : Mem :=
  writeBank (fiveValues u (productValues initial a b u)) (coeffAddr p (32*u)) 16 current

theorem productPassMem_step (m : Mem) (p a b : Addr) (u : Nat) :
    productPassMem m p a b (u+1)=productMemStep m (productPassMem m p a b u) p a b u := by
  simp only [productPassMem,productMemStep,coeffAddr,show 4*(32*u)=128*u by omega_using []]

theorem productMemStep_at (m current : Mem) (p a b : Addr) {u : Nat}
    (hu : u<8) (i : Fin 8) {e : Nat} (he : e<4) :
    coeffAt (productMemStep m current p a b u) p (32*u+4*i.val+e)=
      vword (fiveValues u (productValues m a b u))[i.val] e := by
  exact writeBank_coeff_at _ current p (start := 32*u) (step := 4) (by decide) (by omega_using [hu]) i he

theorem productMemStep_outside (m current : Mem) (p a b : Addr) {u k : Nat}
    (hu : u<8) (hk : k<n) (hout : k/32≠u) :
    coeffAt (productMemStep m current p a b u) p k=coeffAt current p k := by
  apply writeBank_coeff_outside (start := 32*u) (step := 4) _ current p (by omega_using [hu]) hk
  intro i; omega_using [hout]

theorem productPass_processed (m : Mem) (p a b : Addr) {u k : Nat}
    (hu : u≤8) (hk : k<n) (hp : k/32<u) :
    coeffAt (productPassMem m p a b u) p k=
      vword (fiveValues (k/32) (productValues m a b (k/32)))[k%32/4]! (k%4) := by
  induction u with
  | zero => omega
  | succ u ih =>
    rw [productPassMem_step]
    by_cases he : k/32=u
    · have hi : k%32/4<8 := by omega_using []
      have hidx : 32*u+4*(k%32/4)+k%4=k := by omega_using [he]
      have hx := productMemStep_at m (productPassMem m p a b u) p a b (by omega_using [hu] : u<8)
        ⟨k%32/4,hi⟩ (e := k%4) (by omega_using [])
      rw [hidx] at hx
      simpa only [he,getElem!_pos (fiveValues u (productValues m a b u)) (k%32/4) hi] using hx
    · rw [productMemStep_outside _ _ _ _ _ (by omega_using [hu]) hk he]
      exact ih (by omega_using [hu]) (by omega_using [hp, he])

theorem productPass_all_values (m : Mem) (p a b : Addr) {k : Nat} (hk : k<n) :
    coeffAt (productPassMem m p a b 8) p k=
      vword (fiveValues (k/32) (productValues m a b (k/32)))[k%32/4]! (k%4) :=
  productPass_processed m p a b (by decide) hk (by change k<256 at hk; omega_using [hk])

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `ProductMemoryField.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem local_coordinate (w : Poly) {k : Nat} (hk : k<n) :
    (InverseTraversal.run InverseTraversal.localSchedule w)[k]! =
      (InverseTraversal.run (InverseTraversal.localSlice (k/32)) w)[k]! := by
  exact InverseTraversal.prefix_selected InverseTraversal.localSlice (fun k => k/32) 8
    (fun u hu => InverseTraversal.local_supported ⟨u,hu⟩) w hk (by change k<256 at hk; omega_using [hk])

/-- Multiplication is fused into each local block's initial loads. The first
pass therefore needs neither a materialized product polynomial nor an
initialized destination. -/
theorem productPass_field {m : Mem} {p a b : Addr} {f g : Poly}
    (hf : PosPolyIs m a f) (hg : PosPolyIs m b g) :
    SignedPolyIs (productPassMem m p a b 8) p
      (InverseTraversal.run InverseTraversal.localSchedule (Representation.product true f g))
      (-268173344) 268173344 := by
  have bank (u : Nat) (hu : u<8) := fiveValues_field (productValues m a b u)
    (Representation.product true f g) hu (productValues_bound hf hg hu) (productValues_field hf hg hu)
  have lane (k : Nat) (hk : k<n) :
      -268173344≤(coeffAt (productPassMem m p a b 8) p k).toInt ∧
      (coeffAt (productPassMem m p a b 8) p k).toInt≤268173344 ∧
      ofInt (coeffAt (productPassMem m p a b 8) p k).toInt=
        (InverseTraversal.run InverseTraversal.localSchedule (Representation.product true f g))[k]! := by
    have hu : k/32<8 := by change k<256 at hk; omega_using [hk]
    have hi : k%32/4<8 := by omega_using []
    have he : k%4<4 := by omega_using []
    have hb := (bank _ hu).1 ⟨k%32/4,hi⟩ (k%4) he
    have hv := (bank _ hu).2 ⟨k%32/4,hi⟩ (k%4) he
    rw [productPass_all_values m p a b hk,getElem!_pos _ (k%32/4) hi]
    refine ⟨hb.1,hb.2,?_⟩
    have hidx : 32*(k/32)+4*(k%32/4)+k%4=k := by omega_using []
    simpa only [local_coordinate _ hk,Traversal.innerLoc,hidx] using hv
  exact ⟨fun k hk => ⟨(lane k hk).1,(lane k hk).2.1⟩,fun k hk => (lane k hk).2.2⟩

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end

end

/-! ### `MlDsa.AArch64.Optimized.InverseRawMemoryValues`, which only this module used -/

section

/-! ## From `InverseRawMemory.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

def rawFinalMemStep (m : Mem) (p : Addr) (u : Nat) : Mem :=
  writeBank (rawFinalValues (readBank m (coeffAddr p (4*u)) 128)) (coeffAddr p (4*u)) 128 m

theorem rawFinalPassMem_step (m : Mem) (p : Addr) (u : Nat) :
    rawFinalPassMem m p (u+1)=rawFinalMemStep (rawFinalPassMem m p u) p u := by
  simp only [rawFinalPassMem,rawFinalMemStep,coeffAddr,show 4*(4*u)=16*u by omega_using []]

theorem rawFinalMemStep_at (m : Mem) (p : Addr) {u : Nat}
    (hu : u<8) (i : Fin 8) {e : Nat} (he : e<4) :
    coeffAt (rawFinalMemStep m p u) p (4*u+32*i.val+e)=
      vword (rawFinalValues (readBank m (coeffAddr p (4*u)) 128))[i.val] e := by
  exact writeBank_coeff_at _ m p (start := 4*u) (step := 32) (by decide) (by omega_using [hu]) i he

theorem rawFinalMemStep_outside (m : Mem) (p : Addr) {u k : Nat}
    (hu : u<8) (hk : k<n) (hout : k%32/4≠u) :
    coeffAt (rawFinalMemStep m p u) p k=coeffAt m p k := by
  apply writeBank_coeff_outside (start := 4*u) (step := 32) _ m p (by omega_using [hu]) hk
  intro i; omega_using [hu, hout]

theorem rawFinalPass_untouched (m : Mem) (p : Addr) {u k : Nat}
    (hu : u≤8) (hk : k<n) (hbefore : u≤k%32/4) :
    coeffAt (rawFinalPassMem m p u) p k=coeffAt m p k := by
  induction u with
  | zero => rfl
  | succ u ih =>
    rw [rawFinalPassMem_step,rawFinalMemStep_outside _ _ (by omega_using [hu]) hk (by omega_using [hbefore])]
    exact ih (by omega_using [hu]) (by omega_using [hbefore])

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `InverseRawMemoryValues.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem rawFinalPass_bank_original (m : Mem) (p : Addr) {u : Nat} (hu : u<8) :
    readBank (rawFinalPassMem m p u) (coeffAddr p (4*u)) 128=
      readBank m (coeffAddr p (4*u)) 128 := by
  apply Vector.ext
  intro i hi
  apply vec_ext
  intro e he
  rw [readBank_coeff _ p (4*u) 32 ⟨i,hi⟩ he,readBank_coeff _ p (4*u) 32 ⟨i,hi⟩ he]
  exact rawFinalPass_untouched m p (by omega_using [hu]) (by change 4*u+32*i+e<256; omega_using [hu, hi, he]) (by omega_using [hu, he])

/-- A completed coefficient is the raw result of its own strided bank,
evaluated on the original pass input. -/
theorem rawFinalPass_processed (m : Mem) (p : Addr) {u k : Nat}
    (hu : u≤8) (hk : k<n) (hp : k%32/4<u) :
    coeffAt (rawFinalPassMem m p u) p k=
      vword (rawFinalValues (readBank m (coeffAddr p (4*(k%32/4))) 128))[k/32]! (k%4) := by
  induction u with
  | zero => omega
  | succ u ih =>
    rw [rawFinalPassMem_step]
    by_cases he : k%32/4=u
    · have hi : k/32<8 := by change k<256 at hk; omega_using [hk]
      have hidx : 4*u+32*(k/32)+k%4=k := by omega_using [he]
      have hx := rawFinalMemStep_at (rawFinalPassMem m p u) p (by omega_using [hu] : u<8)
        ⟨k/32,hi⟩ (e := k%4) (by omega_using [])
      rw [hidx,rawFinalPass_bank_original m p (by omega_using [hu])] at hx
      simpa only [he,getElem!_pos (rawFinalValues (readBank m (coeffAddr p (4*u)) 128)) (k/32) hi] using hx
    · rw [rawFinalMemStep_outside _ _ (by omega_using [hu]) hk he]
      exact ih (by omega_using [hu]) (by omega_using [hp, he])

theorem rawFinalPass_all_values (m : Mem) (p : Addr) {k : Nat} (hk : k<n) :
    coeffAt (rawFinalPassMem m p 8) p k=
      vword (rawFinalValues (readBank m (coeffAddr p (4*(k%32/4))) 128))[k/32]! (k%4) :=
  rawFinalPass_processed m p (by decide) hk (by omega_using [])

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end

end


/-! ## From `RawInverseField.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem signedPolyAt_get (m : Mem) (p : Addr) {i : Nat} (hi : i<n) :
    (signedPolyAt m p)[i]! =ofInt (coeffAt m p i).toInt := by
  rw [_root_.getElem!_pos (signedPolyAt m p) i hi]
  simp only [signedPolyAt,Vector.getElem_ofFn]

/-- Caller-facing form of the raw contract: strict bounds and exact field
values, without interpreting a negative coefficient as an unsigned integer. -/
theorem rawPolyIs_iff {m : Mem} {p : Addr} {f : Poly} :
    RawPolyIs m p f ↔ ∀ i<n,
      -(q : Int)<(coeffAt m p i).toInt ∧ (coeffAt m p i).toInt<2*(q : Int) ∧
      ofInt (coeffAt m p i).toInt=f[i]! := by
  constructor
  · rintro ⟨hb,hf⟩ i hi
    exact ⟨(hb i hi).1,(hb i hi).2,by rw [← signedPolyAt_get m p hi,hf]⟩
  · intro h
    refine ⟨fun i hi => ⟨(h i hi).1,(h i hi).2.1⟩,ext_getElem! fun i hi => ?_⟩
    rw [signedPolyAt_get m p hi]
    exact (h i hi).2.2

end VG.Proof.MlDsa.AArch64.Optimized

end

/-! ## From `InverseRawBankField.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- Omitting the final correction retains the exact field result in the
strict signed Barrett interval. -/
theorem rawFinalValues_field (v : Vector (BitVec 128) 8) (w : Poly)
    {u : Nat} (hu : u<8) (hv : BankBound v 268173344) (hf : BankField u v w)
    (i : Fin 8) {e : Nat} (he : e<4) :
    -8380417<(vword (rawFinalValues v)[i.val] e).toInt ∧
      (vword (rawFinalValues v)[i.val] e).toInt<2*8380417 ∧
      ofInt (vword (rawFinalValues v)[i.val] e).toInt=
        (InverseTraversal.run (InverseTraversal.stridedSlice u) w)[4*u+32*i.val+e]! * 16382 := by
  have hp := runValues_final_six 0 6 (by decide) v w hu
    ((stageBound_zero v 268173344).mpr hv) hf
  have hl := foldedStage_field _ _ hu hp.1 hp.2 i he
  rw [rawFinalValues,runValues_split_last]
  refine ⟨hl.1,hl.2.1,?_⟩
  simpa only [← InverseTraversal.run_append,stridedOps_eq hu,
    InverseTraversal.stridedLoc,show 32*i.val+4*u+e=4*u+32*i.val+e by omega_using [],
    show ofInt (16382 : Int)=(16382 : Zq) by decide +kernel] using hl.2.2

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `InverseRawMemoryField.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- Every signed final coefficient comes from its independent strided slice;
folded scaling preserves the ordinary field value and the strict raw range. -/
theorem rawFinalPass_field {m : Mem} {p : Addr} {w : Poly}
    (h : SignedPolyIs m p w (-268173344) 268173344) :
    RawPolyIs (rawFinalPassMem m p 8) p
      ((InverseTraversal.run InverseTraversal.stridedSchedule w).map (· * 16382)) := by
  have bank (u : Nat) (hu : u<8) := fun (i : Fin 8) (e : Nat) (he : e<4) =>
    rawFinalValues_field (readBank m (coeffAddr p (4*u)) 128) w hu
      (fun j e he => by
        rw [readBank_coeff m p (4*u) 32 j he]
        exact h.bound _ (by change 4*u+32*j.val+e<256; omega_using [hu, he]))
      (fun j e he => by
        rw [readBank_coeff m p (4*u) 32 j he]
        simpa only [Traversal.loc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using
          h.value (4*u+32*j.val+e) (by change 4*u+32*j.val+e<256; omega_using [hu, he])) i he
  apply rawPolyIs_iff.mpr
  intro k hk
  have hi : k/32<8 := by change k<256 at hk; omega_using [hk]
  have hu : k%32/4<8 := by omega_using []
  have he : k%4<4 := by omega_using []
  rw [rawFinalPass_all_values m p hk,getElem!_pos _ (k/32) hi]
  have hh := bank _ hu ⟨k/32,hi⟩ _ he
  refine ⟨hh.1,hh.2.1,?_⟩
  have hidx : 4*(k%32/4)+32*(k/32)+k%4=k := by omega_using []
  rw [hidx] at hh
  rw [map_mul_get _ _ hk,InverseTraversal.strided_coordinate w hk]
  exact hh.2.2

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `ProductMemoryCorrect.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- Centered Montgomery products and the folded inverse scale cancel exactly,
leaving the ordinary polynomial product required by callers. -/
theorem productRawInverse_field {m : Mem} {p a b : Addr} {f g : Poly}
    (hf : PosPolyIs m a f) (hg : PosPolyIs m b g) :
    RawPolyIs (rawFinalPassMem (productPassMem m p a b 8) p 8) p
      (nttInv (multiplyNTT f g)) := by
  have h := rawFinalPass_field (productPass_field (p := p) hf hg)
  rw [InverseTraversal.traversal_montgomery] at h
  change RawPolyIs _ _ (Representation.inverse true (Representation.product true f g)) at h
  simpa only [Representation.inverse_product] using h

theorem positiveReduced_is {m : Mem} {p : Addr} (h : PositiveReduced m p) :
    PosPolyIs m p (polyAt m p) := ⟨h,rfl⟩

/-- Direct instantiation from the shared raw helper's input predicates. -/
theorem productRawInverse_contract_field {m : Mem} {p a b : Addr}
    (ha : PositiveReduced m a) (hb : PositiveReduced m b) :
    RawPolyIs (rawFinalPassMem (productPassMem m p a b 8) p 8) p
      (nttInv (multiplyNTT (polyAt m a) (polyAt m b))) :=
  productRawInverse_field (positiveReduced_is ha) (positiveReduced_is hb)

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end
