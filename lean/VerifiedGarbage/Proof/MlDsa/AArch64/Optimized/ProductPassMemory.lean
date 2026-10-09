import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductFive
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductBankField
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseStaticCore

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
