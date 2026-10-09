import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFinalSource
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductMemory

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith

theorem valuesAt_word (m : Mem) (a b : Addr) (poly : Fin 2) (j : Fin 8) {e : Nat} (he : e<4) :
    vword ((valuesAt m a b poly)[j.val]) e=centeredProduct
      (vword (m.read (a+BitVec.ofNat 64 (16*j.val)) 16) e)
      (vword (m.read (b+BitVec.ofNat 64 (1024*poly.val+16*j.val)) 16) e) := by
  simp only [valuesAt,Vector.getElem_ofFn]
  rcases (show e=0 ∨ e=1 ∨ e=2 ∨ e=3 by omega) with rfl | rfl | rfl | rfl <;> simp only [vword_ofVWords_0,vword_ofVWords_1,vword_ofVWords_2,vword_ofVWords_3]

/-- The paired SIMD layout contains the same pointwise products as the scalar polynomial view. -/
theorem valuesAt_coeff (m : Mem) (a b : Addr) (u : Nat) (poly : Fin 2) (j : Fin 8)
    {e : Nat} (he : e<4) :
    vword ((valuesAt m (a+BitVec.ofNat 64 (128*u)) (b+BitVec.ofNat 64 (128*u)) poly)[j.val]) e=
      centeredProduct (coeffAt m a (32*u+4*j.val+e))
        (coeffAt m (b+BitVec.ofNat 64 (1024*poly.val)) (32*u+4*j.val+e)) := by
  rw [valuesAt_word _ _ _ _ _ he,VG.Proof.MlDsa.AArch64.Arith.Neon.vword_read16 _ _ he,VG.Proof.MlDsa.AArch64.Arith.Neon.vword_read16 _ _ he]
  simp only [coeffAt,BitVec.add_assoc,←BitVec.ofNat_add]
  rw [show 128*u+16*j.val+4*e=4*(32*u+4*j.val+e) by omega,
    show 128*u+(1024*poly.val+16*j.val)+4*e=1024*poly.val+4*(32*u+4*j.val+e) by omega]

theorem valuesAt_bounds {m : Mem} {a b : Addr} {u : Nat} {poly : Fin 2} {f g : Poly}
    (hu : u<8) (hf : PosPolyIs m a f) (hg : PosPolyIs m (b+BitVec.ofNat 64 (1024*poly.val)) g)
    (j : Fin 8) {e : Nat} (he : e<4) :
    -(q : Int)≤(vword ((valuesAt m (a+BitVec.ofNat 64 (128*u)) (b+BitVec.ofNat 64 (128*u)) poly)[j.val]) e).toInt ∧
    (vword ((valuesAt m (a+BitVec.ofNat 64 (128*u)) (b+BitVec.ofNat 64 (128*u)) poly)[j.val]) e).toInt≤147168 := by
  rw [valuesAt_coeff _ _ _ _ _ _ he]
  exact centeredProduct_bounds _ _ (hf.bound _ (by change 32*u+4*j.val+e<256; omega))
    (hg.bound _ (by change 32*u+4*j.val+e<256; omega))

theorem valuesAt_scaled {m : Mem} {a b : Addr} {u : Nat} {poly : Fin 2} {f g : Poly}
    (hu : u<8) (hf : PosPolyIs m a f) (hg : PosPolyIs m (b+BitVec.ofNat 64 (1024*poly.val)) g)
    (j : Fin 8) {e : Nat} (he : e<4) :
    ofInt (vword ((valuesAt m (a+BitVec.ofNat 64 (128*u)) (b+BitVec.ofNat 64 (128*u)) poly)[j.val]) e).toInt * ofInt 4294967296=
      f[32*u+4*j.val+e]! * g[32*u+4*j.val+e]! := by
  have hi : 32*u+4*j.val+e<n := by change 32*u+4*j.val+e<256; omega
  rw [valuesAt_coeff _ _ _ _ _ _ he,
    centeredProduct_scaled _ _ (hf.bound _ hi) (hg.bound _ hi),
    ofInt_nat_eq,ofInt_nat_eq,←polyAt_get _ _ hi,←polyAt_get _ _ hi,hf.value,hg.value]
end VG.Proof.MlDsa.AArch64.Optimized.Paired
