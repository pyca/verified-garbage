import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.LazyBase
import VerifiedGarbage.Proof.MlDsa.Arith.LazyButterfly
import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Lazy

namespace VG.Proof.MlDsa.X86_64.Arith.Lazy
open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.Arith.Lazy
open VG.Proof.MlKem.X86_64 (XOnly)
open VG.Impl.MlKem.X86_64 (xb xmov)
open VG.Spec.MlDsa (q Zq)

theorem prod_lt {y z : BitVec 128} {f : Nat → Word} {ζ : Nat → Zq}
    (hy : DLanes y f) (hz : ZLanes z ζ) :
    ∀ i < 4, (dword y i).toNat * (dword z i).toNat < q * 2 ^ 32 := fun i hi => by
  rw [hy i hi, hz i hi]
  exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le (f i).isLt
    (Nat.le_of_lt (Nat.mod_lt _ (show 0 < q by decide))) (by decide)) (by decide)

theorem bfly_ok : VBflyOk lazyBfly op := by
  intro s hc x y ζ hx hy hz ho
  simp only [lazyBfly, vmont, vredc, xmov, xb, List.cons_append, List.nil_append]
  vrun [eval_movdqa]
  rw [hc.q, hc.qinv, hc.q2]
  have hm (i : Nat) (hi : i < 4) :
      (dword (montV (s.xmm .xmm1) (s.xmm .xmm13) (s.xmm .xmm12)) i).toNat = product (y i) (ζ i) := by
    rw [dword_montV ho (prod_lt hy hz) hi, hy i hi, hz i hi]; rfl
  refine ⟨?_, ?_, by xonly⟩
  · change DLanes (XBinOp.eval .paddd (s.xmm .xmm0)
      (montV (s.xmm .xmm1) (s.xmm .xmm13) (s.xmm .xmm12))) _
    intro i hi
    rw [dword_paddd _ _ hi, BitVec.toNat_add, hx i hi, hm i hi]
    simp only [op, Fin.val_add, Fin.val_ofNat, Nat.add_mod_mod]
  · change DLanes (XBinOp.eval .psubd
      (XBinOp.eval .paddd (s.xmm .xmm0) (ofDwords 16760834#32 16760834#32 16760834#32 16760834#32))
      (montV (s.xmm .xmm1) (s.xmm .xmm13) (s.xmm .xmm12))) _
    intro i hi
    have hq : (dword (ofDwords 16760834#32 16760834#32 16760834#32 16760834#32) i).toNat = 16760834 := by
      rcases cases4 hi with rfl | rfl | rfl | rfl <;> rfl
    rw [dword_psubd _ _ hi, BitVec.toNat_sub, dword_paddd _ _ hi, BitVec.toNat_add, hx i hi, hq, hm i hi]
    have ht := product_lt (y i) (ζ i)
    simp only [op, Fin.val_sub, Fin.val_add, Fin.val_ofNat,
      show (16760834 : Word).val = 16760834 from rfl]
    have ht32 : product (y i) (ζ i) < 4294967296 := by exact Nat.lt_trans ht (by decide)
    rw [Nat.mod_eq_of_lt ht32]

end VG.Proof.MlDsa.X86_64.Arith.Lazy
