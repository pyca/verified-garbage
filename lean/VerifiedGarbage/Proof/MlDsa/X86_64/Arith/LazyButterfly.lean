module

public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.LazyBase
public import VerifiedGarbage.Proof.MlDsa.Arith.LazyButterfly
public import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Lazy
public import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Montgomery
import VerifiedGarbage.Proof.Framework.Offset

@[expose] public section

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

/-- `128 q`, the bias of `vibflyLazy`, in each doubleword of xmm11. -/
abbrev bInvC : BitVec 32 := 1072693376#32

theorem bflyInv_ok : VBflyOkW bInvC vibflyLazy opInv := by
  intro s hc x y ζ hx hy hz ho
  simp only [vibflyLazy, vmont, vredc, xmov, xb, List.cons_append, List.nil_append]
  vrun [eval_movdqa]
  rw [hc.q, hc.qinv, hc.q2]
  have hw : DLanes (XBinOp.eval .paddd (XBinOp.eval .psubd (s.xmm .xmm1) (s.xmm .xmm0))
      (ofDwords bInvC bInvC bInvC bInvC)) (fun i => y i + 1072693376 - x i) := by
    intro i hi
    have hb : (dword (ofDwords bInvC bInvC bInvC bInvC) i).toNat = 1072693376 := by
      rcases cases4 hi with rfl | rfl | rfl | rfl <;> rfl
    rw [dword_paddd _ _ hi, BitVec.toNat_add, dword_psubd _ _ hi, BitVec.toNat_sub, hx i hi, hy i hi, hb]
    simp only [Fin.val_sub, Fin.val_add, show (1072693376 : Word).val = 1072693376 from rfl]
    have := (x i).isLt; have := (y i).isLt
    omega
  refine ⟨?_, ?_, by xonly⟩
  · change DLanes (XBinOp.eval .paddd (s.xmm .xmm0) (s.xmm .xmm1)) _
    intro i hi
    rw [dword_paddd _ _ hi, BitVec.toNat_add, hx i hi, hy i hi]
    simp only [opInv, Fin.val_add]
  · change DLanes (montV (XBinOp.eval .paddd (XBinOp.eval .psubd (s.xmm .xmm1) (s.xmm .xmm0))
      (ofDwords bInvC bInvC bInvC bInvC)) (s.xmm .xmm13) (s.xmm .xmm12)) _
    intro i hi
    rw [dword_montV ho (prod_lt hw hz) hi, hw i hi, hz i hi]
    have ht := product_lt (y i + 1072693376 - x i) (ζ i)
    have ht32 : product (y i + 1072693376 - x i) (ζ i) < 4294967296 := Nat.lt_trans ht (by decide)
    simp only [opInv, Fin.val_ofNat, Nat.mod_eq_of_lt ht32]
    rfl

end VG.Proof.MlDsa.X86_64.Arith.Lazy
