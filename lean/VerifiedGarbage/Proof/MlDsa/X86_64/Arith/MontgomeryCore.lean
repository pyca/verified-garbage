import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Montgomery
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YMul
import VerifiedGarbage.Spec.MlDsa.Montgomery

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.X86_64 (XOnly)
open VG.Impl.MlKem.X86_64 (xb xmov toY)
open VG.Spec.MlDsa (q Zq montgomeryRInv)

def montMulV (x y : BitVec 128) : BitVec 128 := csubV (montV x y (shufDwords y 0xF5))
def montMulAddV (x y z : BitVec 128) : BitVec 128 := csubV (XBinOp.eval .paddd (montMulV x y) z)

theorem mont_inverse (x : Nat) : mont x % q = x * 8265825 % q := by
  apply cancel_R
  rw [mont_mod, Nat.mul_assoc, Nat.mul_mod, show 8265825 * 2 ^ 32 % q = 1 by decide,
    Nat.mul_one, Nat.mod_mod]

theorem montMul_lane {x y : BitVec 128} {a b : Nat → Zq} (hx : DLanes x a) (hy : DLanes y b)
    {i : Nat} (hi : i < 4) : (dword (montMulV x y) i).toNat = (a i * b i * montgomeryRInv).val := by
  have hzo : ZOdd y (shufDwords y 0xF5) := fun j hj => by
    rw [dword_shufDwords _ _ (by omega)]
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> rfl
  have hb : ∀ i < 4, (dword x i).toNat * (dword y i).toNat < q * 2 ^ 32 := fun i hi => by
    rw [hx i hi, hy i hi]
    exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le (val_lt (a i)) (Nat.le_of_lt (val_lt (b i)))
      (by decide)) (by decide)
  rw [montMulV, dword_csubV _ hi, csubL_toNat (by rw [dword_montV hzo hb hi]; exact mont_lt (hb i hi)),
    dword_montV hzo hb hi, condSub_mont (hb i hi), mont_inverse, hx i hi, hy i hi,
    val_mul, val_mul, Nat.mod_mul_mod]
  rfl

theorem montMulAdd_lane {x y z : BitVec 128} {a b c : Nat → Zq}
    (hx : DLanes x a) (hy : DLanes y b) (hz : DLanes z c) {i : Nat} (hi : i < 4) :
    (dword (montMulAddV x y z) i).toNat = (c i + a i * b i * montgomeryRInv).val := by
  have hm := montMul_lane hx hy hi
  rw [montMulAddV, dword_csubV _ hi, dword_paddd _ _ hi, addD_toNat (by rw [hm]; exact val_lt _)
    (by rw [hz i hi]; exact val_lt _), hm, hz i hi, Nat.add_comm, ← val_add]

theorem montMulCore_ok {s : State} (hc : VConsts s) :
    WP isa (.block montMulCore) s fun s' =>
      s'.xmm .xmm3 = montMulV (s.xmm .xmm3) (s.xmm .xmm13) ∧ XOnly [.xmm12, .xmm3, .xmm2, .xmm4] s s' := by
  simp only [montMulCore, vmont, vredc, vcsub, vcadd, xmov, xb, List.cons_append, List.nil_append]
  vrun [eval_movdqa]
  rw [hc.q, hc.qinv]
  exact ⟨rfl, by xonly⟩

theorem montMulAddCore_ok {s : State} (hc : VConsts s) :
    WP isa (.block montMulAddCore) s fun s' =>
      s'.xmm .xmm3 = montMulAddV (s.xmm .xmm3) (s.xmm .xmm13) (s.xmm .xmm5) ∧
        XOnly [.xmm12, .xmm3, .xmm2, .xmm4] s s' := by
  simp only [montMulAddCore, montMulCore, vmont, vredc, vcsub, vcadd, xmov, xb, List.cons_append, List.nil_append]
  vrun [eval_movdqa]
  rw [hc.q, hc.qinv]
  exact ⟨rfl, by xonly⟩

theorem lane_montMulCore : laneSseBlock (toY montMulCore) = some montMulCore := by decide +kernel
theorem lane_montMulAddCore : laneSseBlock (toY montMulAddCore) = some montMulAddCore := by decide +kernel

end VG.Proof.MlDsa.X86_64.Arith
