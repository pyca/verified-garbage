module

import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Framework.Mem
public import Init.Prelude
public import VerifiedGarbage.Proof.Mont.Words32

/-! Two adjacent quotient stores extend a previously written prefix. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm

theorem pair_memory {mem mem' : Mem} {base : Addr} {size o i : Nat} {lo hi : BitVec 32}
    (nowrap : base.toNat+size≤2^32) (fit : o+4*(i+2)≤size)
    (hm : mem'=(mem.writeW (off base (o+4*i)) lo).writeW (off base (o+4*i+4)) hi) :
    Outside base (o+4*i) 8 mem mem' ∧
      val32 mem' base o (i+2)=val32 mem base o i+2^(32*i)*(lo.toNat+2^32*hi.toNat) := by
  have w0 := writeW32_outside mem base (d:=o+4*i) lo (by omega)
  have w1 := writeW32_outside (mem.writeW (off base (o+4*i)) lo)
    base (d:=o+4*i+4) hi (by omega)
  rw [←hm] at w1
  have outside : Outside base (o+4*i) 8 mem mem' :=
    (w0.mono (by omega) (by omega)).trans (w1.mono (by omega) (by omega))
  have low := outside.val32 (d:=o) (k:=i) (by omega) (by omega)
  have top0 : w32 mem' base (o+4*i)=lo.toNat := by
    rw [hm,w32_write_ne nowrap (by omega) (by omega) (by omega),w32_write_self]
  have top1 : w32 mem' base (o+4*i+4)=hi.toNat := by rw [hm,w32_write_self]
  refine ⟨outside,?_⟩
  rw [val32_append mem' base o i 2,low,val32,val32,val32,top0,top1,Nat.mul_zero,Nat.add_zero]

end VG.Proof.Bignum.Arm.Fios
