module

public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Store the oldest pending product's cancelled low word. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.FiosPipelined
open VG VG.Proof.Mont VG.Proof.Bignum.Arm

theorem store_prefix {mem mem' : Mem} {base : Addr} {size acc i : Nat} {out : BitVec 32}
    (nowrap : base.toNat+size≤2^32) (fit : acc+4*(i+1)≤size)
    (memory : mem'=mem.writeW (off base (acc+4*i)) out) :
    Outside base (acc+4*i) 4 mem mem' ∧
    val32 mem' base acc (i+1)=val32 mem base acc i+2^(32*i)*out.toNat := by
  have outside := writeW32_outside mem base (d:=acc+4*i) out (by omega)
  rw [←memory] at outside
  have low := outside.val32 (d:=acc) (k:=i) (by omega) (by omega)
  have top : w32 mem' base (acc+4*i)=out.toNat := by rw [memory,w32_write_self]
  exact ⟨outside,by rw [val32_succ,low,top]⟩

end VG.Proof.Bignum.Arm.FiosPipelined
