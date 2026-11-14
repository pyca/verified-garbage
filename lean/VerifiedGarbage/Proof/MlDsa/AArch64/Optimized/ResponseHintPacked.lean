module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintFinish
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZInit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseAdd
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFinish

/-! ### `MlDsa.AArch64.Optimized.ResponseHintCount`, which only this module used -/

section

/-! ## From `ResponseHintSemantic.lean` -/

@[expose] public section

/-! ## From `ResponseHintCount.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64

theorem shift31_bound (x : BitVec 32) : (x >>> 31).toNat≤1 := by
  rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  have h := x.isLt
  change _<4294967296 at h
  change _/2147483648≤1
  omega_using []

/-- The final logical shift makes every hint a bit, even on rejected inputs. -/
theorem hintWord_bit (B t h : BitVec 32) : (hintWord B t h).toNat≤1 :=
  shift31_bound _

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

end

end


@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64

theorem packedWords_nat (lo hi : BitVec 32) :
    (lo.setWidth 64 ||| (hi.setWidth 64 <<< 32)).toNat=lo.toNat+hi.toNat*4294967296 := by
  rw [BitVec.or_comm,←BitVec.setWidth_append_eq_shiftLeft_setWidth_or,BitVec.setWidth_eq,
    BitVec.toNat_append,←Nat.shiftLeft_add_eq_or_of_lt lo.isLt,Nat.shiftLeft_eq]
  omega_using []

end VG.Proof.MlDsa.AArch64.Optimized.Response
