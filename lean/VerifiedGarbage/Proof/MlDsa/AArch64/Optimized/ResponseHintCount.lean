module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZInit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseAdd
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem

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
  omega

/-- The final logical shift makes every hint a bit, even on rejected inputs. -/
theorem hintWord_bit (B t h : BitVec 32) : (hintWord B t h).toNat≤1 :=
  shift31_bound _

end VG.Proof.MlDsa.AArch64.Optimized.Response

end
