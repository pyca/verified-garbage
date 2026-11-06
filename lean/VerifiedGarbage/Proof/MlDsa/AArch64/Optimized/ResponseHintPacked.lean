module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintFinish
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintCount
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZInit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseAdd
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintVec
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFinish

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64

theorem packedWords_nat (lo hi : BitVec 32) :
    (lo.setWidth 64 ||| (hi.setWidth 64 <<< 32)).toNat=lo.toNat+hi.toNat*4294967296 := by
  rw [BitVec.or_comm,←BitVec.setWidth_append_eq_shiftLeft_setWidth_or,BitVec.setWidth_eq,
    BitVec.toNat_append,←Nat.shiftLeft_add_eq_or_of_lt lo.isLt,Nat.shiftLeft_eq]
  omega

end VG.Proof.MlDsa.AArch64.Optimized.Response
