module

public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallResult
import VerifiedGarbage.Proof.Framework.Omega

/-! Setting the link register at call entry leaves the signing inputs unchanged. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64

theorem random_callResult_plain {extra : Nat} {s t : State} (_h : RandomSignABI extra s)
    (_hsp : t.sp = randomBase s) :
    randomCallResult s t = Spec.Dsa.signBytes (s.gpr .x5).toNat (s.gpr .x6).toNat
      (Spec.Rsa.bytesAt t.mem (s.gpr .x3) (s.gpr .x4).toNat)
      (Spec.Rsa.bytesAt t.mem (off (randomBase s) Random.oNonce) (s.gpr .x6).toNat)
      (Spec.Rsa.bytesAt t.mem (s.gpr .x7) (stackArg s 0).toNat) := rfl

end VG.Proof.Dsa.AArch64
