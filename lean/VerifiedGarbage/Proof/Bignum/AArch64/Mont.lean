import VerifiedGarbage.Proof.Bignum.AArch64.SquareMont

/-! The default Montgomery implementation used by AArch64 RSA callers. -/
namespace VG.Proof.Bignum.AArch64

def Mont.base : Mont := Mont.square

end VG.Proof.Bignum.AArch64
