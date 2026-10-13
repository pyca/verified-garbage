module

public import VerifiedGarbage.Proof.Bignum.AArch64.SquareMont
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! The default Montgomery implementation used by AArch64 RSA callers. -/

@[expose] public section

namespace VG.Proof.Bignum.AArch64

def Mont.base : Mont := Mont.square

end VG.Proof.Bignum.AArch64
