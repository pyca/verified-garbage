module

public import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.SboxLit
meta import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.SboxLit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint

@[expose] public section

namespace VG

materialize_code Impl.TripleDes.AArch64.BitsliceNeon.encrypt
materialize_code Impl.TripleDes.AArch64.BitsliceNeon.decrypt

end VG
