module

public import VerifiedGarbage.Proof.TripleDes.AArch64.FunctionsLit
meta import VerifiedGarbage.Proof.TripleDes.AArch64.FunctionsLit
public import VerifiedGarbage.Impl.TripleDes.AArch64.Cbc
meta import VerifiedGarbage.Impl.TripleDes.AArch64.Cbc
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-! # Triple DES-CBC's AArch64 code as literals, for kernel-evaluated checks -/

@[expose] public section

namespace VG

materialize_code Impl.TripleDes.AArch64.cbcEncryptChained
materialize_code Impl.TripleDes.AArch64.cbcDecryptChained

end VG
