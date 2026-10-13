module

public import VerifiedGarbage.Proof.TripleDes.X86_64.FunctionsLit
meta import VerifiedGarbage.Proof.TripleDes.X86_64.FunctionsLit
public import VerifiedGarbage.Impl.TripleDes.X86_64.Cbc
meta import VerifiedGarbage.Impl.TripleDes.X86_64.Cbc
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Triple DES-CBC's x86-64 code as literals, for kernel-evaluated checks -/

@[expose] public section

namespace VG

materialize_code Impl.TripleDes.X86_64.cbcEncrypt
materialize_code Impl.TripleDes.X86_64.cbcDecrypt
materialize_code Impl.TripleDes.X86_64.cbcEncryptI
materialize_code Impl.TripleDes.X86_64.cbcDecryptI

end VG
