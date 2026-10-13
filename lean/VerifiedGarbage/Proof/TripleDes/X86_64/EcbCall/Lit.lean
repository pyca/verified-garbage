module

public import VerifiedGarbage.Impl.TripleDes.X86_64.EcbCall
meta import VerifiedGarbage.Impl.TripleDes.X86_64.EcbCall
public import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx512.Lit
meta import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx512.Lit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
public import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx2.SboxLit
meta import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx2.SboxLit

/-! # The ECB functions' code around the call of the core, as literals -/

@[expose] public section

namespace VG

materialize_code Impl.TripleDes.X86_64.EcbCall.sseEncrypt
materialize_code Impl.TripleDes.X86_64.EcbCall.sseDecrypt
materialize_code Impl.TripleDes.X86_64.EcbCall.avx2Encrypt
materialize_code Impl.TripleDes.X86_64.EcbCall.avx2Decrypt
materialize_code Impl.TripleDes.X86_64.EcbCall.avx512Encrypt
materialize_code Impl.TripleDes.X86_64.EcbCall.avx512Decrypt

end VG
