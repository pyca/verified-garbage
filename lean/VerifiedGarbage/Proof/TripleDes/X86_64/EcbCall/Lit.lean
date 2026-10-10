import VerifiedGarbage.Impl.TripleDes.X86_64.EcbCall
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx512.Lit

/-! # The ECB functions' code around the call of the core, as literals -/

namespace VG

materialize_code Impl.TripleDes.X86_64.EcbCall.sseEncrypt
materialize_code Impl.TripleDes.X86_64.EcbCall.sseDecrypt
materialize_code Impl.TripleDes.X86_64.EcbCall.avx2Encrypt
materialize_code Impl.TripleDes.X86_64.EcbCall.avx2Decrypt
materialize_code Impl.TripleDes.X86_64.EcbCall.avx512Encrypt
materialize_code Impl.TripleDes.X86_64.EcbCall.avx512Decrypt

end VG
