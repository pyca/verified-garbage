module

public import VerifiedGarbage.Proof.RsaOaep.X86.Certs
public import VerifiedGarbage.Proof.RsaPss.X86.Hashes.Sha224

/-! # RSAES-OAEP on x86: SHA-224, with any SHA-256 backend, as RSASSA-PSS has them (`Proof/RsaPss/X86/Hashes/Sha224.lean`) -/

@[expose] public section

namespace VG.Proof.RsaOaep.X86

open VG.Proof.Sha256.X86.Variants (Backend)


/-- SHA-224 with the SHA-256 backend `v`. -/
def sha224 (v : Backend) : OHash :=
  .ofPss (Proof.RsaPss.X86.sha224 v) (.inr (.inl (Proof.RsaPss.X86.sha224 v).glen.symm))

end VG.Proof.RsaOaep.X86
