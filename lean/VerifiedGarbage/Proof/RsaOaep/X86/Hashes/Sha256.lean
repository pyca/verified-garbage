module

public import VerifiedGarbage.Proof.RsaOaep.X86.Certs
public import VerifiedGarbage.Proof.RsaPss.X86.Hashes.Sha256

/-! # RSAES-OAEP on x86: SHA-256, with any backend, as RSASSA-PSS has them (`Proof/RsaPss/X86/Hashes/Sha256.lean`) -/

@[expose] public section

namespace VG.Proof.RsaOaep.X86

open VG.Proof.Sha256.X86.Variants (Backend)


/-- SHA-256 with the backend `v`. -/
def sha256 (v : Backend) : OHash :=
  .ofPss (Proof.RsaPss.X86.sha256 v) (.inr (.inr (.inl (Proof.RsaPss.X86.sha256 v).glen.symm)))

end VG.Proof.RsaOaep.X86
