module

public import VerifiedGarbage.Proof.RsaOaep.X86.Certs
public import VerifiedGarbage.Proof.RsaPss.X86.Hashes.Sha1

/-! # RSAES-OAEP on x86: SHA-1, with any backend, as RSASSA-PSS has them (`Proof/RsaPss/X86/Hashes/Sha1.lean`) -/

@[expose] public section

namespace VG.Proof.RsaOaep.X86

open VG.Proof.Sha1.X86.Variants (Backend)


/-- SHA-1 with the backend `v`. -/
def sha1 (v : Backend) : OHash := .ofPss (Proof.RsaPss.X86.sha1 v) (.inl (Proof.RsaPss.X86.sha1 v).glen.symm)

end VG.Proof.RsaOaep.X86
