module

public import VerifiedGarbage.Proof.RsaOaep.X86.Certs
public import VerifiedGarbage.Proof.RsaPss.X86.Hashes.Sha512

/-! # RSAES-OAEP on x86: the SHA-512 family, as RSASSA-PSS has them (`Proof/RsaPss/X86/Hashes/Sha512.lean`) -/

@[expose] public section

namespace VG.Proof.RsaOaep.X86


def sha384 : OHash := .ofPss Proof.RsaPss.X86.sha384 (.inr (.inr (.inr (.inl Proof.RsaPss.X86.sha384.glen.symm))))
def sha512 : OHash := .ofPss Proof.RsaPss.X86.sha512 (.inr (.inr (.inr (.inr Proof.RsaPss.X86.sha512.glen.symm))))
def sha512_224 : OHash :=
  .ofPss Proof.RsaPss.X86.sha512_224 (.inr (.inl Proof.RsaPss.X86.sha512_224.glen.symm))
def sha512_256 : OHash :=
  .ofPss Proof.RsaPss.X86.sha512_256 (.inr (.inr (.inl Proof.RsaPss.X86.sha512_256.glen.symm)))

end VG.Proof.RsaOaep.X86
