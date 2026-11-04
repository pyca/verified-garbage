module

public import VerifiedGarbage.Proof.RsaOaep.X86.Certs
public import VerifiedGarbage.Proof.RsaPss.X86.Hashes.Md5

/-! # RSAES-OAEP on x86: MD5, as RSASSA-PSS has it (`Proof/RsaPss/X86/Hashes/Md5.lean`) -/

@[expose] public section

namespace VG.Proof.RsaOaep.X86

def md5 : OHash := .ofPss Proof.RsaPss.X86.md5 (.inr (.inr (.inr (.inr (.inr Proof.RsaPss.X86.md5.glen.symm)))))

end VG.Proof.RsaOaep.X86
