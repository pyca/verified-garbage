module

public import VerifiedGarbage.Proof.AesXts.X86_64.Verified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.AesXts.X86_64.Body

/-! # XTS-AES (IEEE Std 1619-2007, NIST SP 800-38E) on x86-64 -/

@[expose] public section

namespace VG.Generic.AesBlocks.X86_64.AesXts

open VG.Proof.AesXts.X86_64

def artifacts (v : Proof.Aes.X86_64.BlocksImpl) : List Artifact := [
  ]

end VG.Generic.AesBlocks.X86_64.AesXts
