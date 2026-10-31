module

public import VerifiedGarbage.Proof.Camellia.X86_64.Verified
public import VerifiedGarbage.Proof.Camellia.X86_64.KeyVerified
public import VerifiedGarbage.Proof.Camellia.X86_64.PreparedVerified
import VerifiedGarbage.Proof.Camellia.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.Camellia.X86_64

def artifacts : List Artifact := [
  Spec.Camellia.expandKeyApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3216 .rcx 401 Impl.Camellia.X86_64.expandKey
    stack := 3216
    verified := Proof.Camellia.X86_64.expandKey_framed },
  Spec.Camellia.ecbEncryptApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3216 .r8 401
      (Impl.Camellia.X86_64.ecb .encrypt)
    stack := 3216
    verified := Proof.Camellia.X86_64.ecb_framed .encrypt },
  Spec.Camellia.ecbDecryptApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3216 .r8 401
      (Impl.Camellia.X86_64.ecb .decrypt)
    stack := 3216
    verified := Proof.Camellia.X86_64.ecb_framed .decrypt },
  (Spec.Camellia.Prepared.cryptApi Impl.Camellia.X86_64.layout).artifact X86_64.target {
    code := Impl.Camellia.X86_64.cryptPrepared
    verified := Proof.Camellia.X86_64.crypt_verified }]

end VG.Artifacts.Camellia.X86_64
