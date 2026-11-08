module

public import VerifiedGarbage.Proof.AesSiv.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
public import VerifiedGarbage.Impl.AesCcm.X86_64
public import VerifiedGarbage.Impl.Gcm.X86_64
public import VerifiedGarbage.Impl.Gcm.X86_64.Pclmul
public import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
public import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
public import VerifiedGarbage.Proof.AesCcm.Mac
public import VerifiedGarbage.Proof.AesCcm.X86_64.Contract
public import VerifiedGarbage.Proof.AesSiv.Ctr32
public import VerifiedGarbage.Proof.AesSiv.X86_64.CmacOf
public import VerifiedGarbage.Proof.AesSiv.X86_64.Init
public import VerifiedGarbage.Proof.AesSiv.X86_64.Open
public import VerifiedGarbage.Proof.AesSiv.X86_64.XorBytes
public import VerifiedGarbage.Proof.Cmac.Dbl32
public import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Proof.CmacAes.X86_64.Dbl
public import VerifiedGarbage.Proof.CmacAes.X86_64.UpdateCorrect
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegSetOrder
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86_64.Avx
public import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.Masked
public import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.Framework.X86_64.Sse
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
public import VerifiedGarbage.Proof.Gcm.Spec
public import VerifiedGarbage.Proof.Gcm.Stream
public import VerifiedGarbage.Proof.Gcm.X86_64.Bits
public import VerifiedGarbage.Spec.Ccm.Contract
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.Variants.AesCtr32.X86_64
public import VerifiedGarbage.Proof.Variants.CmacAesUpdate.X86_64

/-! # AES-SIV (RFC 5297) key setup on x86-64 -/

@[expose] public section

namespace VG.Artifacts.AesSiv.X86_64.AesCtr32

open VG.Proof.AesSiv.X86_64

def artifacts (v : Proof.Aes.X86_64.Ctr32Impl) : List Artifact := [
  Spec.Siv.initApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackScratch 2568 .rcx
      (Impl.AesSiv.X86_64.init v.expand v.callee v.suffix)
    stack := 2584
    verified := init_framed v
    spSafe := X86_64.withStackScratch_spSafe_of (init_spSafe v)
    features := v.features }]

end VG.Artifacts.AesSiv.X86_64.AesCtr32

-- AES-SIV (RFC 5297) encryption and decryption on x86-64
namespace VG.Artifacts.AesSiv.X86_64.CmacAesUpdate

open VG.Proof.AesSiv.X86_64

def artifacts (v : Proof.CmacAes.X86_64.UpdateImpl) : List Artifact := [
  Spec.Siv.encryptApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2600 1
      (Impl.AesSiv.X86_64.encrypt v.callee v.ctr.callee v.ctr.suffix)
    stack := 2616
    verified := Proof.AesSiv.encrypt_keyed (encrypt_framed v)
    spSafe := X86_64.withStackArgScratch_spSafe (encrypt_spSafe v)
    features := v.ctr.features },
  Spec.Siv.decryptApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2600 1
      (Impl.AesSiv.X86_64.decrypt v.callee v.ctr.callee v.ctr.suffix)
    stack := 2616
    verified := Proof.AesSiv.decrypt_keyed (decrypt_framed v)
    spSafe := X86_64.withStackArgScratch_spSafe (decrypt_spSafe v)
    features := v.ctr.features }]

end VG.Artifacts.AesSiv.X86_64.CmacAesUpdate

namespace VG.Artifacts.AesSiv.X86_64

def artifacts : List Artifact :=
  (VG.Proof.Variants.AesCtr32.X86_64.variants.flatMap fun v => AesCtr32.artifacts v) ++
  (VG.Proof.Variants.CmacAesUpdate.X86_64.variants.flatMap fun v => CmacAesUpdate.artifacts v)

end VG.Artifacts.AesSiv.X86_64
