module

public import VerifiedGarbage.Proof.AesSiv.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
import VerifiedGarbage.Impl.AesCcm.X86_64
import VerifiedGarbage.Impl.Gcm.X86_64
import VerifiedGarbage.Impl.Gcm.X86_64.Pclmul
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
import VerifiedGarbage.Proof.AesCcm.Mac
import VerifiedGarbage.Proof.AesCcm.X86_64.Contract
import VerifiedGarbage.Proof.AesSiv.Ctr32
import VerifiedGarbage.Proof.AesSiv.X86_64.CmacOf
import VerifiedGarbage.Proof.AesSiv.X86_64.Init
import VerifiedGarbage.Proof.AesSiv.X86_64.Open
import VerifiedGarbage.Proof.AesSiv.X86_64.XorBytes
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.CmacAes.X86_64.Dbl
import VerifiedGarbage.Proof.CmacAes.X86_64.UpdateCorrect
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Gcm.X86_64.Bits
import VerifiedGarbage.Spec.Ccm.Contract
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

/-!
# AES-SIV (RFC 5297) encryption and decryption on x86-64

A generic file (see `TCB/Emit.lean`): `vg_aes_siv_encrypt` and
`vg_aes_siv_decrypt`, calling an implementation `v` of `vg_cmac_aes_update`,
and the CMAC functions and `vg_aes_ctr32` made with the implementation of
AES that goes with it (`v.ctr`), are emitted once for each implementation
of the update (`Variants/CmacAesUpdate/X86_64/`), named with its suffix
(e.g. `vg_aes_siv_encrypt_aesni_cbc`), and need the CPU features of both.

Each function keeps its working space in a frame of its own
(`Proof/AesSiv/X86_64/Frame.lean`) of 2600 bytes, which also holds a copy of
`siv`, its seventh argument, passed on the stack; below it its calls use at
most 16 bytes: the return addresses of the call of a CMAC function (or of
`vg_aes_ctr32`) and of its call of `vg_aes_ctr32` (2616 bytes of stack in
all).
-/

@[expose] public section

namespace VG.Generic.CmacAesUpdate.X86_64.AesSiv

open VG.Proof.AesSiv.X86_64

def artifacts (v : Proof.CmacAes.X86_64.UpdateImpl) : List Artifact := [
  Spec.Siv.encryptApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2600 1
      (Impl.AesSiv.X86_64.encrypt v.callee v.ctr.callee v.ctr.suffix)
    stack := 2616
    verified := encrypt_framed v
    spSafe := X86_64.withStackArgScratch_spSafe (encrypt_spSafe v)
    features := v.ctr.features },
  Spec.Siv.decryptApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2600 1
      (Impl.AesSiv.X86_64.decrypt v.callee v.ctr.callee v.ctr.suffix)
    stack := 2616
    verified := decrypt_framed v
    spSafe := X86_64.withStackArgScratch_spSafe (decrypt_spSafe v)
    features := v.ctr.features }]

end VG.Generic.CmacAesUpdate.X86_64.AesSiv
