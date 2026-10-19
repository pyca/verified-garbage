module

public import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
import VerifiedGarbage.Impl.Gcm.X86_64
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Copy
import VerifiedGarbage.Proof.CmacAes.X86_64.Dbl
import VerifiedGarbage.Proof.CmacAes.X86_64.Finalize
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
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Gcm.X86_64.Bits

/-!
# AES-CMAC (NIST SP 800-38B) on x86-64

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling an
implementation `v` of `vg_aes_ctr32`, are emitted once for each implementation
(`Variants/AesCtr32/X86_64/`), named with its suffix (e.g.
`vg_cmac_aes_update_aesni`), and need its CPU features.

The stack is 8 bytes for every implementation of the first three: the
return address of the call of `vg_aes_ctr32`, which makes no calls. The
streaming functions `init` and `finish` call those, so their stack is 16
bytes; `init` also calls the implementation of `vg_aes_expand_key_scratch`
that goes with `v`. `vg_cmac_aes_absorb`, which calls only
`vg_cmac_aes_update`, follows its implementations instead
(`Generic/CmacAesUpdate/X86_64/Absorb.lean`).

The streaming functions keep their working space in a frame of their own
on the stack (`Proof/CmacAes/Stream/X86_64/Frame.lean`): their `stack` is that
frame and the stack their code uses below it.
-/

@[expose] public section

namespace VG.Generic.AesCtr32.X86_64.CmacAes

open VG.Proof.CmacAes.X86_64

/-- Which implementation of `vg_aes_ctr32` an instance calls. -/
def ctrNote (v : Proof.Aes.X86_64.Ctr32Impl) : String :=
  "This implementation encrypts each block with `" ++ v.callee.name ++ "`."

/-- Which CMAC functions an instance of a streaming function calls. -/
def streamNote (v : Proof.Aes.X86_64.Ctr32Impl) : String :=
  "This implementation calls the CMAC functions made with `" ++ v.callee.name ++ "` (e.g. `" ++
    Spec.Cmac.aesUpdateApi.name ++ v.suffix ++ "`)."

def artifacts (v : Proof.Aes.X86_64.Ctr32Impl) : List Artifact := [
  Spec.Cmac.aesSubkeysApi.artifact X86_64.target {
    suffix := v.suffix
    notes := [ctrNote v]
    code := Impl.CmacAes.X86_64.subkeys v.callee
    stack := 8
    verified := subkeys_verified v
    spSafe := subkeys_spSafe v
    features := v.features },
  Spec.Cmac.aesUpdateApi.artifact X86_64.target {
    suffix := v.suffix
    notes := [ctrNote v]
    code := Impl.CmacAes.X86_64.update v.callee
    stack := 8
    verified := update_verified v
    spSafe := update_spSafe v
    features := v.features },
  Spec.Cmac.aesFinalizeApi.artifact X86_64.target {
    suffix := v.suffix
    notes := [ctrNote v]
    code := Impl.CmacAes.X86_64.finalize v.callee
    stack := 8
    verified := finalize_verified v
    spSafe := finalize_spSafe v
    features := v.features },
  Spec.Cmac.aesInitApi.artifact X86_64.target {
    suffix := v.suffix
    notes := [streamNote v,
      "It expands the key with `" ++ v.expand.name ++ "`."]
    code := Impl.StackScratch.X86_64.withStackScratch 2312 .rcx
      (Impl.CmacAes.Stream.X86_64.init v.expand v.callee v.suffix)
    stack := 2328
    verified := Proof.CmacAes.Stream.X86_64.init_framed v
    spSafe := X86_64.withStackScratch_spSafe_of (Proof.CmacAes.Stream.X86_64.init_spSafe v)
    features := v.features },
  Spec.Cmac.aesFinishApi.artifact X86_64.target {
    suffix := v.suffix
    notes := [streamNote v]
    code := Impl.StackScratch.X86_64.withStackScratch 2312 .r8
      (Impl.CmacAes.Stream.X86_64.finish v.callee v.suffix)
    stack := 2328
    verified := Proof.CmacAes.Stream.X86_64.finish_framed v
    spSafe := X86_64.withStackScratch_spSafe_of (Proof.CmacAes.Stream.X86_64.finish_spSafe v)
    features := v.features }]

end VG.Generic.AesCtr32.X86_64.CmacAes
