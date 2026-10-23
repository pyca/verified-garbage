module

public import VerifiedGarbage.Proof.AesXts.AArch64.Variant
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# XTS-AES (IEEE Std 1619-2007, NIST SP 800-38E) of whole blocks on AArch64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. They are the two implementations of `vg_aes_xts_encrypt` and
`vg_aes_xts_decrypt` (the variants of `AesXts` on AArch64, which
`Generic/AesXts/AArch64/Unit.lean` calls): the baseline, which calls the
bitsliced `vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` on all the
blocks, and `_aes`, the variant for `vg_aes_encrypt_blocks_aes` and
`vg_aes_decrypt_blocks_aes`, which does their work itself, in one pass with
the AES instructions, and calls nothing.

No stack is used: the baseline's call keeps the return address in `x30`,
which it saves in the scratch buffer.
-/

@[expose] public section

namespace VG.Artifacts.AesXts.AArch64

open VG.Proof.AesXts.AArch64

def artifacts : List Artifact := [
  Spec.Xts.aesEncryptApi.artifact AArch64.target {
    notes := ["This implementation enciphers one block at a time with `vg_aes_encrypt_blocks`."]
    code := (XtsImpl.blocks .scalar).enc.code
    verified := encrypt_verified .scalar },
  Spec.Xts.aesDecryptApi.artifact AArch64.target {
    notes := ["This implementation deciphers one block at a time with `vg_aes_decrypt_blocks`."]
    code := (XtsImpl.blocks .scalar).dec.code
    verified := decrypt_verified .scalar },
  Spec.Xts.aesEncryptApi.artifact AArch64.target {
    suffix := "_aes"
    notes := [
      "This implementation reads each block once: it enciphers eight blocks at a time with the AES " ++
      "instructions, each round applied to all eight, then one at a time, computing each group's " ++
      "tweaks in general-purpose registers while the group before it runs."]
    code := Impl.AesXts.AArch64Aes.encrypt
    verified := Aes.encrypt_verified
    features := ["aes"] },
  Spec.Xts.aesDecryptApi.artifact AArch64.target {
    suffix := "_aes"
    notes := [
      "This implementation reads each block once: it deciphers eight blocks at a time with the AES " ++
      "instructions, each round applied to all eight, then one at a time, computing each group's " ++
      "tweaks in general-purpose registers while the group before it runs."]
    code := Impl.AesXts.AArch64Aes.decrypt
    verified := Aes.decrypt_verified
    features := ["aes"] }]

end VG.Artifacts.AesXts.AArch64
