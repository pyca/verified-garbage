module

public import VerifiedGarbage.Proof.AesXts.AArch64.Verified
public import VerifiedGarbage.Proof.AesXts.AArch64.Unit.Verified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.AesXts.AArch64.Body

/-!
# XTS-AES (IEEE Std 1619-2007, NIST SP 800-38E) on AArch64

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling an
implementation `v` of `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks`,
are emitted once for each implementation (`Variants/AesBlocks/AArch64/`),
named with its suffix (e.g. `vg_aes_xts_encrypt_aes`), and need its CPU
features. The functions on whole data units call the whole-block functions
with the same suffix (e.g. `vg_aes_xts_encrypt_unit_aes` calls
`vg_aes_xts_encrypt_aes`).

No stack is used: the calls keep the return address in `x30`, which each
function saves in the scratch buffer.
-/

@[expose] public section

namespace VG.Generic.AesBlocks.AArch64.AesXts

open VG.Proof.AesXts.AArch64

def artifacts (v : Proof.Aes.AArch64.BlocksImpl) : List Artifact := [
  Spec.Xts.aesEncryptApi.artifact AArch64.target {
    suffix := v.suffix
    notes := ["This implementation enciphers one block at a time with `" ++
      v.enc.name ++ "`."]
    code := Impl.AesXts.AArch64.encrypt v.enc
    verified := encrypt_verified v
    features := v.features },
  Spec.Xts.aesDecryptApi.artifact AArch64.target {
    suffix := v.suffix
    notes := ["This implementation deciphers one block at a time with `" ++
      v.dec.name ++ "`."]
    code := Impl.AesXts.AArch64.decrypt v.dec
    verified := decrypt_verified v
    features := v.features },
  Spec.Xts.aesEncryptUnitApi.artifact AArch64.target {
    suffix := v.suffix
    notes := ["This implementation enciphers the tweak value and the data with `" ++ (Unit.xtsE v).name ++
      "` (the tweak value as one block from a zero tweak), and steals ciphertext by swapping bytes of the " ++
      "last two blocks in place."]
    code := Impl.AesXts.AArch64Unit.encrypt (Unit.xtsE v)
    verified := Unit.encrypt_verified v
    features := v.features },
  Spec.Xts.aesDecryptUnitApi.artifact AArch64.target {
    suffix := v.suffix
    notes := ["This implementation enciphers the tweak value with `" ++ (Unit.xtsE v).name ++
      "` (as one block from a zero tweak), deciphers the data with `" ++ (Unit.xtsD v).name ++
      "`, and steals ciphertext by swapping bytes of the last two blocks in place."]
    code := Impl.AesXts.AArch64Unit.decrypt (Unit.xtsE v) (Unit.xtsD v)
    verified := Unit.decrypt_verified v
    features := v.features }]

end VG.Generic.AesBlocks.AArch64.AesXts
