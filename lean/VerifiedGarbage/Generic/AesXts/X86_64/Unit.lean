module

public import VerifiedGarbage.Proof.AesXts.X86_64.Unit.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# XTS-AES (IEEE Std 1619-2007, NIST SP 800-38E) of whole data units on x86-64

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling an
implementation `v` of `vg_aes_xts_encrypt` and `vg_aes_xts_decrypt`, are
emitted once for each implementation (`Variants/AesXts/X86_64/`), named
with its suffix (e.g. `vg_aes_xts_encrypt_unit_vaes_vpclmul`), and need its
CPU features.

The stack is 16 bytes: the return addresses of the call of the whole-block
function and of its call of a block function, if it makes one.
-/

@[expose] public section

namespace VG.Generic.AesXts.X86_64.Unit

open VG.Proof.AesXts.X86_64.Unit

def artifacts (v : Proof.AesXts.X86_64.XtsImpl) : List Artifact := [
  Spec.Xts.aesEncryptUnitApi.artifact X86_64.target {
    suffix := v.suffix
    notes := ["This implementation enciphers the tweak value and the data with `" ++ v.enc.name ++
      "` (the tweak value as one block from a zero tweak), and steals ciphertext by swapping bytes of the " ++
      "last two blocks in place."]
    code := Impl.AesXts.X86_64Unit.encrypt v.xts
    stack := 16
    verified := encrypt_verified v
    spSafe := encrypt_spSafe v
    features := v.features },
  Spec.Xts.aesDecryptUnitApi.artifact X86_64.target {
    suffix := v.suffix
    notes := ["This implementation enciphers the tweak value with `" ++ v.enc.name ++
      "` (as one block from a zero tweak), deciphers the data with `" ++ v.dec.name ++
      "`, and steals ciphertext by swapping bytes of the last two blocks in place."]
    code := Impl.AesXts.X86_64Unit.decrypt v.xts
    stack := 16
    verified := decrypt_verified v
    spSafe := decrypt_spSafe v
    features := v.features }]

end VG.Generic.AesXts.X86_64.Unit
