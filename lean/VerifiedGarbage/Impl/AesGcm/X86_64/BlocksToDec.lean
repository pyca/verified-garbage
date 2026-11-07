module

public import VerifiedGarbage.Impl.AesGcm.X86_64.BlocksTo

/-!
# AES-GCM decryption of whole blocks, out of place: x86-64 implementation

`vg_aes_gcm_decrypt_blocks_to` `(ctx = rdi, rounds = rsi, counter = rdx,
y = rcx, src = r8, n = r9, dst = [rsp + 8], dst_n = [rsp + 16],
scratch = [rsp + 24])`: `vg_aes_gcm_encrypt_blocks_to`'s code
(`BlocksTo.encrypt`), with a `piece` that decrypts out of place
(`Gcm.X86_64.Stitch.DPostTo`, the first `16 ⌊n / 16⌋` blocks, if any), and
calling `vg_aes_gcm_decrypt_blocks` (`dec`) in place for the rest, which it
copies from `src` to `dst` first: GHASH absorbs the ciphertext, which the
piece reads from `src` and the call from its copy.
-/

@[expose] public section

namespace VG.Impl.AesGcm.X86_64.BlocksToDec

open VG.X86_64

/-- `vg_aes_gcm_decrypt_blocks_to`, with the out-of-place decrypting
`piece`, if any, and calling `dec` (`vg_aes_gcm_decrypt_blocks`) for the
rest. -/
def decrypt (dec : Fn) (piece : Option (Prog isa)) (aligned : Bool := false) : Prog isa :=
  BlocksTo.encrypt dec piece aligned false

end VG.Impl.AesGcm.X86_64.BlocksToDec
