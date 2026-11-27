module

public import VerifiedGarbage.Impl.AesGcm.RISCV64

/-!
# AES-GCM decryption out of place, reading the key's bitsliced form: RISC-V implementation

`vg_aes_gcm_open_to_bitsliced(ctx = a0, rounds = a1, nonce = a2,
nonce_len = a3, aad = a4, aad_len = a5, src = a6, len = a7, dst, dst_len,
tag, tag_len, bk)`, its ninth to thirteenth arguments in memory (RISC-V
psABI, "Integer Calling Convention": on the stack, from `sp` on entry), is
`vg_aes_gcm_open_bitsliced`'s body out of place (`openWithB true true`,
`Impl/AesGcm/RISCV64.lean`): it hashes the ciphertext at `src` and, if the
tag is right, decrypts it from `src` straight to `dst` (`vg_aes_ctr32_bs_to`
on the buffer at `bk` for the whole blocks, `xorLoop` from `src` to `dst`
for the others), with no copy. If the tag is wrong, or its length is not
allowed, it zeroes `dst` a byte at a time (`wipe`) and returns 0.

The frame of `withStackScratchArgs` (`Proof/AesGcm/RISCV64/OpenToBs.lean`)
copies the five stack arguments and then passes the working space's
address after them: `dst`, `dst_len`, `tag`, `tag_len` and `bk` at `sp` …
`sp + 32`, the working space at `sp + 40`. The branches are on the lengths
and on whether the tag is right, as `vg_aes_gcm_open_bitsliced`'s.
-/

@[expose] public section

namespace VG.Impl.AesGcm.RISCV64.OpenTo

open VG.RISCV64

/-- `vg_aes_gcm_open_to_bitsliced`. -/
def openToBs : Prog isa := openWithB true true

end VG.Impl.AesGcm.RISCV64.OpenTo
