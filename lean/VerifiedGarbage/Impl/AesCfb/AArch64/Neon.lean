module

public import VerifiedGarbage.Impl.AesCbc.AArch64.Neon
public import VerifiedGarbage.Impl.Aes.AArch64.Neon.Ctr32

/-!
# CFB128 decryption, bitsliced in AdvSIMD registers, on AArch64

`decrypt(schedule = x0, rounds = x1, iv = x2, data = x3, n = x4, scratch = x5)`,
the arguments of `vg_aes_cfb128_decrypt` (`Impl/AesCfb/AArch64.lean`), for
CPUs without the Cryptographic Extension: eight blocks at a time, enciphered
as `vg_aes_encrypt_blocks_neon` enciphers them, with the round keys
bitsliced once for the whole call (`Impl.AesCbc.AArch64.Neon.whole`).

Each group of eight blocks, or the last one to seven: the inputs of the
block cipher, the block at `iv` and the `Cⱼ` but the last, are loaded into
`v0`–`v7` (`loadPrev`) and enciphered into `v16`–`v23`; then each `Cⱼ` in
turn is loaded into `v31`, XORed into its enciphered input, and the result
stored over it (counter mode's `xorFrom`, in place); and `v31`, the last
`Cⱼ`, is stored to `iv`. One block alone (`n = 1`) is decrypted by table
lookups, with nothing bitsliced (`decOne`).

Only the first 2048 bytes of the scratch buffer are written, and no
callee-saved register. Only the pointers, `rounds` and `n` can affect
timing.
-/

@[expose] public section

namespace VG.Impl.AesCfb.AArch64.Neon

open VG.AArch64
open VG.Impl.Aes.AArch64.Neon

/-- Data blocks `k`, `k + 1`, … into `A (k + 1)`, … while they have a block
after them (`x4`, the blocks left): the inputs of the blocks after the
first. -/
def loadPrev : Nat → Nat → Prog isa
  | 0, k => .block [.ldrq (A (k + 1)) .x3 (16 * k)]
  | fuel + 1, k =>
    .seq (.block [.ldrq (A (k + 1)) .x3 (16 * k), .subImm .x .x6 .x4 (k + 2)])
      (.ite (.nonzero .x .x6) (loadPrev fuel (k + 1)) (.block []))

/-- One group of (up to) eight blocks. -/
def decGroup : Prog isa :=
  .seq (.block [.ldrq (A 0) .x2 0, .subImm .x .x6 .x4 1])
    (.seq (.ite (.nonzero .x .x6) (loadPrev 6 0) (.block []))
      (.seq encrypt8
        (.seq (xorFrom false 7 0) (.seq (.block [.strq .v31 .x2 0]) advance))))

/-- One block: the block at `iv` enciphered by vector permutations
(`Vperm.core`), XORed with the ciphertext block into the data, and the
ciphertext block stored to `iv`. -/
def decOne : Prog isa :=
  .seq (.block [.ldrq .v0 .x2 0])
    (.seq Impl.Aes.AArch64.Vperm.core
      (.block [.ldrq .v1 .x3 0, veor .v0 .v0 .v1, .strq .v0 .x3 0, .strq .v1 .x2 0]))

/-- `vg_aes_cfb128_decrypt_neon`: one block by vector permutations, as the generic
code decrypts it, any other number of blocks bitsliced. -/
def decrypt : Prog isa :=
  .seq (.block [.subImm .x .x6 .x4 1])
    (.ite (.zero .x .x6) decOne (Impl.AesCbc.AArch64.Neon.whole decGroup))

end VG.Impl.AesCfb.AArch64.Neon
