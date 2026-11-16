module

public import VerifiedGarbage.Impl.Aes.AArch64.Neon.Blocks

/-!
# CBC decryption, bitsliced in AdvSIMD registers, on AArch64

`decrypt(schedule = x0, rounds = x1, iv = x2, data = x3, n = x4, scratch = x5)`,
the arguments of `vg_aes_cbc_decrypt` (`Impl/AesCbc/AArch64.lean`), for
CPUs without the Cryptographic Extension: eight blocks at a time, deciphered
as `vg_aes_decrypt_blocks_neon` deciphers them (`Impl/Aes/AArch64/Neon/Blocks.lean`:
`keySetup`, `keyBody`, `loadFrom`, `decrypt8`, `advance`), with the round
keys bitsliced once for the whole call.

Each group of eight blocks, or the last one to seven: the `Cⱼ` are loaded and
deciphered into `v16`–`v23`; then, with the chaining value in `v31` (loaded
from `iv`), each block in turn is XORed with it, its `Cⱼ`, still in the
data, is loaded into `v31`, and the block is stored (`chainFrom`); and `v31`,
the last `Cⱼ`, is stored to `iv`. One block alone (`n = 1`) is decrypted by
vector permutations, with nothing bitsliced (`decOne`).

Only the first 2048 bytes of the scratch buffer are written, and no
callee-saved register. Only the pointers, `rounds` and `n` can affect
timing.
-/

@[expose] public section

namespace VG.Impl.AesCbc.AArch64.Neon

open VG.AArch64
open VG.Impl.Aes.AArch64.Neon

/-- Deciphered block `k` XORed with the chaining value in `v31`, its
ciphertext block loaded into `v31`, and the result stored. -/
def chain1 (k : Nat) : List Instr :=
  [veor (B k) (B k) .v31, .ldrq .v31 .x3 (16 * k), .strq (B k) .x3 (16 * k)]

/-- `chain1` of the blocks `k`, `k + 1`, … while there are blocks left
(`x4`), `fuel + 1` at most. -/
def chainFrom : Nat → Nat → Prog isa
  | 0, k => .block (chain1 k)
  | fuel + 1, k =>
    .seq (.block (chain1 k ++ ([.subImm .x .x6 .x4 (k + 1)] : List Instr)))
      (.ite (.nonzero .x .x6) (chainFrom fuel (k + 1)) (.block []))

/-- One group of (up to) eight blocks. -/
def decGroup : Prog isa :=
  .seq (loadFrom 7 0)
    (.seq decrypt8
      (.seq (.block [.ldrq .v31 .x2 0])
        (.seq (chainFrom 7 0) (.seq (.block [.strq .v31 .x2 0]) advance))))

/-- Nothing for no block; else the round keys bitsliced, and `group` for
each group of (up to) eight blocks. -/
def whole (group : Prog isa) : Prog isa :=
  .ite (.zero .x .x4) (.block [])
    (.seq (.block keySetup)
      (.seq (.loop (.block keyBody) (.nonzero .x kp)) (.loop group (.nonzero .x .x4))))

/-- One block: deciphered by vector permutations (`Vperm.Dec.core`), XORed
with the block at `iv` into the data, and its ciphertext stored to `iv`. -/
def decOne : Prog isa :=
  .seq (.block [.ldrq .v0 .x3 0])
    (.seq Impl.Aes.AArch64.Vperm.Dec.core
      (.block [.ldrq .v1 .x2 0, veor .v0 .v0 .v1, .ldrq .v1 .x3 0, .strq .v0 .x3 0,
        .strq .v1 .x2 0]))

/-- The code `vg_aes_cbc_decrypt_neon` runs before it wipes `scratch`: one
block by vector permutations, any other number of blocks bitsliced. -/
def decrypt : Prog isa :=
  .seq (.block [.subImm .x .x6 .x4 1]) (.ite (.zero .x .x6) decOne (whole decGroup))

end VG.Impl.AesCbc.AArch64.Neon
