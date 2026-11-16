module

public import VerifiedGarbage.Impl.Aes.AArch64.Neon.Blocks
public import VerifiedGarbage.Impl.Aes.AArch64.Aese
public import VerifiedGarbage.Impl.Aes.AArch64.Ctr32

/-!
# AES counter mode (GCM's `inc₃₂`), bitsliced in AdvSIMD registers, on AArch64

`vg_aes_ctr32_neon(schedule = x0, rounds = x1, counter = x2, data = x3, n = x4, scratch = x5)`,
as `vg_aes_ctr32` (`Ctr32.lean`), and its out-of-place form, the internal
`vg_aes_ctr32_to_neon(…, src = x3, …, dst = x6)`: the same code
(`ctr32Gen`), but that the output goes to the destination, kept in `x14`.

Eight blocks at a time, encrypted as `vg_aes_encrypt_blocks_neon` encrypts
them (`Blocks.lean`: `keySetup`, `keyBody`, `encrypt8`), with the round keys
bitsliced once a call.

* The counter, an integer, is in `w10`. Each group builds eight counter
  blocks in `v0`–`v7` (`Aese.ctrs`), encrypts them into `v16`–`v23`, and
  XORs as many as there are blocks left into the data (`xorFrom`): the
  keystream blocks past the last are computed and dropped.
* The final counter is written back at the end.

Only `x0`, `x3`, `x4`, `x6`–`x10`, `x12`, `x14`, `v0`–`v7` and `v16`–`v31`
are written. `x0`–`x5`, `x7`, `x14`, `kp` and `cnt` hold public values, and
no address or branch depends on anything else.

`vg_aes_ctr32_neon` is `ctr32N`, and `vg_aes_ctr32_to_neon` is `ctr32ToN`:
as `vg_aes_ctr32` and `vg_aes_ctr32_to` do, they return at once for no block
(`n = 0`), and encrypt one block (`n = 1`) by vector permutations (`ctr32One`,
`ctr32OneTo`), with nothing bitsliced; `ctr32Gen` is for two blocks or more.
-/

@[expose] public section

namespace VG.Impl.Aes.AArch64.Neon

open VG.AArch64
open VG.Impl.Aes.AArch64.Aese (ctrs regs8 xor1 advO ctrStore)

/-- XOR the keystream blocks `B k`, … into the data blocks `k`, `k + 1`, …
while there are blocks left (`x4`), `fuel + 1` at most, stored to the
output. -/
def xorFrom (to : Bool) : Nat → Nat → Prog isa
  | 0, k => .block (xor1 to (B k) k)
  | fuel + 1, k =>
    .seq (.block (xor1 to (B k) k ++ ([.subImm .x .x6 .x4 (k + 1)] : List Instr)))
      (.ite (.nonzero .x .x6) (xorFrom to fuel (k + 1)) (.block []))

/-- On to the next eight blocks, if more than eight were left; the counter
goes past the blocks done. -/
def ctrAdvance (to : Bool) : Prog isa :=
  .seq (.block [.subImm .x .x6 .x4 1, .lsr .x .x6 .x6 3])
    (.ite (.nonzero .x .x6)
      (.block (([.addImm .w .x10 .x10 8, .addImm .x .x3 .x3 128, .subImm .x .x4 .x4 8] : List Instr) ++
        advO to 128))
      (.block [.add .w .x10 .x10 .x4, .movz .x .x4 0 0]))

/-- One group of (up to) eight blocks. -/
def ctrGroup (to : Bool) : Prog isa :=
  .seq (.block (ctrs regs8 0)) (.seq encrypt8 (.seq (xorFrom to 7 0) (ctrAdvance to)))

/-- The destination to `x14`, out of place, and the counter to `w10`. -/
def ctrSetup (to : Bool) : List Instr :=
  cond to [.addImm .x .x14 .x6 0] [] ++ ([.ldr .w .x10 .x2 12, .rev32 .x10 .x10] : List Instr)

/-- The bitsliced code, for one block at least: in place, or out of place
(`to`), with the destination in `x6`. -/
def ctr32Gen (to : Bool) : Prog isa :=
  .seq (.block (ctrSetup to))
    (.seq (.seq (.block keySetup)
        (.seq (.loop (.block keyBody) (.nonzero .x kp)) (.loop (ctrGroup to) (.nonzero .x .x4))))
      (.block ctrStore))

/-- `vg_aes_ctr32_neon`: nothing for no block, one block by vector permutations,
any other number of blocks bitsliced. -/
def ctr32N : Prog isa :=
  .ite (.zero .x .x4) (.block [])
    (.seq (.block [.subImm .x .x6 .x4 1]) (.ite (.zero .x .x6) ctr32One (ctr32Gen false)))

/-- `vg_aes_ctr32_to_neon`: as `ctr32N`, out of place. -/
def ctr32ToN : Prog isa :=
  .ite (.zero .x .x4) (.block [])
    (.seq (.block [.subImm .x .x7 .x4 1]) (.ite (.zero .x .x7) ctr32OneTo (ctr32Gen true)))

end VG.Impl.Aes.AArch64.Neon
