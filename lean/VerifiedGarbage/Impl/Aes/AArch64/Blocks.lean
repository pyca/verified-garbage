module

public import VerifiedGarbage.Impl.Aes.AArch64.Ctr32
public import VerifiedGarbage.Impl.Aes.AArch64.Inv
public import VerifiedGarbage.Impl.Aes.AArch64.Vperm

/-!
# AES encryption and decryption of whole blocks on AArch64

`vg_aes_encrypt_blocks(schedule = x0, rounds = x1, data = x2, n = x3, scratch = x4)`
and `vg_aes_decrypt_blocks` with the same arguments (`Spec/Aes/Contract.lean`).

`vg_aes_encrypt_blocks` is `encryptBlocksN`, and `vg_aes_decrypt_blocks` is
`decryptBlocksN`: nothing for no block, else every block one at a time by
vector permutations (`Vperm.lean`, `few`), with nothing written to
`scratch`. The functions bitsliced in AdvSIMD registers
(`Neon/Blocks.lean`) take one to four blocks the same way (`isFew`, `few`),
and move their arguments with `blocksSetup`.

No address and no branch depends on the key or the data: the loop counts
`x3`, loads and stores the block at `x2`, and reads the schedule at `x0`.
-/

@[expose] public section

namespace VG.Impl.Aes.AArch64

open VG.AArch64

/-- The scratch buffer to `x5`, the number of blocks to `x4`, the data to `x3`. -/
def blocksSetup : List Instr := [movR .x5 .x4, movR .x4 .x3, movR .x3 .x2]

/-- One block of `few`: the block at `x2` through `core` in place, on to
the next, and `x0` and `x1`, which `core` writes, back from `x9` and
`x10`. -/
def fewBody (core : Prog isa) : Prog isa :=
  .seq (.block [.ldrq .v0 .x2 0])
    (.seq core (.block [.strq .v0 .x2 0, .addImm .x .x2 .x2 16, .subImm .x .x3 .x3 1,
      movR .x0 .x9, movR .x1 .x10]))

/-- The `x3` blocks at `x2` (one at least), each through `core` (`v0 :=
core(v0)`, the schedule at `x0`, the rounds in `x1`) in place: a few blocks
one at a time, which costs less than a bitsliced batch. -/
def few (core : Prog isa) : Prog isa :=
  .seq (.block [movR .x9 .x0, movR .x10 .x1]) (.loop (fewBody core) (.nonzero .x .x3))

/-- `x6 := 0` for one to four blocks (`x3`), which go one at a time: a batch
costs more than five blocks do (measured). -/
def isFew : List Instr := [.subImm .x .x6 .x3 1, .lsr .x .x6 .x6 2]

/-- `vg_aes_encrypt_blocks`: nothing for no block, else each block by
vector permutations, one at a time. -/
def encryptBlocksN : Prog isa :=
  .ite (.zero .x .x3) (.block []) (few Vperm.core)

/-- `vg_aes_decrypt_blocks`: nothing for no block, else each block by
vector permutations, one at a time. -/
def decryptBlocksN : Prog isa :=
  .ite (.zero .x .x3) (.block []) (few Vperm.Dec.core)

end VG.Impl.Aes.AArch64
