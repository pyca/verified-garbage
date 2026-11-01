module

public import VerifiedGarbage.Impl.AesCbc.RISCV64
public import VerifiedGarbage.Impl.Words.RISCV64.Bytes
public import VerifiedGarbage.Impl.Cmac.RISCV64
public import VerifiedGarbage.Impl.Aes.RISCV64.Chain

/-!
# AES-CMAC: RISC-V implementation

`vg_cmac_aes_subkeys(schedule = a0, rounds = a1, subkeys = a2, scratch = a3)`,
`vg_cmac_aes_update(schedule = a0, rounds = a1, state = a2, data = a3, n = a4, scratch = a5)`
and `vg_cmac_aes_finalize(key = a0, rounds = a1, state = a2, last = a3, last_len = a4, scratch = a5)`
(see `VG.Proof.Cmac.aesSubkeysContract` and the others), composed of calls of
the verified `vg_aes_encrypt_blocks` on one block in place, as on PPC64LE
(`VG.Impl.CmacAes.PPC64LE`).

The scratch buffer (2176 bytes) is laid out as AES-CBC's
(`VG.Impl.AesCbc.RISCV64`): `[0, 2048)` is the working space of
`vg_aes_encrypt_blocks`, and from `sv = scratch + 2048` rounded up to a
multiple of 8 (`savePtr`), `[sv + 16, sv + 72)` our return address (which
the call replaces) and the callee-saved registers we use. The contracts
state no alignment for the schedule, the subkeys, the state and the data, so
blocks are accessed a byte at a time.

* `subkeys` zeroes the first block of `subkeys` and enciphers it in place
  (`L = CIPH_K(0)`), keeping `subkeys` in `s1` and the scratch buffer in
  `s2` across the call, then doubles it there (`K1`) and into the second
  block (`K2`), a byte at a time (`VG.Impl.Cmac.RISCV64.dbl`): each byte shifted left by one bit,
  with the top bit of the next byte entering on the right, and the last
  byte XORed with `0x87` masked by the top bit of the first.
* `update` calls the CBC-MAC chain (`Impl.Aes.RISCV64.chain false`), whose
  arguments are the same and which bitslices the round keys once for all
  the blocks: each block, the state becomes `CIPH_K(C ⊕ Mᵢ)`. It gives the
  chain the first 2048 bytes of the scratch buffer, and saves its return
  address and `s1` above them, as `finalize` does.
* `finalize` XORs the last block `Mₙ` into the state as it forms it:
  `Mₙ* ⊕ K1` for a complete block, else `Mₙ*` a byte at a time, `0x80` after
  it, and `K2`. It then enciphers the state in place, keeping only the
  scratch buffer (in `s1`) across the call.

The branches are on `n`, on `last_len - 16` and on `last_len`. Only the
pointers, `rounds`, `n` and `last_len` can affect timing: the doubling is
masked.
-/

@[expose] public section

namespace VG.Impl.CmacAes.RISCV64

open VG.RISCV64 VG.Impl.Words.RISCV64
open VG.Impl.AesCbc.RISCV64 (mov savePtr xorInto advance whole encCall)
open VG.Impl.Cmac.RISCV64 (dbl)

/-! ## `vg_cmac_aes_subkeys` -/

/-- The registers `subkeys` saves, and their offsets from `sv`. -/
def skSaved : List (Reg × Nat) := [(.ra, 16), (.s1, 24), (.s2, 32)]

/-- Saves them (with the scratch buffer in `a3`), keeps `subkeys` in `s1`
and the scratch buffer in `s2`, zeroes the first block of `subkeys`, and
sets up the arguments of `vg_aes_encrypt_blocks` on it (the schedule and the
rounds are already in `a0` and `a1`). -/
def subkeysPre : List Instr :=
  savePtr .a3 ++ skSaved.map (fun (r, d) => .store .d r .t0 d) ++
    [mov .s1 .a2, mov .s2 .a3] ++ storeBytes .t1 .s1 0 (List.replicate 16 0) ++
    [mov .a2 .s1, .li .a3 1, mov .a4 .s2]

/-- `K1` over `L`, `K2` after it, and the registers restored (with the
scratch buffer in `s2`). -/
def subkeysPost : List Instr :=
  dbl 16 0x87 0 0 ++ dbl 16 0x87 0 16 ++ savePtr .s2 ++ skSaved.map (fun (r, d) => .load .d r .t0 d)

def subkeys : Prog isa := .seq (.block subkeysPre) (.seq encCall (.block subkeysPost))

/-! ## `vg_cmac_aes_update` -/

/-- The arguments of `vg_aes_encrypt_blocks` on the state: the schedule, the
rounds, the state, `n = 1`, and the working space. -/
def updArgs : List Instr := [mov .a0 .s1, mov .a1 .s2, mov .a2 .s3, .li .a3 1, mov .a4 .s6]

/-- The return address and `s1`, saved above the first 2048 bytes of the
scratch buffer (with the scratch buffer in `a5`), and the scratch buffer kept in `s1`. -/
def updSave : List Instr :=
  savePtr .a5 ++ [.store .d .ra .t0 16, .store .d .s1 .t0 24, mov .s1 .a5]

/-- They restored, with the scratch buffer in `s1`. -/
def updRestore : List Instr := savePtr .s1 ++ [.load .d .ra .t0 16, .load .d .s1 .t0 24]

/-- The blocks chained into the state by the CBC-MAC chain
(`Impl.Aes.RISCV64.chain false`), which takes `update`'s arguments and the
first 2048 bytes of its scratch buffer, and bitslices the round keys once
for all the blocks. -/
def update : Prog isa := .seq (.block updSave) (.seq Impl.Aes.RISCV64.macChainCall (.block updRestore))

/-! ## `vg_cmac_aes_finalize` -/

/-- The registers `finalize` saves, and their offsets from `sv`. -/
def finSaved : List (Reg × Nat) := [(.ra, 16), (.s1, 24)]

/-- Saves them (with the scratch buffer in `a5`), keeps the scratch buffer
in `s1`, and `last_len - 16` in `t1`. -/
def finSave : List Instr :=
  savePtr .a5 ++ finSaved.map (fun (r, d) => .store .d r .t0 d) ++ [mov .s1 .a5, .addi .t1 .a4 (-16)]

/-- `Mₙ* ⊕ K1` (`K1` at `a0 + 240`) XORed into the state, for a complete last
block. -/
def full : List Instr := xorInto .a2 .a3 ++ [.addi .t5 .a0 240] ++ xorInto .a2 .t5

/-- The `t1` (nonzero) bytes at `t5` XORed into `t6`, advancing both. -/
def xorLoop : Prog isa :=
  .loop (.block [.load .b .t3 .t5 0, .load .b .t4 .t6 0, .logic .xor .t3 .t3 .t4, .store .b .t3 .t6 0,
      .addi .t5 .t5 1, .addi .t6 .t6 1, .addi .t1 .t1 (-1)])
    (.nonzero .t1)

/-- `0x80` XORed into the byte after them (at `t6`), and the block XORed
with `K2` (at `a0 + 256`). -/
def padK2 : List Instr :=
  [.load .b .t3 .t6 0, .logicImm .xor .t3 .t3 0x80, .store .b .t3 .t6 0, .addi .t5 .a0 256] ++
    xorInto .a2 .t5

/-- `K2 ⊕ (Mₙ* ‖ 10ʲ)` XORed into the state, for a partial last block
(`last_len < 16`): the bytes at `last` (`t5`) into the state (`t6`), `t1`
counting them. -/
def partialBlock : Prog isa :=
  .seq (.block [mov .t5 .a3, mov .t6 .a2, mov .t1 .a4])
    (.seq (.ite (.zero .t1) (.block []) xorLoop) (.block padK2))

/-- Everything before the call: `C ⊕ Mₙ` in the state, and the arguments of
`vg_aes_encrypt_blocks` but the schedule (`a0`), the rounds (`a1`) and the
state (`a2`), which are ours. -/
def finPre : Prog isa :=
  .seq (.block finSave) (.seq (.ite (.zero .t1) (.block full) partialBlock) (.block [.li .a3 1, mov .a4 .s1]))

/-- The registers restored, with the scratch buffer in `s1`. -/
def finRestore : List Instr := savePtr .s1 ++ finSaved.map (fun (r, d) => .load .d r .t0 d)

def finalize : Prog isa := .seq finPre (.seq encCall (.block finRestore))

end VG.Impl.CmacAes.RISCV64
