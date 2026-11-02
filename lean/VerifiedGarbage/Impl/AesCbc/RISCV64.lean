module

public import VerifiedGarbage.Impl.Aes.RISCV64.Blocks
public import VerifiedGarbage.Impl.Aes.RISCV64.Chain
public import VerifiedGarbage.Impl.Aes.RISCV64.Wide
public import VerifiedGarbage.Impl.Words.RISCV64.XorBytes

/-!
# AES-CBC: RISC-V implementation

`vg_aes_cbc_encrypt(schedule = a0, rounds = a1, iv = a2, data = a3, n = a4, scratch = a5)`
and `vg_aes_cbc_decrypt` with the same arguments (see
`VG.Spec.Cbc.aesEncryptContract` and `aesDecryptContract`): each a call of a
function that takes the same arguments and the first 2048 bytes of the
scratch buffer (2176 bytes), and bitslices the round keys once for all the
blocks (`chainWrapped`), between saving and restoring our return address
and `s1` above those 2048 bytes, at `sv = scratch + 2048` rounded up to a
multiple of 8 (`savePtr`; load and store offsets are below 2048, so `sv` is
computed into `t0` whenever it is used):

* `encrypt` calls the CBC encryption chain (`Impl.Aes.RISCV64.chain true`,
  `Impl/Aes/RISCV64/Chain.lean`): each block becomes `CIPH_K(Pⱼ ⊕ Cⱼ₋₁)`, in
  place, and the chaining value.
* `decrypt` calls the wide CBC decryption (`Impl.Aes.RISCV64.cbcDecWide`,
  `Impl/Aes/RISCV64/Wide.lean`), four blocks at a time: each block becomes
  `CIPH⁻¹_K(Cⱼ) ⊕ Cⱼ₋₁`, in place, and the last `Cⱼ` the chaining value.

The other pieces are for the RISC-V modes built on calls of
`vg_aes_encrypt_blocks` one block at a time (AES-CTR, AES-CMAC): `whole`
saves the return address and our caller's `s1`–`s6` at `sv + 16`, keeps the
arguments in `s1` (schedule), `s2` (rounds), `s3` (the chaining value or
counter), `s4` (the next block), `s5` (blocks left) and `s6` (scratch) across
the calls, which preserve them, runs a body once for each block, and
restores them; `xorInto` XORs a block into another a byte at a time.

Only the pointers, `rounds` and `n` can affect timing: the only branches are
on `n`.
-/

@[expose] public section

namespace VG.Impl.AesCbc.RISCV64

open VG.RISCV64 VG.Impl.Words.RISCV64

/-- `mv d, n` (`addi d, n, 0`). -/
def mov (d n : Reg) : Instr := .addi d n 0

/-- `t0 :=` `n + 2048` rounded up to a multiple of 8 (`(n + 2055) & -8`). -/
def savePtr (n : Reg) : List Instr := [.addi .t0 n 2047, .addi .t0 .t0 8, .logicImm .and .t0 .t0 (-8)]

/-- Our return address and our caller's registers, and their offsets from `sv`. -/
def saved : List (Reg × Nat) :=
  [(.ra, 16), (.s1, 24), (.s2, 32), (.s3, 40), (.s4, 48), (.s5, 56), (.s6, 64)]

/-- Saves them, with the scratch buffer in `a5`. -/
def save : List Instr := savePtr .a5 ++ saved.map fun (r, d) => .store .d r .t0 d

/-- The arguments to their registers. -/
def setup : List Instr :=
  [mov .s1 .a0, mov .s2 .a1, mov .s3 .a2, mov .s4 .a3, mov .s5 .a4, mov .s6 .a5]

/-- Restores them, with the scratch buffer in `s6`. -/
def restore : List Instr := savePtr .s6 ++ saved.map fun (r, d) => .load .d r .t0 d

/-- The block at `dst` XORed with the block at `src`, in place. -/
def xorInto (dst src : Reg) : List Instr := xorBytes .t3 .t4 dst src 16

/-- The block at `src` copied to `dst`. -/
def copy (dst src : Reg) : List Instr := copyBytes .t3 src dst 0 0 16

/-- The registers saved and the arguments set up, `body` run once for each
block, and the registers restored. -/
def whole (body : Prog isa) : Prog isa :=
  .seq (.block (save ++ setup))
    (.seq (.ite (.zero .s5) (.block []) (.loop body (.nonzero .s5))) (.block restore))

/-- A call of `vg_aes_encrypt_blocks`. -/
def encCall : Prog isa := .call "vg_aes_encrypt_blocks" Impl.Aes.RISCV64.encryptBlocks

/-! ## `vg_aes_cbc_encrypt` -/

/-- The return address and `s1`, saved above the first 2048 bytes of the
scratch buffer (with the scratch buffer in `a5`), and the scratch buffer kept in `s1`. -/
def encSave : List Instr :=
  savePtr .a5 ++ [.store .d .ra .t0 16, .store .d .s1 .t0 24, mov .s1 .a5]

/-- They restored, with the scratch buffer in `s1`. -/
def encRestore : List Instr := savePtr .s1 ++ [.load .d .ra .t0 16, .load .d .s1 .t0 24]

/-- A call `c` of a chaining or wide function (`Impl/Aes/RISCV64/Chain.lean`,
`Wide.lean`), which
takes our arguments and the first 2048 bytes of the scratch buffer, between
`encSave` and `encRestore`. -/
def chainWrapped (c : Prog isa) : Prog isa := .seq (.block encSave) (.seq c (.block encRestore))

/-- Each block `Pⱼ ⊕ Cⱼ₋₁`, enciphered in place, the result the chaining
value, by the CBC encryption chain (`Impl.Aes.RISCV64.chain true`), which
takes `encrypt`'s arguments and the first 2048 bytes of its scratch buffer,
and bitslices the round keys once for all the blocks. -/
def encrypt : Prog isa := chainWrapped Impl.Aes.RISCV64.cbcChainCall

/-! ## `vg_aes_cbc_decrypt` -/

/-- Four blocks at a time, by the wide CBC decryption
(`Impl.Aes.RISCV64.cbcDecWide`), which bitslices the round keys once. -/
def decrypt : Prog isa := chainWrapped Impl.Aes.RISCV64.cbcDecWideCall

end VG.Impl.AesCbc.RISCV64
