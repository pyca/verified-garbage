module

public import VerifiedGarbage.Impl.Aes.RISCV64.Blocks
public import VerifiedGarbage.Impl.Aes.RISCV64.Chain
public import VerifiedGarbage.Impl.Words.RISCV64.XorBytes

/-!
# AES-CBC: RISC-V implementation

`vg_aes_cbc_encrypt(schedule = a0, rounds = a1, iv = a2, data = a3, n = a4, scratch = a5)`
and `vg_aes_cbc_decrypt` with the same arguments (see
`VG.Spec.Cbc.aesEncryptContract` and `aesDecryptContract`), composed of a call
of the CBC encryption chain, or of calls of the verified
`vg_aes_decrypt_blocks` on one block at a time, in place, as on PPC64LE (`VG.Impl.AesCbc.PPC64LE`).

The scratch buffer (2176 bytes): `[0, 2048)` is the working space of the
block function. Above it, from `sv = scratch + 2048` rounded up to a
multiple of 8 (`savePtr`, at most `scratch + 2055`): `[sv, sv + 16)` the
ciphertext block that decryption keeps across the call, and `[sv + 16,
sv + 72)` our return address (which each call replaces) and our caller's
`s1`–`s6`. Load and store offsets are below 2048, so `sv` is computed into
`t0` whenever it is used.

Both keep their arguments in `s1` (schedule), `s2` (rounds), `s3` (the
chaining value), `s4` (the next block), `s5` (blocks left) and `s6`
(scratch) across the calls, which preserve them. The contracts state no
alignment for the chaining value and the data, so blocks are XORed and
copied a byte at a time, through `t3` and `t4`.

* `encrypt` calls the CBC encryption chain (`Impl.Aes.RISCV64.chain true`),
  whose arguments are the same and which bitslices the round keys once for
  all the blocks: each block becomes `CIPH_K(Pⱼ ⊕ Cⱼ₋₁)`, in place, and the
  chaining value; it gives the chain the first 2048 bytes of the scratch
  buffer, and saves its return address and `s1` above them.
* `decrypt`, each block: `Cⱼ` saved in the scratch buffer, deciphered in
  place, XORed with the chaining value `Cⱼ₋₁`, and the saved `Cⱼ` copied to
  the chaining value.

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

/-- The arguments of the block function for the block at `s4`: the
schedule, the rounds, the block, `n = 1`, and the working space. -/
def callArgs : List Instr := [mov .a0 .s1, mov .a1 .s2, mov .a2 .s4, .li .a3 1, mov .a4 .s6]

/-- The block at `dst` XORed with the block at `src`, in place. -/
def xorInto (dst src : Reg) : List Instr := xorBytes .t3 .t4 dst src 16

/-- The block at `src` copied to `dst`. -/
def copy (dst src : Reg) : List Instr := copyBytes .t3 src dst 0 0 16

/-- On to the next block. -/
def advance : List Instr := [.addi .s4 .s4 16, .addi .s5 .s5 (-1)]

/-- The registers saved and the arguments set up, `body` run once for each
block, and the registers restored. -/
def whole (body : Prog isa) : Prog isa :=
  .seq (.block (save ++ setup))
    (.seq (.ite (.zero .s5) (.block []) (.loop body (.nonzero .s5))) (.block restore))

/-- A call of `vg_aes_encrypt_blocks`. -/
def encCall : Prog isa := .call "vg_aes_encrypt_blocks" Impl.Aes.RISCV64.encryptBlocks

/-- A call of `vg_aes_decrypt_blocks`. -/
def decCall : Prog isa := .call "vg_aes_decrypt_blocks" Impl.Aes.RISCV64.decryptBlocks

/-! ## `vg_aes_cbc_encrypt` -/

/-- The return address and `s1`, saved above the first 2048 bytes of the
scratch buffer (with the scratch buffer in `a5`), and the scratch buffer kept in `s1`. -/
def encSave : List Instr :=
  savePtr .a5 ++ [.store .d .ra .t0 16, .store .d .s1 .t0 24, mov .s1 .a5]

/-- They restored, with the scratch buffer in `s1`. -/
def encRestore : List Instr := savePtr .s1 ++ [.load .d .ra .t0 16, .load .d .s1 .t0 24]

/-- Each block `Pⱼ ⊕ Cⱼ₋₁`, enciphered in place, the result the chaining
value, by the CBC encryption chain (`Impl.Aes.RISCV64.chain true`), which
takes `encrypt`'s arguments and the first 2048 bytes of its scratch buffer,
and bitslices the round keys once for all the blocks. -/
def encrypt : Prog isa := .seq (.block encSave) (.seq Impl.Aes.RISCV64.cbcChainCall (.block encRestore))

/-! ## `vg_aes_cbc_decrypt` -/

/-- One block: `Cⱼ` saved, deciphered, XORed with `Cⱼ₋₁`, and the saved
`Cⱼ` the chaining value. -/
def decBody : Prog isa :=
  .seq (.block (savePtr .s6 ++ copy .t0 .s4 ++ callArgs))
    (.seq decCall (.block (xorInto .s4 .s3 ++ savePtr .s6 ++ copy .s3 .t0 ++ advance)))

def decrypt : Prog isa := whole decBody

end VG.Impl.AesCbc.RISCV64
