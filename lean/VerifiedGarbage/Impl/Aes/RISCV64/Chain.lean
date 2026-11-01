module

public import VerifiedGarbage.Impl.Aes.RISCV64.Ctr32

/-!
# AES chaining (CBC encryption, CBC-MAC), bitsliced, on RISC-V

`chain out` is a function with the arguments of `vg_aes_ctr32`,
`(schedule = a0, rounds = a1, state = a2, data = a3, n = a4, scratch = a5)`,
that chains the `n` blocks at `data` into the 16-byte state at `state`:
for each block `Mᵢ`, `C := CIPH_K(C ⊕ Mᵢ)`, and, if `out`, `Mᵢ := C` in
place. So `chain false` is the CBC-MAC update of `vg_cmac_aes_update`, and
`chain true` is `vg_aes_cbc_encrypt`, whose chaining value is the state.

It is `vg_aes_ctr32`'s code (`Ctr32.lean`) with another group loop: the
prologue (`roundSb`, `saveRegs`, `maskInit`) and the key loop, which
bitslices the round keys once into the scratch buffer, are the same; the
return address is kept in slot `raSlot` and the state's address in `ra`
(which neither the key loop nor `encrypt4` writes; a register, so that its
taint stays public), and the state itself, loaded
little-endian a byte at a time (its alignment, and the data's, the
contracts do not state), in the registers of block 0 (`q 0` and `q 4`)
across the loop. Each block is XORed into them and `encrypt4` encrypts
them, with the other three blocks' registers holding whatever they hold
(the blocks are independent: each column of the bitsliced state is one
block's). Bitslicing the round keys once rather than once a block is the
point: `vg_aes_encrypt_blocks` on one block costs as much as on four, plus
that.

With no blocks the function does nothing. Only `a0`, `a1` (`kp`), `a3` (the
data), `a4` (the blocks left), `a5`, `ra` (the state's address) and what is computed from them in `t0`
for the branches hold public values; no address and no branch depends on
anything else.
-/

@[expose] public section

namespace VG.Impl.Aes.RISCV64

open VG.RISCV64 VG.Impl.Words.RISCV64

/-- The slot of the return address, while `ra` holds the state's address. -/
def raSlot : Nat := 62

/-- The state (at `ra`) into the registers of block 0. -/
def chainLoad : List Instr := loadLE64 (q 0) t0 t1 .ra 0 ++ loadLE64 (q 4) t0 t1 .ra 8

/-- The data block at `a3` XORed into them. -/
def chainXor : List Instr :=
  loadLE64 .t2 t0 t1 .a3 0 ++ [xorR (q 0) (q 0) .t2] ++ loadLE64 .t2 t0 t1 .a3 8 ++
    [xorR (q 4) (q 4) .t2]

/-- The new state stored over the data block (CBC encryption's ciphertext). -/
def chainOut : List Instr := storeLE64 (q 0) t0 t1 .a3 0 ++ storeLE64 (q 4) t0 t1 .a3 8

/-- On to the next block. -/
def chainNext : List Instr := [.addi .a3 .a3 16, .addi .a4 .a4 (-1)]

/-- One block: XORed into the state, which is encrypted (and, if `out`,
stored over the block). -/
def chainBody (out : Bool) : Prog isa :=
  .seq (.block chainXor) (.seq encrypt4 (.block ((if out then chainOut else []) ++ chainNext)))

/-- The state stored back (at `ra`), and the return address restored. -/
def chainStore : List Instr :=
  storeLE64 (q 0) t0 t1 .ra 0 ++ storeLE64 (q 4) t0 t1 .ra 8 ++ [ldS .ra raSlot]

/-- The `n` blocks at `data` chained into the state, as above. -/
def chain (out : Bool) : Prog isa :=
  .ite (.zero .a4) (.block [])
    (.seq (.block (roundSb ++ saveRegs ++ maskInit ++ [stS raSlot .ra, movR .ra .a2] ++ keySetup))
      (.seq (.loop (.block keyBody) (.nonzero .a1))
        (.seq (.block (keyDone ++ chainLoad))
          (.seq (.loop (chainBody out) (.nonzero .a4))
            (.block (chainStore ++ restoreRegs))))))

/-- A call of the CBC-MAC chain, `vg_cmac_aes_update`'s, an internal function. -/
def macChainCall : Prog isa := .call "vg_aes_mac_chain" (chain false)

/-- A call of the CBC encryption chain, `vg_aes_cbc_encrypt`'s, an internal
function. -/
def cbcChainCall : Prog isa := .call "vg_aes_cbc_chain" (chain true)

end VG.Impl.Aes.RISCV64
