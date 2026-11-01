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

/-- `chain`'s frame around a loop of `body`, with `pre` after the state is
loaded and `post` before it is stored. -/
def chainFrame (body : Prog isa) (pre post : List Instr) : Prog isa :=
  .ite (.zero .a4) (.block [])
    (.seq (.block (roundSb ++ saveRegs ++ maskInit ++ [stS raSlot .ra, movR .ra .a2] ++ keySetup))
      (.seq (.loop (.block keyBody) (.nonzero .a1))
        (.seq (.block (keyDone ++ chainLoad ++ pre))
          (.seq (.loop body (.nonzero .a4))
            (.block (post ++ chainStore ++ restoreRegs))))))

/-- The `n` blocks at `data` chained into the state, as above. -/
def chain (out : Bool) : Prog isa := chainFrame (chainBody out) [] []

/-- A call of the CBC-MAC chain, `vg_cmac_aes_update`'s, an internal function. -/
def macChainCall : Prog isa := .call "vg_aes_mac_chain" (chain false)

/-- A call of the CBC encryption chain, `vg_aes_cbc_encrypt`'s, an internal
function. -/
def cbcChainCall : Prog isa := .call "vg_aes_cbc_chain" (chain true)

/-! ## The other chaining modes

The same frame as `chain` (`chainFrame`: the prologue, the key loop, the
state loaded from `ra` into block 0's registers, a loop of `body` while
blocks or bytes are left in `a4`, the state stored back) with other bodies: AES-CFB128
encryption and AES-OFB per block, and AES-CFB8 per byte. -/

/-- AES-CFB128 encryption, one block: `Cⱼ = Pⱼ ⊕ CIPH_K(Cⱼ₋₁)`, stored over
`Pⱼ`, and the state. -/
def cfbBody : Prog isa := .seq encrypt4 (.block (chainXor ++ chainOut ++ chainNext))

/-- The data block at `a3` XORed with the state (through `t2`), in place. -/
def ofbXor : List Instr :=
  loadLE64 .t2 t0 t1 .a3 0 ++ [xorR .t2 .t2 (q 0)] ++ storeLE64 .t2 t0 t1 .a3 0 ++
    loadLE64 .t2 t0 t1 .a3 8 ++ [xorR .t2 .t2 (q 4)] ++ storeLE64 .t2 t0 t1 .a3 8

/-- AES-OFB, one block: `Oⱼ = CIPH_K(Oⱼ₋₁)`, the state, XORed into the data
block. -/
def ofbBody : Prog isa := .seq encrypt4 (.block (ofbXor ++ chainNext))

def cfbChain : Prog isa := chainFrame cfbBody [] []
def ofbChain : Prog isa := chainFrame ofbBody [] []

/-- The slots of AES-CFB8's input block, bytes 0–7 and 8–15 (little-endian),
which `encrypt4` would overwrite in the registers. -/
def iLo : Nat := 58
def iHi : Nat := 63

/-- The input block shifted left by a byte, with the ciphertext byte in `t2`
shifted in, in its slots; on to the next byte. -/
def cfb8Shift : List Instr :=
  [ldS t0 iLo, ldS t1 iHi, shrI t0 t0 8, shlI .t3 t1 56, .logic .or t0 t0 .t3,
    shrI t1 t1 8, shlI .t3 .t2 56, .logic .or t1 t1 .t3, stS iLo t0, stS iHi t1,
    .addi .a3 .a3 1, .addi .a4 .a4 (-1)]

/-- `C#ⱼ = P#ⱼ ⊕ MSB₈(Oⱼ)` stored over `P#ⱼ`, and in `t2`. -/
def cfb8Enc : List Instr :=
  [.load .b .t2 .a3 0, .logicImm .and t1 (q 0) 255, xorR .t2 .t2 t1, .store .b .t2 .a3 0]

/-- `P#ⱼ = C#ⱼ ⊕ MSB₈(Oⱼ)` stored over `C#ⱼ`, which stays in `t2`. -/
def cfb8Dec : List Instr :=
  [.load .b .t2 .a3 0, .logicImm .and t1 (q 0) 255, xorR t1 t1 .t2, .store .b t1 .a3 0]

/-- AES-CFB8, one byte: the input block from its slots, enciphered, its
first byte XORed with the data byte, and the input block shifted. -/
def cfb8Body (enc : Bool) : Prog isa :=
  .seq (.block [ldS (q 0) iLo, ldS (q 4) iHi])
    (.seq encrypt4 (.block ((if enc then cfb8Enc else cfb8Dec) ++ cfb8Shift)))

/-- AES-CFB8 over the `a4` bytes at `a3`, the input block kept in its
slots and stored back to the state. -/
def cfb8Chain (enc : Bool) : Prog isa :=
  chainFrame (cfb8Body enc) [stS iLo (q 0), stS iHi (q 4)] [ldS (q 0) iLo, ldS (q 4) iHi]

def cfbChainCall : Prog isa := .call "vg_aes_cfb_chain" cfbChain
def ofbChainCall : Prog isa := .call "vg_aes_ofb_chain" ofbChain
def cfb8EncChainCall : Prog isa := .call "vg_aes_cfb8_enc_chain" (cfb8Chain true)
def cfb8DecChainCall : Prog isa := .call "vg_aes_cfb8_dec_chain" (cfb8Chain false)

end VG.Impl.Aes.RISCV64
