module

public import VerifiedGarbage.Impl.Aes.RISCV64.Chain
public import VerifiedGarbage.Impl.Aes.RISCV64.Blocks

/-!
# AES modes four blocks at a time, bitsliced, on RISC-V

The modes whose blocks can be enciphered independently, once the inputs of
the block cipher are known: AES-CBC decryption, AES-CFB128 decryption and
XTS-AES, with the arguments of `vg_aes_ctr32`,
`(schedule = a0, rounds = a1, state = a2, data = a3, n = a4, scratch = a5)`,
where the state is the chaining value (CBC, CFB) or the tweak (XTS), as
`chain`'s (`Chain.lean`).

`wide load store crypt4` is `chainFrame` (the prologue, the key loop, which
bitslices the round keys once, the state at `ra`, which is loaded and stored
back) around a loop of groups of up to four blocks, as `vg_aes_ctr32`'s and
`vg_aes_encrypt_blocks`' (`Blocks.lean`): `load b` for each block `b` of the
group puts the input of the block cipher in `q b` and `q (b + 4)`, `crypt4`
(`encrypt4` or `decrypt4`) enciphers or deciphers the four, and `store b`
writes the data block `b`. The state is kept in two scratch slots
(`stLo`, `stLo + 1`) across the loop, and each mode's blocks in others, at
slots 80–97, all below the bitsliced round keys (slot 128 on):

* CBC decryption: `load` copies the ciphertext block `Cⱼ` to its slots and
  into the registers; `store` XORs the deciphered block with `Cⱼ₋₁` (the
  state for the first, the previous block's copy otherwise), and makes `Cⱼ`
  the state.
* CFB128 decryption: `load` puts `Cⱼ₋₁` (the state, or the data block before,
  not yet overwritten) in the registers; `store` makes `Cⱼ` the state and
  XORs `CIPH_K(Cⱼ₋₁)` into it.
* XTS: `load` keeps the tweak `Tⱼ` in the block's slots, XORs it into the
  data block in the registers, and multiplies the tweak by `α` (`xtsMulA`,
  on its two 64-bit little-endian words); `store` XORs `Tⱼ` into the result.

With no blocks the function does nothing. Only `a0`, `a1` (`kp`), `a3` (the
data), `a4` (the blocks left), `a5`, `ra` (the state's address) and what is
computed from them in `t0` for the branches hold public values; no address
and no branch depends on anything else.
-/

@[expose] public section

namespace VG.Impl.Aes.RISCV64

open VG.RISCV64 VG.Impl.Words.RISCV64

/-- The slots of the state across the loop. -/
def stLo : Nat := 78

/-- The two slots of block `b`'s copy (CBC) or tweak (XTS). -/
def blkLo (b : Nat) : Nat := 80 + 2 * b

/-- The state into its slots, from the registers `chainLoad` loads it to. -/
def wideIn : List Instr := [stS stLo (q 0), stS (stLo + 1) (q 4)]

/-- The state from its slots into the registers `chainStore` stores. -/
def wideOut : List Instr := [ldS (q 0) stLo, ldS (q 4) (stLo + 1)]

/-- Four blocks loaded. -/
def wideLoadFull (load : Nat → List Instr) : List Instr := (List.range 4).flatMap load

/-- The last one to three blocks loaded. -/
def wideLoadTail (load : Nat → List Instr) : Prog isa :=
  .seq (.block (load 0 ++ ([.addi t0 .a4 (-1)] : List Instr)))
    (.ite (.nonzero t0) (.seq (.block (load 1 ++ ([.addi t0 .a4 (-3)] : List Instr)))
        (.ite (.zero t0) (.block (load 2)) (.block [])))
      (.block []))

/-- Four blocks stored, and on to the next four. -/
def wideStoreFull (store : Nat → List Instr) : List Instr :=
  (List.range 4).flatMap store ++ ([.addi .a3 .a3 64, .addi .a4 .a4 (-4)] : List Instr)

/-- The last one to three blocks stored (and none left). -/
def wideStoreTail (store : Nat → List Instr) : Prog isa :=
  .seq (.block (store 0 ++ ([.addi t0 .a4 (-1)] : List Instr)))
    (.seq (.ite (.nonzero t0) (.seq (.block (store 1 ++ ([.addi t0 .a4 (-3)] : List Instr)))
        (.ite (.zero t0) (.block (store 2)) (.block [])))
      (.block []))
    (.block [.li .a4 0]))

/-- One group of (up to) four blocks. -/
def wideGroup (load store : Nat → List Instr) (crypt4 : Prog isa) : Prog isa :=
  .seq (.block [shrI t0 .a4 2])
    (.seq (.ite (.nonzero t0) (.block (wideLoadFull load)) (wideLoadTail load))
      (.seq crypt4
        (.seq (.block [shrI t0 .a4 2])
          (.ite (.nonzero t0) (.block (wideStoreFull store)) (wideStoreTail store)))))

/-- The `n` blocks at `data`, four at a time, as above. -/
def wide (load store : Nat → List Instr) (crypt4 : Prog isa) : Prog isa :=
  chainFrame (wideGroup load store crypt4) wideIn wideOut

/-! ## AES-CBC decryption -/

/-- `Cⱼ` (block `b`) loaded, and copied to its slots. -/
def cbcLoad (b : Nat) : List Instr :=
  loadBlock b ++ [stS (blkLo b) (q b), stS (blkLo b + 1) (q (b + 4))]

/-- The slots of `Cⱼ₋₁` for block `b`: the state for the first block. -/
def cbcPrev (b : Nat) : Nat := if b = 0 then stLo else blkLo (b - 1)

/-- `Pⱼ = CIPH⁻¹_K(Cⱼ) ⊕ Cⱼ₋₁` stored; `Cⱼ` the state. -/
def cbcStore (b : Nat) : List Instr :=
  [ldS .t2 (cbcPrev b), xorR .t2 .t2 (q b)] ++ storeLE64 .t2 t0 t1 .a3 (16 * b) ++
    [ldS .t2 (cbcPrev b + 1), xorR .t2 .t2 (q (b + 4))] ++ storeLE64 .t2 t0 t1 .a3 (16 * b + 8) ++
    [ldS .t2 (blkLo b), stS stLo .t2, ldS .t2 (blkLo b + 1), stS (stLo + 1) .t2]

def cbcDecWide : Prog isa := wide cbcLoad cbcStore decrypt4

/-! ## AES-CFB128 decryption -/

/-- `Cⱼ₋₁` for block `b` into the registers: the state for the first block,
the data block before it (not yet overwritten) otherwise. -/
def cfbLoad (b : Nat) : List Instr :=
  if b = 0 then [ldS (q 0) stLo, ldS (q 4) (stLo + 1)]
  else loadLE64 (q b) t0 t1 .a3 (16 * (b - 1)) ++ loadLE64 (q (b + 4)) t0 t1 .a3 (16 * (b - 1) + 8)

/-- `Cⱼ` the state, and `Pⱼ = Cⱼ ⊕ CIPH_K(Cⱼ₋₁)` stored over it. -/
def cfbStore (b : Nat) : List Instr :=
  loadLE64 .t2 t0 t1 .a3 (16 * b) ++ [stS stLo .t2, xorR .t2 .t2 (q b)] ++
    storeLE64 .t2 t0 t1 .a3 (16 * b) ++
    loadLE64 .t2 t0 t1 .a3 (16 * b + 8) ++ [stS (stLo + 1) .t2, xorR .t2 .t2 (q (b + 4))] ++
    storeLE64 .t2 t0 t1 .a3 (16 * b + 8)

def cfbDecWide : Prog isa := wide cfbLoad cfbStore encrypt4

/-! ## XTS-AES -/

/-- The tweak in its slots (low and high little-endian words) times `α`:
shifted left by one bit, and the low word XORed with `0x87` if the top bit
was set (a mask from `0 − (hi >> 63)`). -/
def xtsMulA : List Instr :=
  [ldS t0 stLo, ldS t1 (stLo + 1), shrI .t2 t1 63, .li .t3 0, .sub .t2 .t3 .t2, .li .t3 0x87,
    .logic .and .t2 .t2 .t3, shrI .t3 t0 63, shlI t0 t0 1, xorR t0 t0 .t2, shlI t1 t1 1,
    .logic .or t1 t1 .t3, stS stLo t0, stS (stLo + 1) t1]

/-- Block `b` loaded and XORed with its tweak `Tⱼ`, which is kept in its
slots, and the tweak times `α`. -/
def xtsLoad (b : Nat) : List Instr :=
  [ldS .t2 stLo, stS (blkLo b) .t2] ++ loadLE64 (q b) t0 t1 .a3 (16 * b) ++ [xorR (q b) (q b) .t2,
    ldS .t2 (stLo + 1), stS (blkLo b + 1) .t2] ++ loadLE64 (q (b + 4)) t0 t1 .a3 (16 * b + 8) ++
    [xorR (q (b + 4)) (q (b + 4)) .t2] ++ xtsMulA

/-- The result XORed with `Tⱼ`, stored. -/
def xtsStore (b : Nat) : List Instr :=
  [ldS .t2 (blkLo b), xorR .t2 .t2 (q b)] ++ storeLE64 .t2 t0 t1 .a3 (16 * b) ++
    [ldS .t2 (blkLo b + 1), xorR .t2 .t2 (q (b + 4))] ++ storeLE64 .t2 t0 t1 .a3 (16 * b + 8)

def xtsEncWide : Prog isa := wide xtsLoad xtsStore encrypt4
def xtsDecWide : Prog isa := wide xtsLoad xtsStore decrypt4

def cbcDecWideCall : Prog isa := .call "vg_aes_cbc_dec_wide" cbcDecWide
def cfbDecWideCall : Prog isa := .call "vg_aes_cfb_dec_wide" cfbDecWide
def xtsEncWideCall : Prog isa := .call "vg_aes_xts_enc_wide" xtsEncWide
def xtsDecWideCall : Prog isa := .call "vg_aes_xts_dec_wide" xtsDecWide

end VG.Impl.Aes.RISCV64
