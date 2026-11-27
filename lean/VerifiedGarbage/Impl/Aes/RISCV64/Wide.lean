module

public import VerifiedGarbage.Impl.Aes.RISCV64.Blocks
public import VerifiedGarbage.Impl.Aes.RISCV64.Chain

/-!
# AES modes four blocks at a time on RISC-V

CBC and CFB128 decryption and XTS, with the arguments of `vg_aes_ctr32`:
`chain`'s frame (`Chain.lean`) around a loop of groups of up to four blocks.
In each, `load k` for the group's blocks `k` puts the cipher's input into
the state registers, `crypt4` transforms the four, and `store k` makes the
data of them. A mode's chaining value, or tweak, is in the slots `stLo` and
`stLo + 1` across the loop, and what it keeps of the group's blocks in the
slots `blkLo k` and `blkLo k + 1`.
-/

@[expose] public section

namespace VG.Impl.Aes.RISCV64

open VG.RISCV64 VG.Impl.Words.RISCV64

def stLo : Nat := 78
def blkLo (k : Nat) : Nat := 80 + 2 * k

/-! ## The groups -/

def wideLoadFull (load : Nat → List Instr) : List Instr := (List.range 4).flatMap load

def wideLoadTail (load : Nat → List Instr) : Prog isa :=
  .seq (.block (load 0 ++ ([.addi t0 .a4 (-1)] : List Instr)))
    (.ite (.nonzero t0) (.seq (.block (load 1 ++ ([.addi t0 .a4 (-3)] : List Instr)))
        (.ite (.zero t0) (.block (load 2)) (.block [])))
      (.block []))

def wideStoreFull (store : Nat → List Instr) : List Instr :=
  (List.range 4).flatMap store ++ ([.addi .a3 .a3 64, .addi .a4 .a4 (-4)] : List Instr)

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

/-- One group, by doublewords if the data's address is a multiple of 8. -/
def wideGroupA (load store : Bool → Nat → List Instr) (crypt4 : Prog isa) : Prog isa :=
  .seq (.block [.logicImm .and t0 .a3 7])
    (.ite (.zero t0) (wideGroup (load true) (store true) crypt4)
      (wideGroup (load false) (store false) crypt4))

/-- The state between its registers and its slots. -/
def wideIn : List Instr := [stS stLo (q 0), stS (stLo + 1) (q 4)]
def wideOut : List Instr := [ldS (q 0) stLo, ldS (q 4) (stLo + 1)]

def wide (load store : Nat → List Instr) (crypt4 : Prog isa) : Prog isa :=
  chainFrame (wideGroup load store crypt4) wideIn wideOut

def wideA (load store : Bool → Nat → List Instr) (crypt4 : Prog isa) : Prog isa :=
  chainFrame (wideGroupA load store crypt4) wideIn wideOut

/-! ## CBC decryption -/

def cbcLoad (w : Bool) (k : Nat) : List Instr :=
  loadBlock w k ++ [stS (blkLo k) (q k), stS (blkLo k + 1) (q (k + 4))]

/-- The slots of the ciphertext block before block `k`. -/
def cbcPrev (k : Nat) : Nat := if k = 0 then stLo else blkLo (k - 1)

def cbcStore (w : Bool) (k : Nat) : List Instr :=
  [ldS .t2 (cbcPrev k), xorR .t2 .t2 (q k)] ++ storeLE64W w .t2 t0 t1 .a3 (16 * k) ++
    [ldS .t2 (cbcPrev k + 1), xorR .t2 .t2 (q (k + 4))] ++ storeLE64W w .t2 t0 t1 .a3 (16 * k + 8) ++
    [ldS .t2 (blkLo k), stS stLo .t2, ldS .t2 (blkLo k + 1), stS (stLo + 1) .t2]

def cbcDecWide : Prog isa := wideA cbcLoad cbcStore decrypt4
def cbcDecWideCall : Prog isa := .call "vg_aes_cbc_dec_wide" cbcDecWide

/-! ## CFB128 decryption -/

/-- The ciphertext block before block `k` (the state before the first). -/
def cfbLoad (k : Nat) : List Instr :=
  if k = 0 then [ldS (q k) stLo, ldS (q (k + 4)) (stLo + 1)]
  else loadLE64 (q k) t0 t1 .a3 (16 * (k - 1)) ++ loadLE64 (q (k + 4)) t0 t1 .a3 (16 * (k - 1) + 8)

def cfbStore (k : Nat) : List Instr :=
  loadLE64 .t2 t0 t1 .a3 (16 * k) ++ [stS stLo .t2, xorR .t2 .t2 (q k)] ++
    storeLE64 .t2 t0 t1 .a3 (16 * k) ++
    loadLE64 .t2 t0 t1 .a3 (16 * k + 8) ++ [stS (stLo + 1) .t2, xorR .t2 .t2 (q (k + 4))] ++
    storeLE64 .t2 t0 t1 .a3 (16 * k + 8)

def cfbDecWide : Prog isa := wide cfbLoad cfbStore encrypt4
def cfbDecWideCall : Prog isa := .call "vg_aes_cfb_dec_wide" cfbDecWide

/-! ## XTS -/

/-- The tweak times `α`. -/
def xtsMulA : List Instr :=
  [ldS t0 stLo, ldS t1 (stLo + 1), shrI .t2 t1 63, .li .t3 0, .sub .t2 .t3 .t2, .li .t3 0x87,
   andR .t2 .t2 .t3, shrI .t3 t0 63, shlI t0 t0 1, xorR t0 t0 .t2, shlI t1 t1 1, .logic .or t1 t1 .t3,
   stS stLo t0, stS (stLo + 1) t1]

/-- Block `k` XORed with its tweak, which is kept; the next tweak. -/
def xtsLoad (w : Bool) (k : Nat) : List Instr :=
  [ldS .t2 stLo, stS (blkLo k) .t2] ++ loadLE64W w (q k) t0 t1 .a3 (16 * k) ++
    [xorR (q k) (q k) .t2, ldS .t2 (stLo + 1), stS (blkLo k + 1) .t2] ++
    loadLE64W w (q (k + 4)) t0 t1 .a3 (16 * k + 8) ++ [xorR (q (k + 4)) (q (k + 4)) .t2] ++ xtsMulA

def xtsStore (w : Bool) (k : Nat) : List Instr :=
  [ldS .t2 (blkLo k), xorR .t2 .t2 (q k)] ++ storeLE64W w .t2 t0 t1 .a3 (16 * k) ++
    [ldS .t2 (blkLo k + 1), xorR .t2 .t2 (q (k + 4))] ++ storeLE64W w .t2 t0 t1 .a3 (16 * k + 8)

def xtsEncWide : Prog isa := wideA xtsLoad xtsStore encrypt4
def xtsDecWide : Prog isa := wideA xtsLoad xtsStore decrypt4
def xtsEncWideCall : Prog isa := .call "vg_aes_xts_enc_wide" xtsEncWide
def xtsDecWideCall : Prog isa := .call "vg_aes_xts_dec_wide" xtsDecWide

end VG.Impl.Aes.RISCV64
