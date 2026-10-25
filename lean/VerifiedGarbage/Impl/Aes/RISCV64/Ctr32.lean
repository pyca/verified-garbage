module

public import VerifiedGarbage.Impl.Aes.RISCV64.Inv
public import VerifiedGarbage.Impl.Words.RISCV64.Bytes
public import VerifiedGarbage.Impl.Words64.RISCV64

/-!
# AES counter mode (GCM's `inc₃₂`), bitsliced, on RISC-V

`vg_aes_ctr32(schedule = a0, rounds = a1, counter = a2, data = a3, n = a4, scratch = a5)`.

Constant-time AES in the style of BearSSL's `aes_ct64` (Thomas Pornin, MIT
licence): four blocks at a time, bitsliced in eight 64-bit registers
(`Linear.lean`, `Sbox.lean`), as on PPC64LE (`Impl/Aes/PPC64LE/Ctr32.lean`).

* `scratch` is rounded up to a multiple of 8 (`roundSb`), which leaves 255
  slots of it, so that the slots are accessed aligned. The schedule, the
  counter block and the data, whose alignment the contract does not state,
  are accessed a byte at a time.
* The callee-saved registers `s0`–`s11` are saved in slots 40–51, the masks
  of the linear layers are built in slots 52–57 and 64–75 (`maskInit`), and
  the counter block is kept in slots 59–61: bytes 0–7, bytes 8–11 (the high
  half zero, later each counter block's last four bytes, stored
  big-endian) and the 32-bit counter as an integer.
* The final counter `inc₃₂ⁿ(CB₁)` is written first.
* The round keys are bitsliced once, into slots `128 + 8 (j + 14 - rounds)`
  for round `j`, so that the last is always at slot 240 (byte 1920). The
  loop runs from the last round key down, counting `rounds + 1` keys in
  `a1`, with `a0` at the round key of the schedule and `a2` at its
  bitsliced form.
* Each group of four blocks: build the counter blocks, bitslice them,
  encrypt (the round loop runs `kp` over the round keys until the last but
  one, the first at `a0`), un-bitslice, and XOR the keystream into the
  data, four blocks or the remaining one to three.
* Only `a0`, `a1` (`kp`), `a2`, `a3` (the data), `a4` (the blocks left),
  `a5` and what is computed from them in `t0` for the branches hold public
  values; no address and no branch depends on anything else.
-/

@[expose] public section

namespace VG.Impl.Aes.RISCV64

open VG.RISCV64 VG.Impl.Words.RISCV64

/-- `a5 :=` the scratch buffer rounded up to a multiple of 8. -/
def roundSb : List Instr := [.addi sb sb 7, .logicImm .and sb sb (-8)]

/-- The callee-saved registers, and their slots. -/
def savedRegs : List (Reg × Nat) :=
  [(.s0, 40), (.s1, 41), (.s2, 42), (.s3, 43), (.s4, 44), (.s5, 45), (.s6, 46),
   (.s7, 47), (.s8, 48), (.s9, 49), (.s10, 50), (.s11, 51)]

def saveRegs : List Instr := savedRegs.map fun (r, k) => stS k r
def restoreRegs : List Instr := savedRegs.map fun (r, k) => ldS r k

/-- Build the masks `ms` in the slots from `base` on, through `t0` and `t1`. -/
def storeMasks (base : Nat) (ms : List (Nat × BitVec 64)) : List Instr :=
  ms.flatMap fun (k, v) => Words64.RISCV64.movImm64 t0 t1 v ++ [stS (base + k - 1) t0]

/-- The masks of every linear layer. -/
def maskInit : List Instr :=
  storeMasks bsSlot bsMasks ++ storeMasks srSlot srMasks ++ storeMasks invSrSlot invSrMasks

/-- The slots of the counter block. -/
def cLo : Nat := 59
def cHi : Nat := 60
def cNum : Nat := 61

/-- Load the counter block (`a2`) into its slots, and write the final
counter `(c + n) mod 2³²` back. -/
def ctrSetup : List Instr :=
  loadLE64 t0 t1 t2 .a2 0 ++ [stS cLo t0] ++
  loadLE32 t0 t1 .a2 8 ++ [stS cHi t0] ++
  loadBE32 t0 t1 .a2 12 ++ [stS cNum t0, .add t0 t0 .a4] ++
  storeBE 4 t0 t1 .a2 12

/-- The byte offset of the last round key in the scratch buffer. -/
def lastKey : Nat := 1920

/-- Set up the key loop: `a0 := schedule + 16 rounds`, `a2 := a5 + lastKey`,
`a1 := rounds + 1`. -/
def keySetup : List Instr :=
  [shlI t0 .a1 4, .add .a0 .a0 t0, .addi .a2 sb lastKey, .addi .a1 .a1 1]

/-- The round key at `a0`, as four blocks for `toBs`. -/
def keyLoad : List Instr :=
  loadLE64 (q 0) t0 t1 .a0 0 ++ loadLE64 (q 4) t0 t1 .a0 8 ++
  [movR (q 1) (q 0), movR (q 2) (q 0), movR (q 3) (q 0),
   movR (q 5) (q 4), movR (q 6) (q 4), movR (q 7) (q 4)]

/-- Store the bitsliced round key at `a2`. -/
def keyStore : List Instr := (List.range 8).map fun j => .store .d (q j) .a2 (8 * j)

/-- Step `a0` and `a2` back a round key, and count it in `a1`. -/
def keyStep : List Instr := [.addi .a0 .a0 (-16), .addi .a2 .a2 (-64), .addi .a1 .a1 (-1)]

/-- Bitslice the round key at `a0` to `a2`, and step back. -/
def keyBody : List Instr := keyLoad ++ toBs ++ keyStore ++ keyStep

/-- `a0 := ` the first round key. -/
def keyDone : List Instr := [.addi .a0 .a2 64]

/-- The counter blocks `c + b` (`b < 4`): bytes 0–7 in `q b`, bytes 8–15 in
`q (b + 4)`; and `c := c + 4`. The counter is stored big-endian into the
high half of slot `cHi`, whose low half is bytes 8–11. -/
def ctrBlock (b : Nat) : List Instr :=
  [ldS (q b) cLo, ldS t0 cNum, .addi t0 t0 b] ++ storeBE 4 t0 t1 sb (8 * cHi + 4) ++
  [ldS (q (b + 4)) cHi]

def ctrBlocks : List Instr :=
  ctrBlock 0 ++ ctrBlock 1 ++ ctrBlock 2 ++ ctrBlock 3 ++
  ([ldS t0 cNum, .addi t0 t0 4, stS cNum t0] : List Instr)

/-- A middle round, with `kp` at the previous round key; loops until `kp`
is at the last round key but one. -/
def roundBody : List Instr :=
  ([.addi kp kp 64] : List Instr) ++ sboxCode ++ shiftRows ++ mixColumns ++ addRoundKey ++
  [.sub t0 kp sb, .addi t0 t0 (-((lastKey - 64 : Nat) : Int))]

/-- The last round. -/
def lastRound : List Instr := ([.addi kp kp 64] : List Instr) ++ sboxCode ++ shiftRows ++ addRoundKey

/-- Encrypt the four blocks in `q 0 … q 7` (as `toBs` takes them). -/
def encrypt4 : Prog isa :=
  .seq (.block (toBs ++ [movR kp .a0] ++ addRoundKey))
    (.seq (.loop (.block roundBody) (.nonzero t0)) (.block (lastRound ++ fromBs)))

/-- XOR the keystream block `b` into data block `b`. -/
def xorBlock (b : Nat) : List Instr :=
  loadLE64 t0 t1 t2 .a3 (16 * b) ++ [xorR t0 t0 (q b)] ++ storeLE64 t0 t1 t2 .a3 (16 * b) ++
  loadLE64 t0 t1 t2 .a3 (16 * b + 8) ++ [xorR t0 t0 (q (b + 4))] ++
  storeLE64 t0 t1 t2 .a3 (16 * b + 8)

/-- Four blocks, and on to the next four. -/
def xorFull : List Instr :=
  (List.range 4).flatMap xorBlock ++ ([.addi .a3 .a3 64, .addi .a4 .a4 (-4)] : List Instr)

/-- The last one to three blocks (and none left). -/
def xorTail : Prog isa :=
  .seq (.block (xorBlock 0 ++ ([.addi t0 .a4 (-1)] : List Instr)))
    (.seq (.ite (.nonzero t0) (.seq (.block (xorBlock 1 ++ ([.addi t0 .a4 (-3)] : List Instr)))
        (.ite (.zero t0) (.block (xorBlock 2)) (.block [])))
      (.block []))
    (.block [.li .a4 0]))

/-- One group of (up to) four blocks. -/
def group : Prog isa :=
  .seq (.block ctrBlocks)
    (.seq encrypt4
      (.seq (.block [shrI t0 .a4 2]) (.ite (.nonzero t0) (.block xorFull) xorTail)))

def ctr32 : Prog isa :=
  .seq (.block (roundSb ++ saveRegs ++ maskInit ++ ctrSetup ++ keySetup))
    (.seq (.loop (.block keyBody) (.nonzero .a1))
      (.seq (.block keyDone)
        (.seq (.ite (.zero .a4) (.block []) (.loop group (.nonzero .a4)))
          (.block restoreRegs))))

end VG.Impl.Aes.RISCV64
