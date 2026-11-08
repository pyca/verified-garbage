module

public import VerifiedGarbage.Impl.Aes.AArch64.Linear

/-!
# AES counter mode (GCM's `inc₃₂`), bitsliced, on AArch64

`vg_aes_ctr32(schedule = x0, rounds = x1, counter = x2, data = x3, n = x4, scratch = x5)`,
and its out-of-place form, the internal `vg_aes_ctr32_to(…, src = x3, …,
dst = x6)` (`Proof.Aes.ctr32ToAArch64`): the same code (`ctr32Gen`), but
that `dst` is kept in `x30` (our return address saved in slot 58 until the
end), and the keystream XORed into `src` is stored there.

Constant-time AES in the style of BearSSL's `aes_ct64` (Thomas Pornin, MIT
licence): four blocks at a time, bitsliced in eight 64-bit registers
(`Linear.lean`, `Sbox.lean`).

* The callee-saved registers `x19`–`x28` are saved in slots 48–57 of the
  scratch buffer, the counter block in slots 59–61: bytes 0–7, bytes 8–11
  (the high half zero) and the 32-bit counter as an integer (in the low
  half).
* The final counter `inc₃₂ⁿ(CB₁)` is written first.
* The round keys are bitsliced once, into slots `128 + 8 (j + 14 - rounds)`
  for round `j`, so that the last is always at slot 240 (byte 1920). The
  loop runs from the last round key down, counting in `x2`.
* Each group of four blocks: build the counter blocks, bitslice them,
  encrypt (the round loop runs `x1` over the round keys until the last
  but one), un-bitslice, and XOR the keystream into the data, four blocks
  or the remaining one to three.
* Only `x0` (the first round key), `x1`, `x2` during the key loop, `x3`
  (the data), `x30` (the destination, out of place), `x4` (the blocks
  left), `x5` and the loop tests (`t0`) hold
  public values; no address and no branch depends on anything else.
-/

@[expose] public section

namespace VG.Impl.Aes.AArch64

open VG.AArch64

/-- The callee-saved registers, and their slots. -/
def savedRegs : List (Reg × Nat) :=
  [(.x19, 48), (.x20, 49), (.x21, 50), (.x22, 51), (.x23, 52), (.x24, 53), (.x25, 54), (.x26, 55),
   (.x27, 56), (.x28, 57)]

def saveRegs : List Instr := savedRegs.map fun (r, k) => stS k r
def restoreRegs : List Instr := savedRegs.map fun (r, k) => ldS r k

/-- The slots of the counter block. -/
def cLo : Nat := 59
def cHi : Nat := 60
def cNum : Nat := 61

/-- Load the counter block (`x2`) into its slots, and write the final
counter `(c + n) mod 2³²` back. -/
def ctrSetup : List Instr :=
  [.ldr .x (q 0) .x2 0, stS cLo (q 0),
   .ldr .w (q 0) .x2 8, stS cHi (q 0),
   .ldr .w (q 0) .x2 12, .rev32 (q 0) (q 0), .str .w (q 0) sb (8 * cNum),
   .add .w (q 0) (q 0) .x4, .rev32 (q 0) (q 0), .str .w (q 0) .x2 12]

/-- The byte offset of the last round key in the scratch buffer. -/
def lastKey : Nat := 1920

/-- Set up the key loop: `x2 := rounds + 1` (the round keys left),
`x0 := schedule + 16 rounds`, `x1 := x5 + lastKey`. -/
def keySetup : List Instr :=
  [.addImm .x .x2 .x1 1, .lsl .x (q 0) .x1 4, .add .x .x0 .x0 (q 0), .addImm .x .x1 sb lastKey]

/-- The round key at `x0`, as four blocks for `toBs`. -/
def keyLoad : List Instr :=
  [.ldr .x (q 0) .x0 0, .ldr .x (q 4) .x0 8,
   movR (q 1) (q 0), movR (q 2) (q 0), movR (q 3) (q 0),
   movR (q 5) (q 4), movR (q 6) (q 4), movR (q 7) (q 4)]

/-- Store the bitsliced round key at `x1`. -/
def keyStore : List Instr := (List.range 8).map fun j => .str .x (q j) .x1 (8 * j)

/-- Step `x0` and `x1` back a round key, and `x2` down. -/
def keyStep : List Instr := [.subImm .x .x0 .x0 16, .subImm .x .x1 .x1 64, .subImm .x .x2 .x2 1]

/-- Bitslice the round key at `x0` to `x1`, and step back. -/
def keyBody : List Instr := keyLoad ++ toBs ++ keyStore ++ keyStep

/-- `x0 := ` the first round key. -/
def keyDone : List Instr := [.addImm .x .x0 .x1 64]

/-- The counter blocks `c + b` (`b < 4`): bytes 0–7 in `q b`, bytes 8–15 in
`q (b + 4)`. -/
def ctrBlock (b : Nat) : List Instr :=
  [ldS (q b) cLo, .ldr .w t0 sb (8 * cNum), .addImm .w t0 t0 b, .rev32 t0 t0, .lsl .x t0 t0 32,
   ldS (q (b + 4)) cHi, eorR (q (b + 4)) (q (b + 4)) t0]

/-- The four counter blocks, and `c := c + 4`. -/
def ctrBlocks : List Instr :=
  ctrBlock 0 ++ ctrBlock 1 ++ ctrBlock 2 ++ ctrBlock 3 ++
  ([.ldr .w t0 sb (8 * cNum), .addImm .w t0 t0 4, .str .w t0 sb (8 * cNum)] : List Instr)

/-- A middle round, with `kp` at the previous round key; loops until `kp`
is at the last round key but one (`t0 = 0`). -/
def roundBody : List Instr :=
  ([.addImm .x kp kp 64] : List Instr) ++ sboxCode ++ shiftRows ++ mixColumns ++ addRoundKey ++
  ([.sub .x t0 kp sb, .subImm .x t0 t0 (lastKey - 64)] : List Instr)

/-- The last round. -/
def lastRound : List Instr := ([.addImm .x kp kp 64] : List Instr) ++ sboxCode ++ shiftRows ++ addRoundKey

/-- Encrypt the four blocks in `q 0 … q 7` (as `toBs` takes them). -/
def encrypt4 : Prog isa :=
  .seq (.block (toBs ++ [movR kp .x0] ++ addRoundKey))
    (.seq (.loop (.block roundBody) (.nonzero .x t0)) (.block (lastRound ++ fromBs)))

/-- Where the output goes: over the data (`x3`), or out of place (`to`) to
the destination, which `x30` holds from the entry on (no other register is
left: the key loop writes all the others but those of the data). -/
def dstR (to : Bool) : Reg := cond to .x30 .x3

/-- The slot that keeps our return address out of place, while `x30` holds
the destination: the last of the slots saved (`Proof.Aes.AArch64.Saved`). -/
def lrO : Nat := 58

/-- XOR the keystream block `b` into data block `b`, stored to output block
`b`: both words loaded first, so that in place the second is read before
the first is stored. -/
def xorBlock (to : Bool) (b : Nat) : List Instr :=
  [.ldr .x t0 .x3 (16 * b), .ldr .x t2 .x3 (16 * b + 8), eorR t0 t0 (q b), eorR t2 t2 (q (b + 4)),
   .str .x t0 (dstR to) (16 * b), .str .x t2 (dstR to) (16 * b + 8)]

/-- Four blocks, and on to the next four. -/
def xorFull (to : Bool) : List Instr :=
  (List.range 4).flatMap (xorBlock to) ++ (([.addImm .x .x3 .x3 64, .subImm .x .x4 .x4 4] : List Instr) ++
    cond to [.addImm .x .x30 .x30 64] [])

/-- The last one to three blocks (and none left). -/
def xorTail (to : Bool) : Prog isa :=
  .seq (.block (xorBlock to 0 ++ ([.subImm .x t0 .x4 1] : List Instr)))
    (.seq (.ite (.nonzero .x t0) (.seq (.block (xorBlock to 1 ++ ([.subImm .x t0 .x4 2] : List Instr)))
        (.ite (.nonzero .x t0) (.block (xorBlock to 2)) (.block [])))
      (.block []))
    (.block [.movz .x .x4 0 0]))

/-- One group of (up to) four blocks. -/
def group (to : Bool) : Prog isa :=
  .seq (.block ctrBlocks)
    (.seq encrypt4
      (.seq (.block [lsrI t0 .x4 2]) (.ite (.nonzero .x t0) (.block (xorFull to)) (xorTail to))))

/-- `vg_aes_ctr32`, or out of place (`to`) the internal `vg_aes_ctr32_to`,
with the destination in `x6`, moved to `x30` once our return address is
saved in slot `lrO`. -/
def ctr32Gen (to : Bool) : Prog isa :=
  .seq (.block (saveRegs ++ cond to [stS lrO .x30, movR .x30 .x6] [] ++ ctrSetup ++ keySetup))
    (.seq (.loop (.block keyBody) (.nonzero .x .x2))
      (.seq (.block keyDone)
        (.seq (.ite (.zero .x .x4) (.block []) (.loop (group to) (.nonzero .x .x4)))
          (.block (restoreRegs ++ cond to [ldS .x30 lrO] [])))))

def ctr32 : Prog isa := ctr32Gen false

def ctr32To : Prog isa := ctr32Gen true

end VG.Impl.Aes.AArch64
