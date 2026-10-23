module

public import VerifiedGarbage.Impl.Aes.PPC64LE.Linear

/-!
# AES counter mode (GCM's `inc₃₂`), bitsliced, on PPC64LE

`vg_aes_ctr32(schedule = r3, rounds = r4, counter = r5, data = r6, n = r7, scratch = r8)`.

Constant-time AES in the style of BearSSL's `aes_ct64` (Thomas Pornin, MIT
licence): four blocks at a time, bitsliced in eight 64-bit registers
(`Linear.lean`, `Sbox.lean`), as the x86-64 code does
(`Impl/Aes/X86_64/Ctr32.lean`).

* The nonvolatile registers `r14`–`r31` are saved in slots 40–57 of the
  scratch buffer, the counter block in slots 58–60: bytes 0–7, bytes 8–11
  (the high half zero, later each counter block's last four bytes, stored
  big-endian with `stwbrx`) and the 32-bit counter as an integer.
* The final counter `inc₃₂ⁿ(CB₁)` is written first.
* The round keys are bitsliced once, into slots `128 + 8 (j + 14 - rounds)`
  for round `j`, so that the last is always at slot 240 (byte 1920). The
  loop runs from the last round key down, counting `rounds + 1` keys in
  `r4`, with `r3` at the round key of the schedule and `r5` at its
  bitsliced form.
* Each group of four blocks: build the counter blocks, bitslice them,
  encrypt (the round loop runs `kp` over the round keys until the last but
  one, the first at `r3`), un-bitslice, and XOR the keystream into the
  data, four blocks or the remaining one to three.
* Only `r3`, `r4` (`kp`), `r5`, `r6` (the data), `r7` (the blocks left),
  `r8`, `r10` and what is computed from them in `t0` for the branches hold
  public values; no address and no branch depends on anything else.
-/

@[expose] public section

namespace VG.Impl.Aes.PPC64LE

open VG.PPC64LE

/-- The nonvolatile registers, and their slots. -/
def savedRegs : List (Reg × Nat) :=
  [(.r14, 40), (.r15, 41), (.r16, 42), (.r17, 43), (.r18, 44), (.r19, 45), (.r20, 46),
   (.r21, 47), (.r22, 48), (.r23, 49), (.r24, 50), (.r25, 51), (.r26, 52), (.r27, 53),
   (.r28, 54), (.r29, 55), (.r30, 56), (.r31, 57)]

def saveRegs : List Instr := savedRegs.map fun (r, k) => stS k r
def restoreRegs : List Instr := savedRegs.map fun (r, k) => ldS r k

/-- The slots of the counter block. -/
def cLo : Nat := 58
def cHi : Nat := 59
def cNum : Nat := 60

/-- Load the counter block (`r5`) into its slots, and write the final
counter `(c + n) mod 2³²` back. -/
def ctrSetup : List Instr :=
  [.load .d t0 .r5 0, stS cLo t0,
   .load .w t0 .r5 8, stS cHi t0,
   .li .r0 12, .loadRev .w t0 .r5 .r0, stS cNum t0,
   .add t0 t0 .r7, .storeRev .w t0 .r5 .r0]

/-- The byte offset of the last round key in the scratch buffer. -/
def lastKey : Nat := 1920

/-- Set up the key loop: `r3 := schedule + 16 rounds`, `r5 := r8 + lastKey`,
`r4 := rounds + 1`. -/
def keySetup : List Instr :=
  [.lsl t0 .r4 4, .add .r3 .r3 t0, .addi .r5 sb lastKey, .addi .r4 .r4 1]

/-- The round key at `r3`, as four blocks for `toBs`. -/
def keyLoad : List Instr :=
  [.load .d (q 0) .r3 0, .load .d (q 4) .r3 8,
   movR (q 1) (q 0), movR (q 2) (q 0), movR (q 3) (q 0),
   movR (q 5) (q 4), movR (q 6) (q 4), movR (q 7) (q 4)]

/-- Store the bitsliced round key at `r5`. -/
def keyStore : List Instr := (List.range 8).map fun j => .store .d (q j) .r5 (8 * j)

/-- Step `r3` and `r5` back a round key, and count it in `r4`. -/
def keyStep : List Instr := [.subi .r3 .r3 16, .subi .r5 .r5 64, .subi .r4 .r4 1]

/-- Bitslice the round key at `r3` to `r5`, and step back. -/
def keyBody : List Instr := keyLoad ++ toBs ++ keyStore ++ keyStep

/-- `r3 := ` the first round key. -/
def keyDone : List Instr := [.addi .r3 .r5 64]

/-- The counter blocks `c + b` (`b < 4`): bytes 0–7 in `q b`, bytes 8–15 in
`q (b + 4)`; and `c := c + 4`. The counter is stored big-endian into the
high half of slot `cHi` (at `r8 + r10`), whose low half is bytes 8–11. -/
def ctrBlock (b : Nat) : List Instr :=
  [ldS (q b) cLo, ldS t0 cNum, .addi t0 t0 b, .storeRev .w t0 sb .r10, ldS (q (b + 4)) cHi]

def ctrBlocks : List Instr :=
  ([.li .r10 (8 * cHi + 4)] : List Instr) ++
  ctrBlock 0 ++ ctrBlock 1 ++ ctrBlock 2 ++ ctrBlock 3 ++
  ([ldS t0 cNum, .addi t0 t0 4, stS cNum t0] : List Instr)

/-- A middle round, with `kp` at the previous round key; loops until `kp`
is at the last round key but one. -/
def roundBody : List Instr :=
  ([.addi kp kp 64] : List Instr) ++ sboxCode ++ shiftRows ++ mixColumns ++ addRoundKey ++
  [.sub t0 kp sb, .subi t0 t0 (lastKey - 64)]

/-- The last round. -/
def lastRound : List Instr := ([.addi kp kp 64] : List Instr) ++ sboxCode ++ shiftRows ++ addRoundKey

/-- Encrypt the four blocks in `q 0 … q 7` (as `toBs` takes them). -/
def encrypt4 : Prog isa :=
  .seq (.block (toBs ++ [movR kp .r3] ++ addRoundKey))
    (.seq (.loop (.block roundBody) (.nonzero .d t0)) (.block (lastRound ++ fromBs)))

/-- XOR the keystream block `b` into data block `b`. -/
def xorBlock (b : Nat) : List Instr :=
  [.load .d t0 .r6 (16 * b), xorR t0 t0 (q b), .store .d t0 .r6 (16 * b),
   .load .d t0 .r6 (16 * b + 8), xorR t0 t0 (q (b + 4)), .store .d t0 .r6 (16 * b + 8)]

/-- Four blocks, and on to the next four. -/
def xorFull : List Instr :=
  (List.range 4).flatMap xorBlock ++ ([.addi .r6 .r6 64, .subi .r7 .r7 4] : List Instr)

/-- The last one to three blocks (and none left). -/
def xorTail : Prog isa :=
  .seq (.block (xorBlock 0 ++ ([.subi t0 .r7 1] : List Instr)))
    (.seq (.ite (.nonzero .d t0) (.seq (.block (xorBlock 1 ++ ([.subi t0 .r7 3] : List Instr)))
        (.ite (.zero .d t0) (.block (xorBlock 2)) (.block [])))
      (.block []))
    (.block [.li .r7 0]))

/-- One group of (up to) four blocks. -/
def group : Prog isa :=
  .seq (.block ctrBlocks)
    (.seq encrypt4
      (.seq (.block [shrI t0 .r7 2]) (.ite (.nonzero .d t0) (.block xorFull) xorTail)))

def ctr32 : Prog isa :=
  .seq (.block (saveRegs ++ ctrSetup ++ keySetup))
    (.seq (.loop (.block keyBody) (.nonzero .d .r4))
      (.seq (.block keyDone)
        (.seq (.ite (.zero .d .r7) (.block []) (.loop group (.nonzero .d .r7)))
          (.block restoreRegs))))

end VG.Impl.Aes.PPC64LE
