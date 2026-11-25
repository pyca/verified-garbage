module

public import VerifiedGarbage.Impl.Aes.RISCV64.Fixed
public import VerifiedGarbage.Impl.Words.RISCV64
public import VerifiedGarbage.Impl.Words.RISCV64.Bytes

/-!
# Bitsliced AES encryption and counter mode on RISC-V, four blocks at a time

`vg_aes_ctr32(schedule = a0, rounds = a1, counter = a2, data = a3, n = a4,
scratch = a5)`, and its forms that write elsewhere (`_to`, the source in
`a6`) and take the round keys bitsliced (`_bs`).

The scratch buffer is used from `a5` rounded up to a multiple of 8, in 8-byte
slots: the S-box's spills (0–39, of which it needs four), our caller's
`s0`–`s11` (40–51), the masks (52–57, 64–67), the counter block's first 8
bytes, its next 4 and the counter (59–61), our return address (62) and, from
byte 1024 to byte 1984, the bitsliced round keys, 64 bytes each, the last at
byte `lastKey`.

The code does not depend on secrets but in what it computes: the addresses
and branches are on the pointers, the rounds and the number of blocks.
-/

@[expose] public section

namespace VG.Impl.Aes.RISCV64

open VG.RISCV64 VG.Impl.Words.RISCV64

/-! ## Slots -/

def cLo : Nat := 59
def cHi : Nat := 60
def cNum : Nat := 61
def srcSlot : Nat := 62

/-- The byte of the last bitsliced round key. -/
def lastKey : Nat := 1920

/-- The callee-saved registers, and their slots. -/
def savedRegs : List (Reg × Nat) :=
  [(.s0, 40), (.s1, 41), (.s2, 42), (.s3, 43), (.s4, 44), (.s5, 45), (.s6, 46), (.s7, 47),
   (.s8, 48), (.s9, 49), (.s10, 50), (.s11, 51)]

/-! ## The prologue and epilogue -/

/-- `a5` rounded up to a multiple of 8. -/
def roundSb : List Instr := [.addi sb sb 7, .logicImm .and sb sb (-8)]

def saveRegs : List Instr := savedRegs.map fun p => stS p.2 p.1
def restoreRegs : List Instr := savedRegs.map fun p => ldS p.1 p.2

def maskInit : List Instr := storeMasks bsSlot idxMasks ++ storeMasks srSlot srMasks ++ storeMasks fxSlot fxMasks

/-! ## Round keys -/

/-- `a0`: the last round key; `a2`: where it goes; `a1`: their number. -/
def keySetup : List Instr :=
  [shlI t0 .a1 4, .add .a0 .a0 t0, .addi .a2 sb lastKey, .addi .a1 .a1 1]

/-- The round key at `a0`, as four equal blocks. -/
def keyLoad : List Instr :=
  loadLE64 (q 0) t0 t1 .a0 0 ++ loadLE64 (q 4) t0 t1 .a0 8 ++
    [movR (q 1) (q 0), movR (q 2) (q 0), movR (q 3) (q 0),
     movR (q 5) (q 4), movR (q 6) (q 4), movR (q 7) (q 4)]

def keyStore : List Instr := (List.range 8).map fun j => .store .d (q j) .a2 (8 * j)

def keyStep : List Instr := [.addi .a0 .a0 (-16), .addi .a2 .a2 (-64), .addi .a1 .a1 (-1)]

/-- One round key in form 0, and on to the one before. -/
def keyBody : List Instr := keyLoad ++ toBs ++ keyStore ++ keyStep

/-! Those of `encrypt4` and `decrypt4`: odd ones in form 1 (`Fixed.lean`), with
the bytes loaded where form 1 has them, and all but the first with `{63}` added. -/

/-- The bytes at offsets `f 0`, `f 1`, … of `a0`, as `n` bytes of `d`, the least
significant first. -/
def loadBytes (d : Reg) (f : Nat → Nat) : Nat → List Instr
  | 0 => []
  | 1 => [.load .b d .a0 (f 0)]
  | n + 2 => loadBytes d f (n + 1) ++
      [.load .b t0 .a0 (f (n + 1)), shlI t0 t0 (8 * (n + 1)), .logic .or d d t0]

/-- The byte of the round key that form 0 (form 1, if `o`) has at byte `m`. -/
def keySrc (o : Bool) (m : Nat) : Nat := if o then m % 4 + 4 * ((m / 4 + 4 - m % 4) % 4) else m

def fkLoad (o : Bool) : List Instr :=
  loadBytes (q 0) (keySrc o) 8 ++ loadBytes (q 4) (fun k => keySrc o (8 + k)) 8

/-- One round key, round `a1 - 1`'s, and on to the one before. -/
def fkBody : Prog isa :=
  .seq (.block [.logicImm .and t0 .a1 1])
    (.seq (.ite (.nonzero t0) (.block (fkLoad false)) (.block (fkLoad true)))
      (.seq (.block (slice1 ++ [.addi t0 .a1 (-1)]))
        (.seq (.ite (.nonzero t0) (.block add63) (.block []))
          (.block (keyStore ++ keyStep)))))

/-- `a0`: the first bitsliced round key. -/
def keyDone : List Instr := [.addi .a0 .a2 64]

/-! ## Encryption of four blocks -/

/-! With the round keys in form 0 (those of `_bs`), ShiftRows done. -/

/-- A middle round; the round keys' last is at byte `lastKey` from `kb`. -/
def roundBodyK (kb : Reg) : List Instr :=
  ([.addi kp kp 64] : List Instr) ++ sboxCode ++ shiftRows ++ mixColumns ++ addRoundKey ++
    [.sub t0 kp kb, .addi t0 t0 (-((lastKey - 64 : Nat) : Int))]

def lastRound : List Instr := ([.addi kp kp 64] : List Instr) ++ sboxCode ++ shiftRows ++ addRoundKey

/-- The four blocks in `q 0 … q 7` (as `toBs` takes them) encrypted, with the
round keys at `a0`, the last at byte `lastKey` from `kb`. -/
def encrypt4K (kb : Reg) : Prog isa :=
  .seq (.block (toBs ++ [movR kp .a0] ++ addRoundKey))
    (.seq (.loop (.block (roundBodyK kb)) (.nonzero t0)) (.block (lastRound ++ fromBs)))

/-- An odd round, from form 0 to form 1, and an even one, back. -/
def roundA : List Instr := ([.addi kp kp 64] : List Instr) ++ sbox0Code ++ mixColumns1 ++ addRoundKey
def roundB : List Instr := ([.addi kp kp 64] : List Instr) ++ sbox0Code ++ sr2 ++ mixColumns ++ addRoundKey

def lastFx : List Instr := ([.addi kp kp 64] : List Instr) ++ sbox0Code ++ sr2 ++ addRoundKey

/-- The four blocks in `q 0 … q 7` encrypted with `fkBody`'s round keys, the
first at `a0` and the last at byte `lastKey`. -/
def encrypt4 : Prog isa :=
  .seq (.block (toBs ++ [movR kp .a0] ++ addRoundKey ++ roundA))
    (.seq (.loop (.block (roundB ++ roundA ++ [.sub t0 kp sb, .addi t0 t0 (-((lastKey - 64 : Nat) : Int))]))
        (.nonzero t0))
      (.block (lastFx ++ fromBs)))

/-! ## Counter mode -/

/-- The counter block into its slots, and the final counter stored back. -/
def ctrSetup : List Instr :=
  loadLE64 t0 t1 t2 .a2 0 ++ [stS cLo t0] ++ loadLE32 t0 t1 .a2 8 ++ [stS cHi t0] ++
    loadBE32 t0 t1 .a2 12 ++ [stS cNum t0, .add t0 t0 .a4] ++ storeBE 4 t0 t1 .a2 12

/-- Counter block `c` of the group. -/
def ctrBlock (c : Nat) : List Instr :=
  [ldS (q c) cLo, ldS t0 cNum, .addi t0 t0 c] ++ storeBE 4 t0 t1 sb (8 * cHi + 4) ++ [ldS (q (c + 4)) cHi]

/-- Four counter blocks, and the counter on by four. -/
def ctrBlocks : List Instr :=
  ctrBlock 0 ++ ctrBlock 1 ++ ctrBlock 2 ++ ctrBlock 3 ++ [ldS t0 cNum, .addi t0 t0 4, stS cNum t0]

/-- The source's register: `a2` if it is apart from the data (`o`). -/
def srcReg (o : Bool) : Reg := if o then .a2 else .a3

/-- Block `c` of the source XORed with the keystream to that of the data, by
doublewords if `w`. -/
def xorBlock (o w : Bool) (c : Nat) : List Instr :=
  loadLE64W w t0 t1 t2 (srcReg o) (16 * c) ++ [xorR t0 t0 (q c)] ++ storeLE64W w t0 t1 t2 .a3 (16 * c) ++
    loadLE64W w t0 t1 t2 (srcReg o) (16 * c + 8) ++ [xorR t0 t0 (q (c + 4))] ++
    storeLE64W w t0 t1 t2 .a3 (16 * c + 8)

def srcStep (o : Bool) : List Instr := if o then [.addi .a2 .a2 64] else []

/-- Four blocks, and on to the next. -/
def xorFull (o w : Bool) : List Instr :=
  (List.range 4).flatMap (xorBlock o w) ++ ([.addi .a3 .a3 64, .addi .a4 .a4 (-4)] ++ srcStep o)

/-- The last one to three blocks (and none left). -/
def xorTail (o w : Bool) : Prog isa :=
  .seq (.block (xorBlock o w 0 ++ ([.addi t0 .a4 (-1)] : List Instr)))
    (.seq (.ite (.nonzero t0) (.seq (.block (xorBlock o w 1 ++ ([.addi t0 .a4 (-3)] : List Instr)))
        (.ite (.zero t0) (.block (xorBlock o w 2)) (.block [])))
      (.block []))
    (.block [.li .a4 0]))

/-- One group of (up to) four blocks. -/
def group (crypt : Prog isa) (o w : Bool) : Prog isa :=
  .seq (.block ctrBlocks)
    (.seq crypt
      (.seq (.block [shrI t0 .a4 2]) (.ite (.nonzero t0) (.block (xorFull o w)) (xorTail o w))))

/-- `t0 = 0` if the data (and the source) are at multiples of 8. -/
def alignTest (o : Bool) : List Instr :=
  if o then [.logic .or t0 .a3 .a2, .logicImm .and t0 t0 7] else [.logicImm .and t0 .a3 7]

def ctrGroups (crypt : Prog isa) (o : Bool) : Prog isa :=
  .seq (.block (alignTest o))
    (.ite (.zero t0) (.loop (group crypt o true) (.nonzero .a4)) (.loop (group crypt o false) (.nonzero .a4)))

/-- Out of place, our return address into its slot and the source into `ra`,
which the key loop does not write. -/
def srcSave (o : Bool) : List Instr := if o then [stS srcSlot .ra, movR .ra .a6] else []
def srcLoad (o : Bool) : List Instr := if o then [movR .a2 .ra] else []
def srcRestore (o : Bool) : List Instr := if o then [ldS .ra srcSlot] else []

def ctr32With (o : Bool) : Prog isa :=
  .seq (.block (roundSb ++ srcSave o ++ saveRegs ++ maskInit ++ ctrSetup ++ keySetup))
    (.seq (.loop fkBody (.nonzero .a1))
      (.seq (.block (keyDone ++ srcLoad o))
        (.seq (.ite (.zero .a4) (.block []) (ctrGroups encrypt4 o))
          (.block (restoreRegs ++ srcRestore o)))))

def ctr32 : Prog isa := ctr32With false
def ctr32To : Prog isa := ctr32With true

/-! ## With the round keys bitsliced (at `a0`) -/

def bsSave : List Instr := [stS srcSlot .ra]
def bsSrc (o : Bool) : List Instr := if o then [movR .a2 .a6] else []

/-- `ra`: the last round key is at byte `lastKey` from it. -/
def bsKb : List Instr := [shlI t0 .a1 6, .add .ra .a0 t0, .addi .ra .ra (-((lastKey : Nat) : Int))]

def ctr32BsWith (o : Bool) : Prog isa :=
  .seq (.block (roundSb ++ bsSave ++ saveRegs ++ maskInit ++ ctrSetup ++ bsSrc o ++ bsKb))
    (.seq (.ite (.zero .a4) (.block []) (ctrGroups (encrypt4K .ra) o))
      (.block (restoreRegs ++ srcRestore true)))

def ctr32Bs : Prog isa := ctr32BsWith false
def ctr32BsTo : Prog isa := ctr32BsWith true

end VG.Impl.Aes.RISCV64
