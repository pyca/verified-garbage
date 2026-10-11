module

public import VerifiedGarbage.Impl.Rc2.AArch64.Block

/-! # RC2-CBC decryption on AArch64, eight blocks at a time

CBC decryption decrypts each ciphertext block independently, so the blocks
are decrypted eight at a time in the vector registers, as two *sets* of
four: word `i` of the four blocks of set `h` is in the four 32-bit lanes of
`wreg h i` (`v24`–`v27`, `v28`–`v31`), each lane's low 16 bits the word
(the high 16 bits are not kept clean: only the rotation needs a clean word,
and it masks it first, with `0xffff` in every lane of `m16`). The schedule
is in `v16`–`v23` throughout: a key word is broadcast from it (`keyBcast`),
and it is the table of the mashing's `tbl` lookups (`select false`), whose
indices are the bytes `2 j` and `2 j + 1` of each lane (`514 j + 256`).

Each group loads the eight blocks and gathers their words into the lanes
with `tbl` (`loadGroup`), runs the sixteen reverse rounds on both sets, the
reverse mashing after the fifth and the eleventh, scatters the words back
into blocks with `tbl`, XORs each with the ciphertext block before it (the
chaining value in `x11`, then the group's own blocks, read again before any
is overwritten), and stores them in place (`storeGroup`).

Only caller-saved vector registers (`v0`–`v7`, `v16`–`v31`) and `x6`,
`x7`, `x9`–`x12` are used. The counts and the addresses depend only on the
pointers and `n`; nothing secret is an address or a branch condition.
-/

@[expose] public section

namespace VG.Impl.Rc2.AArch64.Vec

open VG.AArch64 VG.Impl.Tbl.AArch64

/-- Word `i` of the four blocks of set `h`. -/
def wreg (h i : Nat) : VReg := treg (8 + 4 * h + i % 4)

/-- Temporary `k` (the rotated word, `a & b`, `c & ~a`) of set `h`. -/
def tmp (h k : Nat) : VReg := [.v0, .v1, .v2, .v3, .v4, .v5].getD (3 * h + k) .v0

/-- `0xffff` in every 32-bit lane. -/
def m16 : VReg := .v6

/-- A key word, in every lane. -/
def kb : VReg := .v7

/-- Key word `k` into every lane of `kb` (in the low 16 bits): the 32-bit
lane of the schedule holding it, its halves exchanged if `k` is odd. -/
def keyBcast (k : Nat) : List Instr :=
  ([.vop (.dupE .s4 kb (treg (k / 8)) (k % 8 / 2))] : List Instr) ++
    (if k % 2 = 1 then [.vop (.rev .rev32h kb kb)] else [])

/-- The reverse mix of word `i` of set `h`, with the key word in `kb`. -/
def rmix (h i : Nat) : List Instr :=
  [.vop (.logic .and (wreg h i) (wreg h i) m16),
   .vop (.shift .ushr .s4 (tmp h 0) (wreg h i) (Spec.Rc2.rotation i)),
   .vop (.shift .sli .s4 (tmp h 0) (wreg h i) (16 - Spec.Rc2.rotation i)),
   .vop (.logic .and (tmp h 1) (wreg h (i + 3)) (wreg h (i + 2))),
   .vop (.logic .bic (tmp h 2) (wreg h (i + 1)) (wreg h (i + 3))),
   .vop (.sub .s4 (tmp h 0) (tmp h 0) kb),
   .vop (.sub .s4 (tmp h 0) (tmp h 0) (tmp h 1)),
   .vop (.sub .s4 (wreg h i) (tmp h 0) (tmp h 2))]

/-- Reverse mixing round `j`, on both sets. -/
def rmixRound (j : Nat) : List Instr :=
  [3, 2, 1, 0].flatMap fun i => keyBcast (4 * j + i) ++ rmix 0 i ++ rmix 1 i

/-- The reverse mash of word `i` of set `h`: the schedule word at the low six
bits of the word before it, by `tbl`, subtracted. -/
def rmash (h i : Nat) : List Instr :=
  [imm .x9 63, .vop (.dup .s4 .v1 .x9), .vop (.logic .and .v0 (wreg h (i + 3)) .v1),
   imm .x9 514, .vop (.dup .s4 .v4 .x9), .vop (.mul .v0 .v0 .v4),
   imm .x9 256, .vop (.dup .s4 .v1 .x9), .vop (.add .s4 .v0 .v0 .v1)] ++
  quarters false ++ select false ++ ([.vop (.sub .s4 (wreg h i) (wreg h i) .v0)] : List Instr)

/-- The reverse mashing round, on both sets. -/
def rmashRound : List Instr := [3, 2, 1, 0].flatMap fun i => rmash 0 i ++ rmash 1 i

/-- The sixteen reverse rounds. -/
def rounds : List Instr :=
  (List.range 16).flatMap fun j =>
    rmixRound (15 - j) ++ (if j = 4 ∨ j = 10 then rmashRound else [])

/-- The index gathering word `i` of four blocks (32 bytes, in two registers)
into the 32-bit lanes (the high two bytes of each out of range: 0). -/
def inIndex (i : Nat) : BitVec 128 :=
  ofVBytes fun e => if e % 4 < 2 then BitVec.ofNat 8 (8 * (e / 4) + 2 * i + e % 4) else 0xff

/-- The eight blocks at `x1`, their words gathered into the sets. -/
def loadGroup : List Instr :=
  ([.ldrq .v0 .x1 0, .ldrq .v1 .x1 16, .ldrq .v2 .x1 32, .ldrq .v3 .x1 48] : List Instr) ++
  (List.range 4).flatMap fun i => const128 .v4 (inIndex i) ++
    ([.vop (.tblN false 2 (wreg 0 i) .v0 .v4), .vop (.tblN false 2 (wreg 1 i) .v2 .v4)] : List Instr)

/-- The index scattering a set's words back into blocks `2 k`, `2 k + 1`. -/
def outIndex (k : Nat) : BitVec 128 :=
  ofVBytes fun e => BitVec.ofNat 8 (16 * (e % 8 / 2) + 4 * (2 * k + e / 8) + e % 2)

/-- The decrypted blocks, each XORed with the ciphertext block before it
(the chaining value in `x11` before the first), stored in place; the last
ciphertext block into `x11`. -/
def storeGroup : List Instr :=
  const128 .v4 (outIndex 0) ++
  ([.vop (.tblN false 4 .v0 (wreg 0 0) .v4), .vop (.tblN false 4 .v2 (wreg 1 0) .v4)] : List Instr) ++
  const128 .v4 (outIndex 1) ++
  ([.vop (.tblN false 4 .v1 (wreg 0 0) .v4), .vop (.tblN false 4 .v3 (wreg 1 0) .v4),
   .ldr .x .x9 .x1 0, .vop (.ins .d2 .v4 0 .x11), .vop (.ins .d2 .v4 1 .x9),
   .addImm .x .x12 .x1 8, .ldrq .v5 .x12 0,
   .vop (.logic .eor .v0 .v0 .v4), .vop (.logic .eor .v1 .v1 .v5),
   .ldrq .v4 .x12 16, .ldrq .v5 .x12 32,
   .vop (.logic .eor .v2 .v2 .v4), .vop (.logic .eor .v3 .v3 .v5),
   .ldr .x .x11 .x1 56,
   .strq .v0 .x1 0, .strq .v1 .x1 16, .strq .v2 .x1 32, .strq .v3 .x1 48] : List Instr)

/-- One group of eight blocks, and on to the next. -/
def group : List Instr :=
  loadGroup ++ rounds ++ storeGroup ++ ([.addImm .x .x1 .x1 64, .subImm .x .x10 .x10 1] : List Instr)

/-- The schedule into `v16`–`v23`, `0xffff` into `m16`, and the chaining
value into `x11`. -/
def setup : List Instr :=
  (List.range 8).map (fun r => .ldrq (treg r) .x0 (16 * r)) ++
  [imm .x9 65535, .vop (.dup .s4 m16 .x9), .ldr .x .x11 .x23 0]

/-- The groups of eight of the `x24` blocks at `x1` (`x10` counting them),
the chaining value at `x23` updated; then `x24` the blocks left. -/
def phase : Prog isa :=
  .seq (.block [.lsr .x .x10 .x24 3])
    (.seq (.ite (.zero .x .x10) (.block [])
      (.seq (.block setup) (.seq (.loop (.block group) (.nonzero .x .x10))
        (.block [.str .x .x11 .x23 0]))))
      (.block (mask .x24 3)))

end VG.Impl.Rc2.AArch64.Vec
