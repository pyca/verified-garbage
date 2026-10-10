import VerifiedGarbage.TCB.AArch64.Isa
import VerifiedGarbage.Impl.Blowfish.Table

/-!
# Blowfish on AArch64: sixteen blocks at a time, S-boxes by `tbl`

The S-boxes are key-dependent and indexed by secret bytes, so no lookup
reads memory at a secret address. The code works on sixteen blocks at once
(a *batch*), one per byte lane:

* The halves xL and xR of the sixteen blocks are sixteen 32-bit words each,
  four per register (`A`, `v4`–`v7`, and `B`, `v8`–`v11`), in block order.
* The schedule holds the S-boxes in byte planes (`Spec.Blowfish.scheduleAt`):
  byte `b` of S_{j+1}[x] at `1024 j + 256 b + x` (`planeOff`).
* F of sixteen words (`f`): `uzp` splits them into four planes of sixteen
  bytes (`a`, `b`, `c`, `d`, in `v16`–`v19`); each plane indexes its S-box:
  for each of the S-box's four byte planes, one `tbl` and three `tbx` of
  four registers (`v28`–`v31`, loaded with a quarter of the plane), on the
  index XORed with 0, 64, 128 and 192, exactly one of which is in range of
  its quarter; `zip` turns the four byte planes found back into words,
  which are added and XORed into F (`v12`–`v15`).

Timing depends only on the pointers, `n` and loop counters: every secret is
in a register, and `tbl`/`tbx` take a time independent of their data.
`v8`–`v15` are callee-saved: they are saved in the working space. No
instruction outside the baseline ISA is used.

Key expansion runs the same batch code with one meaningful lane (lane 0 of
`A` and `B`): 521 chained encryptions, each one's output written to the
schedule, in the planes for the S-boxes, before the next.
-/

namespace VG.Impl.Blowfish.AArch64

open VG.AArch64

/-- The offset of byte plane `b` of S-box `j` in the schedule. -/
def planeOff (j b : Nat) : Nat := 1024 * j + 256 * b

/-- The P-array's offset in the schedule. -/
def pOff : Nat := 4096

/-- ECB's working space: a batch for the last blocks (128 bytes), then the
saved `q8`–`q15` (128 bytes). -/
def tailOff : Nat := 0
def saveOff : Nat := 128

/-! ## Registers -/

def aReg (k : Nat) : VReg := [.v4, .v5, .v6, .v7].getD k .v4
def bReg (k : Nat) : VReg := [.v8, .v9, .v10, .v11].getD k .v8
def fReg (k : Nat) : VReg := [.v12, .v13, .v14, .v15].getD k .v12
/-- The byte planes of xL: `a` (the most significant byte), `b`, `c`, `d`,
which index S₁, S₂, S₃ and S₄. -/
def idxReg (j : Nat) : VReg := [.v16, .v17, .v18, .v19].getD j .v16
/-- The byte planes of an S-box's outputs (byte 0 first). -/
def outReg (b : Nat) : VReg := [.v20, .v21, .v22, .v23].getD b .v20
/-- The index XORed with 64, 128 and 192. -/
def qReg (q : Nat) : VReg := [.v24, .v24, .v25, .v26].getD q .v24
/-- The table registers of a `tbl`: `v28`–`v31`. -/
def tReg (r : Nat) : VReg := [.v28, .v29, .v30, .v31].getD r .v28
/-- 64 and 128 in every byte. -/
def c64 : VReg := .v2
def c128 : VReg := .v3

def veor (d n m : VReg) : Instr := .vop (.logic .eor d n m)
def vperm (op : VPermOp) (a : VArr) (d n m : VReg) : Instr := .vop (.perm op a d n m)

/-! ## F -/

/-- The byte planes of the words in `L 0`…`L 3` into `idxReg`, through
`v0`, `v1`, `v20` and `v21`. -/
def planes (L : Nat → VReg) : List Instr :=
  [vperm .uzp1 .b16 .v0 (L 0) (L 1), vperm .uzp2 .b16 .v1 (L 0) (L 1),
   vperm .uzp1 .b16 (outReg 0) (L 2) (L 3), vperm .uzp2 .b16 (outReg 1) (L 2) (L 3),
   vperm .uzp1 .b16 (idxReg 3) .v0 (outReg 0), vperm .uzp2 .b16 (idxReg 1) .v0 (outReg 0),
   vperm .uzp1 .b16 (idxReg 2) .v1 (outReg 1), vperm .uzp2 .b16 (idxReg 0) .v1 (outReg 1)]

/-- Quarter `q` of byte plane `b` of S-box `j`, from the schedule at `sch`,
into `v28`–`v31`. -/
def loadQuarter (sch : Reg) (j b q : Nat) : List Instr :=
  (List.range 4).map fun r => .ldrq (tReg r) sch (planeOff j b + 64 * q + 16 * r)

/-- Byte plane `b` of S-box `j` at the indices in `idxReg j`, into
`outReg b`: a `tbl` of the first quarter, then a `tbx` of each other. -/
def lookupPlane (sch : Reg) (j b : Nat) : List Instr :=
  (List.range 4).flatMap fun q =>
    loadQuarter sch j b q ++
      ([.vop (.tblN (q != 0) 4 (outReg b) (tReg 0) (if q = 0 then idxReg j else qReg q))] : List Instr)

/-- S-box `j` at the indices in `idxReg j`, in byte planes in `outReg`. -/
def lookup (sch : Reg) (j : Nat) : List Instr :=
  [veor (qReg 1) (idxReg j) c64, veor (qReg 2) (idxReg j) c128, veor (qReg 3) (qReg 1) c128] ++
    (List.range 4).flatMap (lookupPlane sch j)

/-- The words of the byte planes in `outReg`, into `wordReg`. -/
def words : List Instr :=
  [vperm .zip1 .b16 .v0 (outReg 0) (outReg 2), vperm .zip2 .b16 .v1 (outReg 0) (outReg 2),
   vperm .zip1 .b16 (outReg 0) (outReg 1) (outReg 3),
   vperm .zip2 .b16 (outReg 2) (outReg 1) (outReg 3),
   vperm .zip1 .b16 (outReg 1) .v0 (outReg 0), vperm .zip2 .b16 (outReg 3) .v0 (outReg 0),
   vperm .zip1 .b16 .v0 .v1 (outReg 2), vperm .zip2 .b16 .v1 .v1 (outReg 2)]

/-- Where `words` leaves words `4 k`…`4 k + 3`. -/
def wordReg (k : Nat) : VReg := [outReg 1, outReg 3, .v0, .v1].getD k .v0

/-- F's accumulation of S-box `j`: S₁, then + S₂, XOR S₃, + S₄. -/
def combine (j : Nat) : List Instr :=
  (List.range 4).map fun k =>
    if j = 0 then .vop (.mov (fReg k) (wordReg k))
    else if j = 2 then veor (fReg k) (fReg k) (wordReg k)
    else .vop (.add .s4 (fReg k) (fReg k) (wordReg k))

/-- F of the words whose planes are in `idxReg`, into `fReg`. -/
def f (sch : Reg) : List Instr :=
  (List.range 4).flatMap fun j => lookup sch j ++ words ++ combine j

/-! ## Rounds -/

/-- The P-array entry at `x5` (in the P-array at `sch`), broadcast in `v0`. -/
def loadP : List Instr := [.ldr .w .x6 .x5 pOff, .vop (.dup .s4 .v0 .x6)]

/-- `L ^= P` (the entry at `x5`), then `R ^= F(L)`; `x5` moves to the next
entry (`up`) or the previous one. -/
def round (sch : Reg) (up : Bool) (L R : Nat → VReg) : List Instr :=
  loadP ++ (List.range 4).map (fun k => veor (L k) (L k) .v0) ++
  planes L ++ f sch ++ (List.range 4).map (fun k => veor (R k) (R k) (fReg k)) ++
  [if up then .addImm .x .x5 .x5 4 else .subImm .x .x5 .x5 4]

/-- Two rounds, the halves trading places twice; `x7` counts the pairs. -/
def roundPair (sch : Reg) (up : Bool) : List Instr :=
  round sch up aReg bReg ++ round sch up bReg aReg ++ ([.subImm .x .x7 .x7 1] : List Instr)

/-- The last swap undone: xR (in `A`) ^= P₁₇ and xL (in `B`) ^= P₁₈ when
encrypting, P₂ and P₁ when decrypting. -/
def finish (sch : Reg) (up : Bool) : List Instr :=
  ([.ldr .w .x6 sch (pOff + 4 * (if up then 16 else 1)), .vop (.dup .s4 .v0 .x6)] : List Instr) ++
  (List.range 4).map (fun k => veor (aReg k) (aReg k) .v0) ++
  ([.ldr .w .x6 sch (pOff + 4 * (if up then 17 else 0)), .vop (.dup .s4 .v0 .x6)] : List Instr) ++
  (List.range 4).map (fun k => veor (bReg k) (bReg k) .v0)

/-- The sixteen rounds on xL in `A` and xR in `B`, leaving xL in `B` and xR
in `A`; the schedule at `sch`, the P-array in encryption order if `up`. -/
def cipher (sch : Reg) (up : Bool) : Prog isa :=
  .seq (.block [.addImm .x .x5 sch (if up then 0 else 68), .movz .x .x7 8 0])
    (.seq (.loop (.block (roundPair sch up)) (.nonzero .x .x7)) (.block (finish sch up)))

/-! ## Batches -/

/-- Blocks `4 k`…`4 k + 3` at `p` (32 bytes) into words `k` of `A` (xL) and
`B` (xR), as big-endian words, through `v20` and `v21`. -/
def loadPair (p : Reg) (k : Nat) : List Instr :=
  [.ldrq .v20 p (32 * k), .ldrq .v21 p (32 * k + 16), .vop (.rev .rev32b .v20 .v20),
   .vop (.rev .rev32b .v21 .v21), vperm .uzp1 .s4 (aReg k) .v20 .v21,
   vperm .uzp2 .s4 (bReg k) .v20 .v21]

/-- The 128 bytes of sixteen blocks at `p` into `A` and `B`. -/
def loadBatch (p : Reg) : List Instr := (List.range 4).flatMap (loadPair p)

/-- Blocks `4 k`…`4 k + 3` back to `p`: xL from `B`, xR from `A`. -/
def storePair (p : Reg) (k : Nat) : List Instr :=
  [vperm .zip1 .s4 .v20 (bReg k) (aReg k), vperm .zip2 .s4 .v21 (bReg k) (aReg k),
   .vop (.rev .rev32b .v20 .v20), .vop (.rev .rev32b .v21 .v21), .strq .v20 p (32 * k),
   .strq .v21 p (32 * k + 16)]

def storeBatch (p : Reg) : List Instr := (List.range 4).flatMap (storePair p)

/-- Sixteen blocks at `x4`, in place, under the schedule at `x0`. -/
def batch (up : Bool) : Prog isa :=
  .seq (.block (loadBatch .x4)) (.seq (cipher .x0 up) (.block (storeBatch .x4)))

/-! ## ECB

`vg_blowfish_ecb_{en,de}crypt(schedule = x0, data = x1, n = x2, scratch = x3)`,
the working space (`scratch`) supplied by a frame. -/

/-- Save `q8`–`q15` at `x3 + off`, and restore them. -/
def saveRegsAt (off : Nat) : List Instr :=
  (List.range 8).map fun k => .strq ([.v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15].getD k .v8)
    .x3 (off + 16 * k)
def restoreRegsAt (off : Nat) : List Instr :=
  (List.range 8).map fun k => .ldrq ([.v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15].getD k .v8)
    .x3 (off + 16 * k)

/-- ECB saves them after its batch for the last blocks. -/
def saveRegs : List Instr := saveRegsAt saveOff
def restoreRegs : List Instr := restoreRegsAt saveOff

/-- 64 and 128 in every byte of `c64` and `c128`. -/
def constants : List Instr :=
  [.movz .x .x6 64 0, .vop (.dup .b16 c64 .x6), .movz .x .x6 128 0, .vop (.dup .b16 c128 .x6)]

/-- `x8 := n / 16`, whether a whole batch is left. -/
def wholeLeft : Instr := .lsr .x .x8 .x2 4

/-- Batches of sixteen blocks, in place, while there are that many. -/
def wide (up : Bool) : Prog isa :=
  .seq (.block [wholeLeft])
    (.ite (.zero .x .x8) (.block [])
      (.loop (.seq (.block [.addImm .x .x4 .x1 0])
          (.seq (batch up) (.block [.addImm .x .x1 .x1 128, .subImm .x .x2 .x2 16, wholeLeft])))
        (.nonzero .x .x8)))

/-- Copy `x13` 8-byte blocks from `x11` to `x12`. -/
def copy : Prog isa :=
  .loop (.block [.ldr .x .x10 .x11 0, .str .x .x10 .x12 0, .addImm .x .x11 .x11 8,
      .addImm .x .x12 .x12 8, .subImm .x .x13 .x13 1]) (.nonzero .x .x13)

/-- The last `n < 16` blocks, through the working space. -/
def tail (up : Bool) : Prog isa :=
  .ite (.zero .x .x2) (.block [])
    (.seq (.block [.addImm .x .x11 .x1 0, .addImm .x .x12 .x3 tailOff, .addImm .x .x13 .x2 0])
      (.seq copy
        (.seq (.block [.addImm .x .x4 .x3 tailOff]) (.seq (batch up)
          (.seq (.block [.addImm .x .x11 .x3 tailOff, .addImm .x .x12 .x1 0,
              .addImm .x .x13 .x2 0])
            copy)))))

def ecb (up : Bool) : Prog isa :=
  .seq (.block (saveRegs ++ constants)) (.seq (wide up) (.seq (tail up) (.block restoreRegs)))

def encrypt : Prog isa := ecb true
def decrypt : Prog isa := ecb false

/-! ## Key expansion

`vg_blowfish_expand_key(key = x0, key_len = x1, schedule = x2)`. -/

/-- The name of the static holding the initial schedule (`Impl.Blowfish.initWords`). -/
def initSym : String := "VG_BLOWFISH_INIT"

def initConsts : List (String × List (BitVec 64)) := [(initSym, Impl.Blowfish.initWords)]

/-- The next key byte into the low byte of `w8` (shifted up), cycling:
the byte at `x0 + x10`, then `x10 := x10 + 1`, or 0 at `key_len`. -/
def keyByte : Prog isa :=
  .seq (.block [.add .x .x13 .x0 .x10, .ldrb .x14 .x13 0, .lsl .w .x8 .x8 8,
      .logic .orr .w .x8 .x8 .x14, .addImm .x .x10 .x10 1, .sub .x .x13 .x10 .x1])
    (.ite (.zero .x .x13) (.block [.movz .x .x10 0 0]) (.block []))

/-- The S-boxes' initial planes: 4096 bytes from `x9` to `x12`, 64 at a time. -/
def copyPlanes : Prog isa :=
  .seq (.block [.movz .x .x11 64 0])
    (.loop (.block ((List.range 4).map (fun r => .ldrq (tReg r) .x9 (16 * r)) ++
        (List.range 4).map (fun r => .strq (tReg r) .x12 (16 * r)) ++
        ([.addImm .x .x9 .x9 64, .addImm .x .x12 .x12 64, .subImm .x .x11 .x11 1] : List Instr)))
      (.nonzero .x .x11))

/-- One P-array entry: the next four key bytes into `w8`, XORed with the
initial entry at `x9`, written at `x12`. -/
def keyWord : Prog isa :=
  .seq (.block [.movz .x .x8 0 0])
    (.seq keyByte (.seq keyByte (.seq keyByte (.seq keyByte
      (.block [.ldr .w .x14 .x9 0, .logic .eor .w .x14 .x14 .x8, .str .w .x14 .x12 0,
        .addImm .x .x9 .x9 4, .addImm .x .x12 .x12 4, .subImm .x .x11 .x11 1])))))

/-- Pᵢ = (initial Pᵢ) XOR the next 32 bits of the key, for the 18 entries. -/
def keyP : Prog isa :=
  .seq (.block [.movz .x .x10 0 0, .movz .x .x11 18 0]) (.loop keyWord (.nonzero .x .x11))

/-- Write the word `w` at entry `x14` of the S-boxes' planes. -/
def storeEntry (w : Reg) (e : Nat) : List Instr :=
  [.strb w .x14 e, .lsr .w .x13 w 8, .strb .x13 .x14 (256 + e), .lsr .w .x13 w 16,
   .strb .x13 .x14 (512 + e), .lsr .w .x13 w 24, .strb .x13 .x14 (768 + e)]

/-- After an encryption (xL in lane 0 of `v8`, xR in lane 0 of `v4`): its
output replaces the next two entries; then xL and xR go back to `A` and
`B` for the next. `x9` counts the P-array's pairs left, `x12` points at
the next P-array entry, `x14` at the next S-box entry and `x10` counts the
entries left in its S-box. -/
def replace : Prog isa :=
  .seq (.block [.umov .w .x6 (bReg 0) 0, .umov .w .x8 (aReg 0) 0])
    (.seq (.ite (.nonzero .x .x9)
        (.block [.str .w .x6 .x12 0, .str .w .x8 .x12 4, .addImm .x .x12 .x12 8,
          .subImm .x .x9 .x9 1])
        (.seq (.block (storeEntry .x6 0 ++ storeEntry .x8 1 ++
            ([.addImm .x .x14 .x14 2, .subImm .x .x10 .x10 2] : List Instr)))
          (.ite (.zero .x .x10) (.block [.addImm .x .x14 .x14 768, .movz .x .x10 256 0])
            (.block []))))
      (.block [.vop (.mov .v0 (aReg 0)), .vop (.mov (aReg 0) (bReg 0)),
        .vop (.mov (bReg 0) .v0), .subImm .x .x15 .x15 1]))

/-- The 521 encryptions, from the all-zero block. -/
def encryptions : Prog isa :=
  .seq (.block ((List.range 4).flatMap (fun k => [.vop (.movi0 (aReg k)), .vop (.movi0 (bReg k))]) ++
      ([.movz .x .x9 9 0, .addImm .x .x12 .x2 2048, .addImm .x .x12 .x12 2048,
       .addImm .x .x14 .x2 0, .movz .x .x10 256 0, .movz .x .x15 521 0] : List Instr)))
    (.loop (.seq (cipher .x2 true) replace) (.nonzero .x .x15))

/-- The low halves of `v8`–`v14` (which the calling convention preserves) into
the general-purpose registers the encryptions leave alone, and `v15` into
`v27`; and back. Key expansion needs no other working space. -/
def keepRegs : List (Reg × VReg) :=
  [(.x0, .v8), (.x1, .v9), (.x3, .v10), (.x4, .v11), (.x11, .v12), (.x16, .v13), (.x17, .v14)]
def saveLow : List Instr :=
  keepRegs.map (fun (x, v) => .umov .x x v 0) ++ ([.vop (.mov .v27 .v15)] : List Instr)
def restoreLow : List Instr :=
  keepRegs.map (fun (x, v) => .vop (.dup .d2 v x)) ++ ([.vop (.mov .v15 .v27)] : List Instr)

def expandKey : Prog isa :=
  .seq (.block (constants ++ ([.adrSym .x9 initSym, .addImm .x .x12 .x2 0] : List Instr)))
    (.seq copyPlanes (.seq keyP (.seq (.block saveLow) (.seq encryptions (.block restoreLow)))))

end VG.Impl.Blowfish.AArch64
