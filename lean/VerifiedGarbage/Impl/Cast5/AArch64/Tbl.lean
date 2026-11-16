module

public import VerifiedGarbage.Impl.Cast5.AArch64
public import VerifiedGarbage.Impl.Blowfish.AArch64

/-!
# CAST5 on AArch64: sixteen blocks at a time, S-boxes by `tbl`

As Blowfish's code (`Impl/Blowfish/AArch64.lean`), whose registers and
pieces this uses, the code works on sixteen blocks at once (a *batch*), one
per byte lane, and no S-box lookup reads memory at a secret address:

* The halves `L` and `R` of the sixteen blocks are sixteen 32-bit words
  each, four per register (`A`, `v4`–`v7`, and `B`, `v8`–`v11`), in block
  order.
* The S-boxes `S1`–`S4` are public constants. They are a table the code
  carries (`ldrqTbl`, the static `VG_CAST5_PLANES`, at a public address), in
  byte planes: byte `b` of `S_{j+1}[x]` at `1024 j + 256 b + x`
  (`Impl.Blowfish.AArch64.planeOff`, `planeBytes`).
* A round (`round`): `I = Kmᵢ ± R` or `Kmᵢ ^ R` for the sixteen words, in
  `fReg` (`v12`–`v15`); its rotation left by `Krᵢ mod 32`, the same secret
  amount in every lane, is a multiplication by `2 ^ (Krᵢ mod 32)`
  (`umull`, whose 64-bit product's halves are ORed), that power computed in
  `w4` by the five selected rotations of 1 (`rotate`, `Impl/Cast5/AArch64.lean`);
  `uzp` splits `I` into four planes of sixteen bytes (`Ia`, `Ib`, `Ic`,
  `Id`, in `v16`–`v19`); each plane indexes its S-box: for each of the
  S-box's four byte planes, one `tbl` and three `tbx` of four registers
  (`v28`–`v31`, loaded with a quarter of the plane), on the index XORed with
  0, 64, 128 and 192, exactly one of which is in range of its quarter; `zip`
  turns the four byte planes found back into words, which are combined into
  `f` (`v12`–`v15`) by the round's type; then `(L, R) := (R, L ^ f)`.

Timing depends only on the pointers, `rounds`, `n` and loop counters: every
secret is in a register, and `tbl`, `tbx` and `umull` take a time
independent of their data. `v8`–`v15` are callee-saved: ECB saves them in
its working space. No instruction outside the baseline ISA is used.
-/

@[expose] public section

namespace VG.Impl.Cast5.AArch64.Tbl

open VG.AArch64
open VG.Impl.Blowfish.AArch64 (aReg bReg fReg idxReg outReg qReg tReg c64 c128 veor vperm planes
  planeOff words wordReg loadBatch storeBatch constants copy saveRegs restoreRegs wholeLeft tailOff)

/-! ## The table -/

def planesSym : String := "VG_CAST5_PLANES"

/-- `S1`–`S4`, each as the list of its 256 entries. -/
def sboxes : List (List Spec.Cast5.Word) :=
  [Spec.Cast5.s1.toList, Spec.Cast5.s2.toList, Spec.Cast5.s3.toList, Spec.Cast5.s4.toList]

/-- The table's 4096 bytes: for each S-box, its four byte planes, each the
256 entries' bytes in order. -/
def planeBytes : List Byte :=
  sboxes.flatMap fun s => (List.range 4).flatMap fun b => s.map fun w => w.extractLsb' (8 * b) 8

/-- Bytes as little-endian quadwords, eight at a time. -/
def pack : List Byte → List (BitVec 64)
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
    (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) :: pack rest
  | _ => []

/-- The table, as 512 little-endian quadwords. It is built by passes over
the S-boxes' entries in order, never by indexing them, which the kernel,
evaluating the code that carries the table, would do one step at a time. -/
def planeWords : List (BitVec 64) := pack planeBytes

/-! ## The round function -/

/-- Quarter `q` of byte plane `b` of S-box `j`, from the table at `x9`, into
`v28`–`v31`. -/
def loadQuarter (j b q : Nat) : List Instr :=
  (List.range 4).map fun r => .ldrqTbl (tReg r) .x9 (planeOff j b + 64 * q + 16 * r) planesSym planeWords

/-- Byte plane `b` of S-box `j` at the indices in `idxReg j`, into
`outReg b`: a `tbl` of the first quarter, then a `tbx` of each other. -/
def lookupPlane (j b : Nat) : List Instr :=
  (List.range 4).flatMap fun q =>
    loadQuarter j b q ++
      ([.vop (.tblN (q != 0) 4 (outReg b) (tReg 0) (if q = 0 then idxReg j else qReg q))] : List Instr)

/-- S-box `j` at the indices in `idxReg j`, in byte planes in `outReg`. -/
def lookup (j : Nat) : List Instr :=
  [veor (qReg 1) (idxReg j) c64, veor (qReg 2) (idxReg j) c128, veor (qReg 3) (qReg 1) c128] ++
    (List.range 4).flatMap (lookupPlane j)

/-- The operations of §2.2. -/
inductive Op | add | eor | sub
  deriving DecidableEq, Repr

def Op.instr (o : Op) (d n m : VReg) : Instr :=
  match o with
  | .add => .vop (.add .s4 d n m)
  | .eor => veor d n m
  | .sub => .vop (.sub .s4 d n m)

/-- The operation of a round of Type `t` (1, 2 or 3) at place `p`: the
mask's (`Kmᵢ` and `R`) for 0, then those that take in `S2`, `S3` and `S4`. -/
def op (t p : Nat) : Op :=
  match t, p with
  | 1, 0 => .add | 1, 1 => .eor | 1, 2 => .sub | 1, _ => .add
  | 2, 0 => .eor | 2, 1 => .sub | 2, 2 => .add | 2, _ => .eor
  | _, 0 => .sub | _, 1 => .add | _, 2 => .eor | _, _ => .sub

/-- `f`'s accumulation of S-box `j`, for a round of Type `t`. -/
def combine (t j : Nat) : List Instr :=
  (List.range 4).map fun k =>
    if j = 0 then .vop (.mov (fReg k) (wordReg k)) else (op t j).instr (fReg k) (fReg k) (wordReg k)

/-- `f` of the words whose planes are in `idxReg`, into `fReg`. -/
def f (t : Nat) : List Instr :=
  (List.range 4).flatMap fun j => lookup j ++ words ++ combine t j

/-- The power of two in every lane of the rotation. -/
def mulReg : VReg := .v27

/-- `Kmᵢ` (at `x5`) in every lane of `v0`, and `2 ^ (Krᵢ mod 32)` (`Krᵢ` at
`x5 + 64`) in every lane of `mulReg`: 1 in `w4`, rotated left by `Krᵢ`. -/
def subkeys : List Instr :=
  ([.ldr .w .x6 .x5 0, .vop (.dup .s4 .v0 .x6), .ldr .w .x13 .x5 64, .movz .w .x4 1 0] : List Instr) ++
    rotate ++ ([.vop (.dup .s4 mulReg .x4)] : List Instr)

/-- The words of `fReg k` rotated left by the amount whose power of two is in
every lane of `mulReg`. -/
def rotl (k : Nat) : List Instr :=
  [.vop (.umull false .v0 (fReg k) mulReg), .vop (.umull true .v1 (fReg k) mulReg),
   vperm .uzp1 .s4 (outReg 0) .v0 .v1, vperm .uzp2 .s4 (outReg 1) .v0 .v1,
   .vop (.logic .orr (fReg k) (outReg 0) (outReg 1))]

/-- `(L, R)` (in `A`, `B`) := `(R, L ^ f)`, `f` in `fReg`. -/
def feistel : List Instr :=
  (List.range 4).map (fun k => veor (fReg k) (aReg k) (fReg k)) ++
  (List.range 4).map (fun k => .vop (.mov (aReg k) (bReg k))) ++
  (List.range 4).map (fun k => .vop (.mov (bReg k) (fReg k)))

/-- A round of Type `t` (1, 2 or 3) with the subkeys `Kmᵢ` at `x5` and `Krᵢ`
at `x5 + 64`; then `x5` to the next round's: up for encryption, down for
decryption. The batch's pointer, `x4`, which the rotation's power of two
overwrites, is kept in `x17`. -/
def round (t : Nat) (up : Bool) : List Instr :=
  subkeys ++ (List.range 4).map (fun k => (op t 0).instr (fReg k) .v0 (bReg k)) ++
  (List.range 4).flatMap rotl ++ planes fReg ++ f t ++ feistel ++
  [if up then .addImm .x .x5 .x5 4 else .subImm .x .x5 .x5 4]

/-- Three rounds, of Types 1, 2 and 3 (encryption) or 3, 2 and 1
(decryption), then the count of groups left (`x7`) down. -/
def group (up : Bool) : List Instr :=
  round (if up then 1 else 3) up ++ round 2 up ++ round (if up then 3 else 1) up ++
    ([.subImm .x .x7 .x7 1] : List Instr)

/-- `x7` := `rounds / 4 + 1`: 4 groups for 12 rounds, 5 for 16; `x8` :=
`rounds - 16`, zero if there are 16; the number of rounds is in `x16`. -/
def groups : List Instr :=
  [.lsr .x .x7 .x16 2, .addImm .x .x7 .x7 1, .subImm .x .x8 .x16 16]

/-- The rounds on `L` in `A` and `R` in `B`, in place: the subkeys at `x0`,
their number in `x16`, the table's address in `x9`. Encryption (`up`): rounds
1–15 in groups of three, then round 16 if there are 16. Decryption: round 16
if there are 16, then the rest in groups of three, down from the last;
`x5` starts at `Kmₙ`, `x0 + 4 (rounds - 1)`. -/
def cipher (up : Bool) : Prog isa :=
  if up then
    .seq (.block (([.addImm .x .x5 .x0 0] : List Instr) ++ groups))
      (.seq (.loop (.block (group true)) (.nonzero .x .x7))
        (.ite (.zero .x .x8) (.block (round 1 true)) (.block [])))
  else
    .seq (.block (([.lsl .x .x5 .x16 2, .add .x .x5 .x5 .x0, .subImm .x .x5 .x5 4] : List Instr) ++
        groups))
      (.seq (.ite (.zero .x .x8) (.block (round 1 false)) (.block []))
        (.loop (.block (group false)) (.nonzero .x .x7)))

/-! ## Batches -/

/-- Sixteen blocks at `x4`, in place, under the subkeys at `x0`: the batch's
pointer is kept in `x17` across the rounds, which use `w4`. The output is
`(Rₙ, Lₙ)`: `storeBatch` writes `B` first. -/
def batch (up : Bool) : Prog isa :=
  .seq (.block (loadBatch .x4 ++ ([.addImm .x .x17 .x4 0] : List Instr)))
    (.seq (cipher up) (.block (([.addImm .x .x4 .x17 0] : List Instr) ++ storeBatch .x4)))

/-! ## ECB

`vg_cast5_ecb_{en,de}crypt(schedule = x0, rounds = x1, data = x2, n = x3,
scratch = x4)`. The arguments move to the registers of Blowfish's ECB, whose
shape this has: the data's address to `x1`, `n` to `x2`, the working space to
`x3` (a batch for the last blocks, 128 bytes, then the saved `q8`–`q15`, 128
bytes), and the number of rounds to `x16`. -/

/-- The arguments to where the batches expect them. -/
def entry : List Instr :=
  [.addImm .x .x16 .x1 0, .addImm .x .x1 .x2 0, .addImm .x .x2 .x3 0, .addImm .x .x3 .x4 0]

/-- 64 and 128 in every byte of `c64` and `c128`, and the table's address in `x9`. -/
def setup : List Instr := constants ++ ([.adrSym .x9 planesSym] : List Instr)

/-- Batches of sixteen blocks, in place, while there are that many. -/
def wide (up : Bool) : Prog isa :=
  .seq (.block [wholeLeft])
    (.ite (.zero .x .x8) (.block [])
      (.loop (.seq (.block [.addImm .x .x4 .x1 0])
          (.seq (batch up) (.block [.addImm .x .x1 .x1 128, .subImm .x .x2 .x2 16, wholeLeft])))
        (.nonzero .x .x8)))

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
  .seq (.block (entry ++ saveRegs ++ setup)) (.seq (wide up) (.seq (tail up) (.block restoreRegs)))

def ecbEncrypt : Prog isa := ecb true
def ecbDecrypt : Prog isa := ecb false

end VG.Impl.Cast5.AArch64.Tbl
