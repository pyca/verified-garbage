import VerifiedGarbage.Impl.CmacTripleDes.Index
import VerifiedGarbage.Impl.Tbl.AArch64

/-!
# DES on AArch64, in constant time: the round, the block and the key schedule

The S-boxes are looked up with `tbl` (`Impl/Tbl/AArch64.lean`), two boxes
to a 64-byte table (`boxTable`), the four tables in `v16`–`v31`; bit
permutations are XORs of rotated and masked *groups* of a word (`groups`,
`linCode`), with constants built with `movz` and `movk` (`movImm`).

`L` and `R` are kept rotated left by 13 bits and *spread* (`xSrc`): bits
`8 m … 8 m + 5` of byte `m < 4` are bits `8 m … 8 m + 5` of the rotated
word, and those of byte `4 + m` its bits `8 m + 4 … 8 m + 9` (mod 32). Then
byte `laneOf i` holds, in its low six bits, the six bits of `R` that the
expansion gives box `i`, so the S-boxes' indices are the spread `R` XORed
with the round key spread the same way (`spread`, which also sets each
byte's top two bits to its box's table). The S-boxes' outputs come back in
one word, `y` (bit `posOf i q` of byte `laneOf i` is output bit `q` of box
`i`), and `L ⊕ f(R, K)`, spread, is `L` XORed with groups of `y`
(`ySrc`): the rotation and the spreading are folded into the
permutation `P`, and the initial and final permutations into `IP` and
`IP⁻¹`.

`block` (TDEA encryption of the block in `x5`, with the key schedule at
`x14` and the scratch buffer at `x15`) first spreads the 48 round keys into
the scratch buffer (`spreadBody`, two at a time, by a `tbl` from four
shifted copies of them), loads the tables and the constants, and then runs
the three passes from the spread keys. It uses `x0`, `x5`–`x13`, `x16` and
`x17`, and the caller-saved vector registers `v0`–`v7` and `v16`–`v31`.
-/

namespace VG.Impl.CmacTripleDes.AArch64

open VG.AArch64 VG.Impl.CmacTripleDes

/-- `mov d, n`. -/
def mov (d n : Reg) : Instr := .addImm .x d n 0

/-- The constant `v` into `d`: `movz` of its low halfword, and `movk` of
each other nonzero one. -/
def movImm (d : Reg) (v : Nat) : List Instr :=
  .movz .x d (BitVec.ofNat 16 v) 0 ::
    ((List.range 3).filterMap fun h =>
      if (v >>> (16 * (h + 1))) % 65536 = 0 then none
      else some (.movk .x d (BitVec.ofNat 16 (v >>> (16 * (h + 1)))) (h + 1)))

/-! ## Bit permutations -/

/-- The groups of a bit map: for each rotation `r` (right) that some
destination bit `d < n` needs (its source `src d` is bit `(d + r) % 64`),
the mask of those destination bits. -/
def groups (src : Nat → Option Nat) (n : Nat) : List (Nat × Nat) :=
  -- Every rotation's mask at once, in one pass over the bits (the kernel
  -- evaluates this): rotation `r`'s in bits `[n r, n r + n)` of `ms`.
  let ms := (List.range n).foldl (fun ms d =>
    match src d with
    | some s => ms ||| (2 ^ d) <<< (n * ((s + 64 - d) % 64))
    | none => ms) 0
  (List.range 64).filterMap fun r =>
    let m := (ms >>> (n * r)) % 2 ^ n
    if m = 0 then none else some (r, m)

/-- One group: `src` rotated right by `r`, masked by `m` (in `u`), into `t`. -/
def group (src t u : Reg) (r m : Nat) : List Instr :=
  movImm u m ++
    (if r = 0 then [.logic .and .x t src u] else [.ror .x t src r, .logic .and .x t t u])

/-- The XOR of the groups `gs` of `src` into `dst` (`t` and `u` are
clobbered); `dst` is first set to the first group if `init`. -/
def linCode (src dst t u : Reg) (init : Bool) : List (Nat × Nat) → List Instr
  | [] => []
  | (r, m) :: gs =>
    if init then group src dst u r m ++ linCode src dst t u false gs
    else group src t u r m ++ [.logic .eor .x dst dst t] ++ linCode src dst t u false gs

/-! ## The layout -/

/-- `L` and `R` are kept rotated left by `rot` bits. -/
def rot : Nat := 13

/-- The byte of the spread words that holds box `i`'s input. -/
def laneOf (i : Nat) : Nat := [1, 4, 0, 7, 3, 6, 2, 5].getD i 0

/-- The table (a quarter of the table registers) of box `i`. -/
def boxTable (i : Nat) : Nat := [0, 1, 0, 2, 1, 2, 3, 3].getD i 0

/-- The bit of a table byte holding output bit `q` of box `i`. -/
def posOf (i q : Nat) : Nat :=
  ([[4, 0, 2, 6], [5, 1, 7, 2], [5, 1, 3, 7], [2, 5, 3, 1], [4, 6, 0, 3], [0, 4, 6, 7],
    [0, 5, 3, 7], [6, 4, 1, 2]].getD i []).getD q 0

/-- Bit `p` of a spread word (for `p % 8 < 6`) is bit `xSrc p` of the rotated word. -/
def xSrc (p : Nat) : Nat := if p < 32 then p else (p - 28) % 32

/-- The spread bits. -/
def xBit (p : Nat) : Bool := p < 64 && p % 8 < 6

/-- A position of bit `e` of the rotated word in the spread word. -/
def xPos (e : Nat) : Nat := if e % 8 < 6 then e else 32 + (e + 28) % 32

/-- The byte of table `k` at index `x`: the outputs of its two boxes. -/
def sboxByte (k x : Nat) : BitVec 8 :=
  (List.range 8).foldl (fun b i =>
    if boxTable i = k then
      (List.range 4).foldl (fun b q =>
        if (Spec.TripleDes.sBox i (BitVec.ofNat 6 x)).getLsbD q then b ||| BitVec.twoPow 8 (posOf i q)
        else b) b
    else b) 0

/-- The table registers: the four tables of 64 bytes. -/
def sTable (k : Nat) : BitVec 8 := sboxByte (k / 64) (k % 64)

/-- The top two bits of each byte: its box's table. -/
def offsets : BitVec 64 :=
  (List.range 8).foldl (fun o i => o ||| BitVec.ofNat 64 (boxTable i * 64) <<< (8 * laneOf i)) 0

/-! ## The round -/

/-- 64, 128 and 192 in every byte of `v4`, `v5` and `v6`. -/
def quarterConsts : List Instr :=
  [.movz .x .x6 64 0, .vop (.dup .b16 .v4 .x6), .movz .x .x6 128 0, .vop (.dup .b16 .v5 .x6),
   .movz .x .x6 192 0, .vop (.dup .b16 .v6 .x6)]

/-- The S-boxes' indices: the spread key at `[x10]` (moving `x10` to the next
one, down if `down`) XORed with `b` (spread `R`), into `v0`, and XORed with
64, 128 and 192 into `v1`–`v3`. -/
def sIn (b : Reg) (down : Bool) : List Instr :=
  [.ldr .x .x5 .x10 0, if down then .subImm .x .x10 .x10 8 else .addImm .x .x10 .x10 8,
   .logic .eor .x .x5 .x5 b, .vop (.ins .d2 .v0 0 .x5),
   .vop (.logic .eor .v1 .v0 .v4), .vop (.logic .eor .v2 .v0 .v5), .vop (.logic .eor .v3 .v0 .v6)]

/-- The S-boxes' outputs, into `x5`. -/
def sOut : List Instr := Tbl.AArch64.select true ++ [.umov .x .x5 .v0 0]

/-- Bit `p` of the spread `P(S)` (rotated): its bit of `y`, the S-boxes' outputs. -/
def ySrc (p : Nat) : Option Nat :=
  if xBit p then
    let u := pSrc ((xSrc p + 32 - rot) % 32)
    let i := 7 - u / 4
    some (8 * laneOf i + posOf i (u % 4))
  else none

/-- The groups of `P`, in three parts. -/
def pGroups : List (Nat × Nat) := groups ySrc 64

/-- `a := a ⊕ P(y)`, spread: three sums of groups, into `x6`, `x9` and `x17`. -/
def pOut (a : Reg) : List Instr :=
  linCode .x5 .x6 .x7 .x8 true (pGroups.take 4) ++
  linCode .x5 .x9 .x13 .x0 true ((pGroups.drop 4).take 4) ++
  linCode .x5 .x17 .x7 .x8 true (pGroups.drop 8) ++
  [.logic .eor .x a a .x6, .logic .eor .x .x9 .x9 .x17, .logic .eor .x a a .x9]

/-- One round: `a := a ⊕ f(b, K)`, spread. -/
def round (a b : Reg) (down : Bool) : List Instr := sIn b down ++ sOut ++ pOut a

/-- Sixteen rounds, alternately on `x11` and `x12`, `x16` counting pairs. -/
def pass (down : Bool) : Prog isa :=
  .seq (.block [.movz .x .x16 8 0])
    (.loop (.block (round .x11 .x12 down ++ round .x12 .x11 down ++ [.subImm .x .x16 .x16 1]))
      (.nonzero .x .x16))

/-- Between passes: `x10` to the next pass's first key (`d` bytes on), and
`L` and `R` exchanged. -/
def passTail (d : Nat) : List Instr :=
  [.addImm .x .x10 .x10 d, mov .x5 .x11, mov .x11 .x12, mov .x12 .x5]

/-! ## The block -/

/-- `IP` of the block in `x5`, its two halves rotated and spread: `L` into
`x11`, `R` into `x12`. -/
def ipCode : List Instr :=
  linCode .x5 .x11 .x6 .x7 true
    (groups (fun p => if xBit p then some (ipSrc (32 + (xSrc p + 32 - rot) % 32)) else none) 64) ++
  linCode .x5 .x12 .x6 .x7 true
    (groups (fun p => if xBit p then some (ipSrc ((xSrc p + 32 - rot) % 32)) else none) 64)

/-- `IP⁻¹(R ‖ L)` into `x5`, with `R` in `x12` and `L` in `x11` (after the
last pass, rotated and spread). -/
def fpCode : List Instr :=
  linCode .x12 .x5 .x6 .x7 true
    (groups (fun j => if j < 64 ∧ 32 ≤ fpSrc j then some (xPos ((fpSrc j - 32 + rot) % 32)) else none) 64) ++
  linCode .x11 .x5 .x6 .x7 false
    (groups (fun j => if j < 64 ∧ fpSrc j < 32 then some (xPos ((fpSrc j + rot) % 32)) else none) 64)

/-- Byte `e` of the index that gathers the spread keys: in the low 8 bytes,
for the byte of box `i`, the byte of `K ≫ (6 (7 - i) mod 8)` that holds box
`i`'s bits (`v0`–`v3` hold `K` shifted by 0, 2, 4 and 6), and in the high 8
bytes the same for the next key. -/
def gatherIndex (e : Nat) : BitVec 8 :=
  let i := (List.range 8).find? (fun i => laneOf i = e % 8) |>.getD 0
  let o := 6 * (7 - i)
  BitVec.ofNat 8 (16 * (o % 8 / 2) + o / 8 + 8 * (e / 8))

/-- The gathering index (`v5`), 63 in every byte (`v6`) and the offsets in
both halves (`v7`); `x6` and `x7` to the keys and the scratch buffer, and
`x16` counting pairs of keys. -/
def spreadPre : List Instr :=
  Tbl.AArch64.const128 .v5 (ofVBytes gatherIndex) ++
  [.movz .x .x6 63 0, .vop (.dup .b16 .v6 .x6)] ++ Tbl.AArch64.const64 .x6 offsets ++
  [.vop (.dup .d2 .v7 .x6), mov .x6 .x14, mov .x7 .x15, .movz .x .x16 24 0]

/-- Two round keys spread into the scratch buffer. -/
def spreadBody : List Instr :=
  [.ldrq .v0 .x6 0, .vop (.shift .ushr .d2 .v1 .v0 2), .vop (.shift .ushr .d2 .v2 .v0 4),
   .vop (.shift .ushr .d2 .v3 .v0 6), .vop (.tblN false 4 .v4 .v0 .v5),
   .vop (.logic .and .v4 .v4 .v6), .vop (.logic .eor .v4 .v4 .v7), .strq .v4 .x7 0,
   .addImm .x .x6 .x6 16, .addImm .x .x7 .x7 16, .subImm .x .x16 .x16 1]

/-- The tables, the quarters' constants, `IP`, and `x10` to the first spread key. -/
def setup : List Instr :=
  Tbl.AArch64.loadTable sTable ++ quarterConsts ++ ipCode ++ [mov .x10 .x15]

/-- TDEA encryption (`E_K3(D_K2(E_K1(x)))`) of the block `x` in `x5` (as a
64-bit integer), into `x5`, with the key schedule at `x14`: the passes share
one `IP` and one `IP⁻¹`, which cancel between them. -/
def block : Prog isa :=
  .seq (.block spreadPre) (.seq (.loop (.block spreadBody) (.nonzero .x .x16))
    (.seq (.block setup) (.seq (.seq (pass false) (.block (passTail 120)))
      (.seq (.seq (pass true) (.block (passTail 136))) (.seq (pass false) (.block fpCode))))))

/-! ## The key schedule -/

/-- The sixteen round keys of the DES key in `x5` (as a 64-bit integer), to
`[x2 + 8 j]`. -/
def roundKeys : List Instr :=
  (List.range 16).flatMap fun j =>
    linCode .x5 .x6 .x7 .x11 true (groups (fun q => if q < 48 then some (rkSrc j q) else none) 48) ++
      [.str .x .x6 .x2 (8 * j)]

end VG.Impl.CmacTripleDes.AArch64
