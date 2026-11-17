module

public import VerifiedGarbage.Spec.Sha3
public import VerifiedGarbage.Impl.Sha3.Tables
public import VerifiedGarbage.TCB.Arm.Isa

/-!
# Keccak-f[1600]: ARMv7 implementation

`vg_keccak_f1600(state = r0, scratch = r1)`.

The rounds run on *interleaved* lanes: each 64-bit lane is two 32-bit words,
its bits at even positions and its bits at odd positions (`half`). A
rotation of a lane is then a rotation of each word (and, by an odd count,
their exchange: `rotSrc`), which costs nothing as the rotated second operand
of the instruction that uses it. So no word is ever rotated in place: a
register or a word of memory holds its value rotated left by a count the
code knows (`rot`, `colRot`, `dRot`), and each instruction rotates its
second operand by the difference of the two counts.

`scratch` (512 bytes) is laid out as:

* `[0, 200)`: the state, interleaved: word `h` of lane `j`, rotated left by
  `rot j h`, at `wOff j h`. The rounds alternate it with `state`: each round
  reads one (`src`) and writes the other (`dst`), and the 24 rounds start
  and end here;
* `[200, 392)`: the 24 round constants, interleaved, stored by the prologue;
* `[392, 396)`: a pointer to the next round's constant;
* `[396, 432)`: the saved `r4`–`r11` and `lr`.

`r0` (`state`) and `r1` (`scratch`) are never written. The prologue
interleaves the lanes of `state` into `scratch` (`toStored`) and the
epilogue brings them back (`ofStored`), each by five exchanges of bits
between the lane's two words (`swaps`).

A round (`round src dst`) computes the ten words of the column parities
`C[x]` (θ) in the registers `creg x h`; then the ten words of `D[x]`, in the
registers of `C[x - 1]`, but those of `dMem`, which it stores in `dst`, in
words that the round writes last; then the output, half a plane at a time
(`halfPlane`): the five words `B[x]` of `π(ρ(θ(A)))`, each a word of `src`
XOR a word of `D`, in the registers `breg x`, and `B[x] ⊕ (¬B[x+1] ∧
B[x+2])` (χ) stored in `dst`. ι is last, on lane 0 of `dst`. The loop runs
two rounds per iteration.

Every address is a pointer plus a constant or the round constant pointer,
which is public, and the only branch is the round loop's, which depends
only on the pointers, so only the pointers can affect timing.
-/

@[expose] public section

namespace VG.Impl.Sha3.Arm

open VG.Arm
open VG.Impl.Sha3 (rhoOff piSrc)

/-- `++`, grouping to the right: the kernel evaluates the code, and
`(a ++ b) ++ c` has it copy `a` twice. -/
local infixr:65 " +++ " => HAppend.hAppend

/-! ## Interleaved lanes -/

/-- The low `n` bits at even positions of `x`. -/
def evenBits (x : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => x % 2 + 2 * evenBits (x / 4) n

/-- The 32 bits of a lane at even positions (`h = 0`) or at odd positions
(`h = 1`): bit `i` is bit `2i + h` of the lane. -/
def half (h : Nat) (x : BitVec 64) : BitVec 32 := BitVec.ofNat 32 (evenBits (x.toNat >>> h) 32)

/-- Half `h` of a lane rotated left by `ρ` is half `(rotSrc ρ h).1` of the
lane, rotated left by `(rotSrc ρ h).2`. -/
def rotSrc (ρ h : Nat) : Nat × Nat :=
  if ρ % 2 = 0 then (h, ρ / 2 % 32) else if h = 0 then (1, (ρ / 2 + 1) % 32) else (0, ρ / 2 % 32)

/-- `a - b` modulo 32, for `b ≤ 32`. -/
def sub32 (a b : Nat) : Nat := (a + 32 - b) % 32

/-- The register holding half `h` of `C[x]` holds it rotated left by
`colRot x h`: as the word of the column that the round before computed
from lane `5x + 1` was stored (`rot`), for `x ≠ 0`. -/
def colRot (x h : Nat) : Nat := if x = 0 then 0 else sub32 0 (rotSrc (rhoOff (5 * x + 1)) h).2

/-- Half `h` of `D[x]` is computed rotated left by `dRot x h`, as `C[x - 1]`. -/
def dRot (x h : Nat) : Nat := colRot ((x + 4) % 5) h

/-- Half `h` of lane `j` is stored rotated left by `rot j h`: as χ leaves
it, computed from a word of `B` that is a word of `D` XOR a word of the
state rotated to it, so rotated as that word of `D` and not yet by ρ. Lane
0, which ρ does not rotate, is stored as it is. -/
def rot (j h : Nat) : Nat :=
  if j = 0 then 0 else
    let s := piSrc (j % 5) (j / 5)
    sub32 (dRot (s % 5) (rotSrc (rhoOff s) h).1) (rotSrc (rhoOff s) h).2

/-- The offset of half `h` of lane `j`. -/
def wOff (j h : Nat) : Nat := 8 * j + 4 * h

/-- The register `r` rotated right by `n < 32`, as a second operand. -/
def ror (r : Reg) (n : Nat) : Op2 := if n = 0 then .reg r else .shifted r .ror n

/-! ## A round -/

/-- The register of half `h` of `C[x]`. -/
def creg (x h : Nat) : Reg :=
  if h = 0 then [Reg.r2, .r4, .r6, .r8, .r10].getD x .r2 else [Reg.r3, .r5, .r7, .r9, .r11].getD x .r3

/-- The temporaries. -/
def T : Reg := .r12
def U : Reg := .lr

/-- The plane of the word of column `x` that the register of `C[x]` starts
from, and so is rotated as: the one computed from lane `5x + 1`. -/
def anchor (x : Nat) : Nat := if x = 0 then 0 else (2 + 3 * x) % 5

/-- Half `h` of `C[x] = A[x, 0] ⊕ … ⊕ A[x, 4]`, from the state at `src`. -/
def column (src : Reg) (x h : Nat) : List Instr :=
  .ldr (creg x h) src (wOff (x + 5 * anchor x) h) ::
    ((List.range 5).filter (· ≠ anchor x)).flatMap fun y =>
      [.ldr T src (wOff (x + 5 * y) h),
        .dp .eor (creg x h) (creg x h) (ror T (sub32 (rot (x + 5 * y) h) (colRot x h)))]

/-- The `D[x]` kept in `dst` (the others are in registers). -/
def dMem (x : Nat) : Bool := x = 0 || x = 3

/-- Where in `dst`: words of plane 4, which the round writes last. -/
def dOff (x h : Nat) : Nat := wOff (20 + (if x = 0 then 0 else 2) + h) 1

/-- `D[x] = C[x - 1] ⊕ ROTL¹(C[x + 1])`: in the registers of `C[x - 1]`, or
stored in `dst`. -/
def dcol (dst : Reg) (x : Nat) : List Instr :=
  let a := (x + 4) % 5
  let b := (x + 1) % 5
  let e := ror (creg b 1) (sub32 (sub32 (colRot b 1) 1) (colRot a 0))
  let o := ror (creg b 0) (sub32 (colRot b 0) (colRot a 1))
  if dMem x then
    [.dp .eor T (creg a 0) e, .str T dst (dOff x 0), .dp .eor T (creg a 1) o, .str T dst (dOff x 1)]
  else [.dp .eor (creg a 0) (creg a 0) e, .dp .eor (creg a 1) (creg a 1) o]

/-- The order of the `D[x]`: each after the one that reads the registers it
overwrites, but the first, which is stored. -/
def dOrder : List Nat := [0, 2, 4, 1, 3]

/-- The register of `B[x]`: those of `C[2]` and `C[4]`, which hold no `D`,
and `U`. -/
def breg (x : Nat) : Reg := [creg 2 0, creg 2 1, creg 4 0, creg 4 1, U].getD x U

/-- Half `h` of `B[x] = ROTL^ρ(A[piSrc x y] ⊕ D[(x + 3y) mod 5])` for plane
`y`, rotated left by `rot (x + 5 y) h`: the word of the state rotated to
the word of `D`, but for lane 0, where the word of `D` is rotated to it. -/
def laneB (src dst : Reg) (x y h : Nat) : List Instr :=
  let j := piSrc x y
  let h' := (rotSrc (rhoOff j) h).1
  let u := j % 5
  let d := if dMem u then T else creg ((u + 4) % 5) h'
  ([.ldr (breg x) src (wOff j h')] : List Instr) ++
    (if dMem u then [.ldr T dst (dOff u h')] else []) ++
    [if x = 0 ∧ y = 0 then .dp .eor (breg x) (breg x) (ror d (sub32 (dRot u h') (rot j h')))
      else .dp .eor (breg x) d (ror (breg x) (sub32 (rot j h') (dRot u h')))]

/-- Half `h` of lane `(x, y)` of χ's output, `B[x] ⊕ (¬B[x+1] ∧ B[x+2])`,
stored in `dst`. -/
def chi (dst : Reg) (x y h : Nat) : List Instr :=
  let p (x : Nat) := rot (x % 5 + 5 * y) h
  [.dp .bic T (breg ((x + 2) % 5)) (ror (breg ((x + 1) % 5)) (sub32 (p (x + 1)) (p (x + 2)))),
    .dp .eor T (breg x) (ror T (sub32 (p (x + 2)) (p x))),
    .str T dst (wOff (x + 5 * y) h)]

/-- Half `h` of plane `y` of χ's output. -/
def halfPlane (src dst : Reg) (y h : Nat) : List Instr :=
  (List.range 5).flatMap (fun x => laneB src dst x y h) ++ (List.range 5).flatMap (fun x => chi dst x y h)

/-- θ, ρ, π and χ, from `src` to `dst`. -/
def roundCore (src dst : Reg) : List Instr :=
  (List.range 5).flatMap (fun x => column src x 0 ++ column src x 1) +++
    dOrder.flatMap (dcol dst) +++
    (List.range 5).flatMap (fun y => halfPlane src dst y 0 ++ halfPlane src dst y 1)

/-- The offset in `scratch` of the pointer to the next round constant. -/
def rcPtr : Nat := 392

/-- ι, on lane 0 of `dst`; then advance to the next round constant. -/
def iota (dst : Reg) : List Instr :=
  [.ldr T .r1 rcPtr,
    .ldr U dst 0, .ldr (breg 0) T 0, .dp .eor U U (.reg (breg 0)), .str U dst 0,
    .ldr U dst 4, .ldr (breg 0) T 4, .dp .eor U U (.reg (breg 0)), .str U dst 4,
    .dp .add T T (.imm 8), .str T .r1 rcPtr]

/-- One round from `src` to `dst`. -/
def round (src dst : Reg) : List Instr := roundCore src dst +++ iota dst

/-- Two rounds, and set Z after the last. -/
def body : List Instr :=
  round .r1 .r0 +++ round .r0 .r1 +++
    [.ldr T .r1 rcPtr, .dp .sub T T (.reg .r1), .cmp T (.imm 392)]

/-! ## To and from the interleaved lanes -/

/-- The registers of a lane's two words, and a temporary. -/
def L : Reg := .r2
def H : Reg := .r3
def X : Reg := .r12

/-- `r := v` -/
def const32 (r : Reg) (v : BitVec 32) : List Instr :=
  .movw r (v.extractLsb' 0 16) :: (if v.extractLsb' 16 16 = 0 then [] else [.movt r (v.extractLsb' 16 16)])

/-- The exchanges that interleave a lane, of its low word in `L` and its
high word in `H`. A bit of the lane is in the word that bit 5 of its
position says, at the position in it that bits 4 to 0 say. Each exchange,
for `i` from 4 down to 0, is of the bits of `L` at the positions with bit
`i` set and the bits of `H` `2 ^ i` lower: it exchanges, in where each bit
of the lane is, the word and bit `i` of the position in the word. So after
the five the word of a bit is bit 0 of its position in the lane, and its
position in the word bits 5 to 1: `L` is the bits at even positions and `H`
those at odd positions. The same exchanges in the opposite order bring the
lane back. Each is given by its distance `2 ^ i`, and the register of its
mask (the positions with bit `i` clear) and the mask. -/
def swaps : List (Nat × Reg × BitVec 32) :=
  [(16, .r4, 0x0000ffff), (8, .r5, 0x00ff00ff), (4, .r6, 0x0f0f0f0f), (2, .r7, 0x33333333),
    (1, .r8, 0x55555555)]

/-- The masks, in their registers. -/
def masks : List Instr := swaps.flatMap fun (_, m, v) => const32 m v

/-- Exchange the bits of `L` at the positions `k` above those of the mask
`m` with the bits of `H` under the mask. (The bits of `X` are under the
mask, so its rotation is a shift left by `k`.) -/
def xswap (k : Nat) (m : Reg) : List Instr :=
  [.dp .eor X H (.shifted L .lsr k), .dp .and X X (.reg m), .dp .eor H H (.reg X),
    .dp .eor L L (.shifted X .ror (32 - k))]

/-- Lane `j` of the state at `r0`, interleaved and stored at `r1`. -/
def toStored (j : Nat) : List Instr :=
  ([.ldr L .r0 (8 * j), .ldr H .r0 (8 * j + 4)] : List Instr) ++
    swaps.flatMap (fun (k, m, _) => xswap k m) ++
    (if rot j 0 = 0 then [] else [.mov L (ror L (32 - rot j 0))]) ++
    (if rot j 1 = 0 then [] else [.mov H (ror H (32 - rot j 1))]) ++
    [.str L .r1 (wOff j 0), .str H .r1 (wOff j 1)]

/-- Lane `j` of the interleaved state at `r1`, stored at `r0`. -/
def ofStored (j : Nat) : List Instr :=
  ([.ldr L .r1 (wOff j 0), .ldr H .r1 (wOff j 1)] : List Instr) ++
    (if rot j 0 = 0 then [] else [.mov L (ror L (rot j 0))]) ++
    (if rot j 1 = 0 then [] else [.mov H (ror H (rot j 1))]) ++
    swaps.reverse.flatMap (fun (k, m, _) => xswap k m) ++ [.str L .r0 (8 * j), .str H .r0 (8 * j + 4)]

/-! ## The function -/

/-- The callee-saved registers we use (and `lr`), and where they are saved. -/
def saved : List (Reg × Nat) :=
  [(.r4, 396), (.r5, 400), (.r6, 404), (.r7, 408), (.r8, 412), (.r9, 416), (.r10, 420),
    (.r11, 424), (.lr, 428)]

/-- Round constant `k`, interleaved, built in `T` and stored at `scratch + 200 + 8k`. -/
def rcStore (k : Nat) : List Instr :=
  const32 T (half 0 (Spec.Sha3.RC k)) +++ [.str T .r1 (200 + 8 * k)] +++
    const32 T (half 1 (Spec.Sha3.RC k)) +++ [.str T .r1 (204 + 8 * k)]

/-- Interleave the state into `scratch`, and store the round constants. -/
def enter : List Instr :=
  masks +++ (List.range 25).flatMap toStored +++ (List.range 24).flatMap rcStore

/-- Save the registers, interleave the state, store the round constants, and
point at the first. -/
def prologue : List Instr :=
  saved.map (fun (r, d) => .str r .r1 d) +++ enter +++
    [.dp .add T .r1 (.imm 200), .str T .r1 rcPtr]

/-- Bring the state back from `scratch`. -/
def leave : List Instr := masks +++ (List.range 25).flatMap ofStored

def restore : List Instr := saved.map fun (r, d) => .ldr r .r1 d

/-- Bring the state back, and restore the registers. -/
def epilogue : List Instr := leave +++ restore

def permute : Prog isa :=
  .seq (.block prologue) (.seq (.loop (.block body) .ne) (.block epilogue))

end VG.Impl.Sha3.Arm
