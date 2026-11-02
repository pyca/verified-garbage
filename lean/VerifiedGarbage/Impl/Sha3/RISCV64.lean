module

public import VerifiedGarbage.Spec.Sha3
public import VerifiedGarbage.Impl.Sha3.Tables
public import VerifiedGarbage.Impl.Words64.RISCV64

/-!
# Keccak-f[1600]: RISC-V implementation

`vg_keccak_f1600(state = a0, scratch = a1)`.

The PPC64LE implementation's rounds (`VG.Impl.Sha3.PPC64LE`, after Andy
Polyakov's CRYPTOGAMS `keccak1600-x86_64`: the "lane complementing"
implementation, with the column parities and `D` in registers), for RV64I,
which has no rotation and faults on misaligned accesses:
* A rotation left by `n` is `slli` by `n` into the temporary `t6`, `srli`
  by `64 - n` and `or` (`rol`); a NOT is `xori` with `-1`. The registers
  are PPC64LE's renamed: `r5`–`r9` (row 4) are `a2`–`a6`, `r10`–`r12` and
  `r14`–`r17` are `a7`, `t0`, `t1` and `t2`–`t5`, and `r0` (the
  temporary) is `t6`.
* The state is an argument buffer, whose alignment the contract does not
  state, so the rounds run on a copy in a frame on the stack (`alloc`,
  16-byte aligned), which the prologue loads and the epilogue stores back:
  a doubleword at a time (`ld`, `sd`) if `state` is 8-byte aligned, as a
  Rust `[u64; 25]` is, and a byte at a time (`loadLE64`, `storeLE64`)
  otherwise, a branch on the pointer's low bits. The rounds alternate between the copy (`a0`) and a second
  state in the frame (`a1`): the first round of each iteration reads `a0`
  and writes `a1`, the second the other way round, so after the 24 rounds
  the result is back in the copy. `scratch` is not used.
* **Lane complementing.** While the rounds run, the lanes `1, 2, 8, 12, 17,
  20` (`complLanes`) of the state are kept complemented: that turns most of
  χ's `¬a ∧ b` into an `∧` or an `∨` of the lanes as they are, so that χ
  needs one NOT per plane instead of five. The copies in and out
  complement those lanes.

The frame (`frameBytes`, 608 bytes) is laid out as:

* `[0, 192)`: the 24 round constants, stored by the prologue (`movImm64`);
* `[192, 392)`: the copy of the state;
* `[392, 592)`: the second state;
* `[592, 608)`: the saved `s0` and `s1`.

`s1` holds `state`. The round constant of round `2i + k` is at `8k(s0)`,
where `s0` is the frame plus `16i`; the loop ends when `s0` reaches the
copy of the state (`a0`), after 12 iterations. Every address is a pointer
plus a constant, and the only branches are the round loop's and those on
`state`'s alignment, so only the pointers can affect timing.
-/

@[expose] public section

namespace VG.Impl.Sha3.RISCV64

open VG.RISCV64
open VG.Impl.Words64.RISCV64
open VG.Impl.Sha3 (complLanes)

/-- The temporary that lanes are loaded into, and that rotations use. -/
def T : Reg := .t6

/-! ## Instructions of a round, as on PPC64LE -/

/-- `r = A[i]` (lane `i` of the state at `b`). -/
def ld (r b : Reg) (i : Nat) : List Instr := [.load .d r b (8 * i)]
/-- `r ^= A[i]`. -/
def xl (r b : Reg) (i : Nat) : List Instr := [.load .d T b (8 * i), .logic .xor r r T]
/-- Lane `i` of the state at `b` is set to `r`. -/
def st (b : Reg) (i : Nat) (r : Reg) : List Instr := [.store .d r b (8 * i)]
def mv (r q : Reg) : List Instr := [.addi r q 0]
def xr (r q : Reg) : List Instr := [.logic .xor r r q]
def an (r q : Reg) : List Instr := [.logic .and r r q]
def orr (r q : Reg) : List Instr := [.logic .or r r q]
/-- A rotation left by `0 < n < 64`, through `T`. -/
def rol (r : Reg) (n : Nat) : List Instr :=
  [.shift .sll .d T r n, .shift .srl .d r r (64 - n), .logic .or r r T]
/-- `r = ¬r`. -/
def nt (r : Reg) : List Instr := [.logicImm .xor r r (-1)]

/-- A round from the state at `s`, up to ι: θ, the `B[x]` of plane 0 and
the first lane of its χ. -/
def roundA (s : Reg) : List Instr := List.flatten [
    -- C[x] = A[x, 4] ⊕ … ⊕ A[x, 0], loading A[0, 0], A[1, 1], A[2, 2], A[3, 3] (sources of
    -- plane 0) into a7, t0, t1, t2 and A[4, 4] into t3 on the way
    ld .a7 s 0, ld .t0 s 6, ld .t1 s 12, ld .t2 s 18,
    xl .a4 s 2, xl .a5 s 3, xr .a2 .a7, xl .a3 s 1,
    xl .a4 s 7, xl .a2 s 5, mv .t3 .a6, xl .a6 s 4,
    xr .a4 .t1, xl .a2 s 10, xl .a5 s 8, xr .a3 .t0,
    xl .a6 s 9, xl .a4 s 17, xl .a2 s 15, xl .a5 s 13,
    xl .a3 s 11, xl .a6 s 14,
    -- D[x] = ROTL¹(C[x + 1]) ⊕ C[x - 1], in place: D[1] in a4, D[4] in a2, D[2] in a5,
    -- D[0] in a3, D[3] in a6
    mv .t4 .a4, rol .a4 1,
    xr .a4 .a2, xr .a5 .t2, rol .a2 1, xr .a2 .a5,
    xl .a3 s 16, rol .a5 1, xr .a5 .a3, xl .a6 s 19,
    rol .a3 1, xr .a3 .a6, rol .a6 1, xr .a6 .t4,
    -- plane 0: B[x] = ROTL^ρ(A[x, x] ⊕ D[x]) in a7, t0, t1, t2, t3, and lane 0 of χ in t0
    xr .t0 .a4, xr .t1 .a5, rol .t0 44, xr .t2 .a6,
    xr .t3 .a2, rol .t1 43, xr .a7 .a3, mv .t4 .t0,
    rol .t2 21, orr .t0 .t1, xr .t0 .a7, rol .t3 14]

/-- The rest of the round from the state at `s` to the state at `d`, after ι. -/
def roundB (s d : Reg) : List Instr := List.flatten [
    -- the rest of plane 0's χ, loading plane 1's sources
    mv .t5 .t3, an .t3 .t2, st d 0 .t0, xr .t3 .t1,
    nt .t1, st d 2 .t3, orr .t1 .t2, ld .t3 s 22,
    xr .t1 .t4, st d 1 .t1, an .t4 .a7, ld .t0 s 9,
    xr .t4 .t5, ld .t1 s 10, st d 4 .t4, orr .t5 .a7,
    ld .a7 s 3, xr .t5 .t2, ld .t2 s 16, st d 3 .t5,
    -- plane 1
    xr .a7 .a6, xr .t3 .a5, rol .a7 28, xr .t2 .a4,
    xr .t0 .a2, rol .t3 61, rol .t2 45, xr .t1 .a3,
    rol .t0 20, mv .t4 .a7, orr .a7 .t3, rol .t1 3,
    xr .a7 .t2, st d 8 .a7, mv .t5 .t0, an .t0 .t4,
    ld .a7 s 1, xr .t0 .t3, nt .t3, st d 9 .t0,
    orr .t3 .t2, ld .t0 s 7, xr .t3 .t1, st d 7 .t3,
    an .t2 .t1, ld .t3 s 20, xr .t2 .t5, st d 6 .t2,
    orr .t5 .t1, ld .t1 s 13, xr .t5 .t4, ld .t2 s 19,
    st d 5 .t5,
    -- plane 2
    xr .t1 .a6, xr .t2 .a2, rol .t1 25,
    xr .t0 .a5, rol .t2 8, xr .t3 .a3, rol .t0 6,
    xr .a7 .a4, rol .t3 18, mv .t4 .t1, an .t1 .t2,
    rol .a7 1, nt .t2, xr .t1 .t0, st d 11 .t1,
    mv .t5 .t3, an .t3 .t2, ld .t1 s 11, xr .t3 .t4,
    st d 12 .t3, orr .t4 .t0, ld .t3 s 23, xr .t4 .a7,
    st d 10 .t4, an .t0 .a7, xr .t0 .t5, st d 14 .t0,
    orr .t5 .a7, ld .t0 s 5, xr .t5 .t2, ld .t2 s 17,
    st d 13 .t5,
    -- plane 3
    ld .a7 s 4, xr .t1 .a4, xr .t2 .a5,
    rol .t1 10, xr .t0 .a3, rol .t2 15, xr .t3 .a6,
    rol .t0 36, xr .a7 .a2, rol .t3 56, mv .t4 .t1,
    orr .t1 .t2, rol .a7 27, nt .t2, xr .t1 .t0,
    st d 16 .t1, mv .t5 .t3, orr .t3 .t2, xr .t3 .t4,
    st d 17 .t3, an .t4 .t0, xr .t4 .a7, st d 15 .t4,
    orr .t0 .a7, xr .t0 .t5, st d 19 .t0, an .a7 .t5,
    xr .a7 .t2, st d 18 .a7,
    -- plane 4, its B[x] computed in place in the registers of D, which are no longer needed
    xl .a5 s 2, xl .a6 s 8,
    rol .a5 62, xl .a4 s 21, rol .a6 55, xl .a2 s 14,
    rol .a4 2, xl .a3 s 15, rol .a2 39, rol .a3 41,
    mv .t4 .a5, an .a5 .a6, nt .a6, xr .a5 .a4,
    st d 24 .a5, mv .t5 .a2, an .a2 .a6, xr .a2 .t4,
    st d 20 .a2, orr .t4 .a4, xr .t4 .a3, st d 23 .t4,
    an .a4 .a3, xr .a4 .t5, st d 22 .a4, orr .a3 .t5,
    xr .a3 .a6, st d 21 .a3,
    -- row 4 of the output back in a2–a6
    mv .a6 .a5, mv .a5 .t4]

/-- ι in the `k`-th round of an iteration: the round constant, XORed into
lane 0 of the output. -/
def iota (k : Nat) : List Instr := [.load .d T .s0 (8 * k), .logic .xor .t0 .t0 T]

/-- A round from the state at `s` to the state at `d`. -/
def round (s d : Reg) (k : Nat) : List Instr := roundA s ++ iota k ++ roundB s d

/-- Two rounds, from the copy of the state to the second state and back,
then the next pair of round constants. -/
def body : List Instr :=
  round .a0 .a1 0 ++ round .a1 .a0 1 ++ ([.addi .s0 .s0 16] : List Instr)

/-! ## The prologue and the epilogue -/

/-- The bytes of the frame. -/
def frameBytes : Nat := 608

/-- Where in the frame the copy of the state is. -/
def stOff : Nat := 192

/-- Where in the frame the second state is. -/
def scrOff : Nat := 392

/-- The register a lane is copied in through: lanes 20–24 (row 4) through
the registers the rounds expect them in, `a2`–`a6`. -/
def laneReg (i : Nat) : Reg :=
  if i < 20 then .t0 else [Reg.a2, .a3, .a4, .a5, .a6].getD (i - 20) .a2

/-- A NOT if lane `i` is kept complemented. -/
def cmplLane (r : Reg) (i : Nat) : List Instr := if complLanes.contains i then nt r else []

/-- Save `s0` and `s1`, with the frame in `t6`, and keep `state` in `s1`. -/
def save : List Instr :=
  [.addSp .t6 0, .store .d .s0 .t6 592, .store .d .s1 .t6 600, .addi .s1 .a0 0]

/-- The round constants. -/
def rcStores : List Instr :=
  (List.range 24).flatMap fun k =>
    movImm64 .t0 .t1 (Spec.Sha3.RC k) ++ ([.store .d .t0 .t6 (8 * k)] : List Instr)

/-- Lane `i` of the state into the copy, complemented if in `complLanes`. -/
def copyIn (i : Nat) : List Instr :=
  loadLE64 (laneReg i) .t1 .t2 .s1 (8 * i) ++ cmplLane (laneReg i) i ++
    ([.store .d (laneReg i) .t6 (stOff + 8 * i)] : List Instr)

/-- The pointers of the rounds: the copy, the second state, and the round
constants. -/
def pointers : List Instr := [.addSp .a0 stOff, .addSp .a1 scrOff, .addi .s0 .t6 0]

/-- Lane `i` of an 8-byte aligned state into the copy, complemented if in
`complLanes`: a doubleword load. -/
def copyInA (i : Nat) : List Instr :=
  ld (laneReg i) .s1 i ++ cmplLane (laneReg i) i ++
    ([.store .d (laneReg i) .t6 (stOff + 8 * i)] : List Instr)

/-- The registers saved, the round constants stored, and in `t0` the low bits
of `state`: zero exactly when it is 8-byte aligned. -/
def setup : List Instr := save ++ rcStores ++ ([.logicImm .and .t0 .s1 7] : List Instr)

/-- The copy of the state into the frame, a doubleword at a time if `state` is
8-byte aligned and a byte at a time otherwise, then the rounds' pointers. -/
def copyIns : Prog isa :=
  .ite (.zero .t0) (.block ((List.range 25).flatMap copyInA ++ pointers))
    (.block ((List.range 25).flatMap copyIn ++ pointers))

/-- Lane `i` of the copy back into the state, complemented back. -/
def copyOut (i : Nat) : List Instr :=
  ld .t0 .a0 i ++ cmplLane .t0 i ++ storeLE64 .t0 .t1 .t2 .s1 (8 * i)

/-- Restore `s0` and `s1`, from the frame at `a0 - stOff`. -/
def restore : List Instr := [.load .d .s0 .a0 (592 - stOff), .load .d .s1 .a0 (600 - stOff)]

/-- Lane `i` of the copy back into an 8-byte aligned state, complemented
back: a doubleword store. -/
def copyOutA (i : Nat) : List Instr := ld .t0 .a0 i ++ cmplLane .t0 i ++ st .s1 i .t0

/-- The copy back, as `copyIns` chooses, and the registers restored. -/
def epilogue : Prog isa :=
  .seq (.block [.logicImm .and .t0 .s1 7])
    (.ite (.zero .t0) (.block ((List.range 25).flatMap copyOutA ++ restore))
      (.block ((List.range 25).flatMap copyOut ++ restore)))

def main : Prog isa :=
  .seq (.block setup) (.seq copyIns (.seq (.loop (.block body) (.ne .s0 .a0)) epilogue))

def permute : Prog isa := .frame (.alloc frameBytes) main (.free frameBytes)

end VG.Impl.Sha3.RISCV64
