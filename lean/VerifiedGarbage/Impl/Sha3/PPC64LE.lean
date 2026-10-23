module

public import VerifiedGarbage.Spec.Sha3
public import VerifiedGarbage.Impl.Sha3.Tables
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# Keccak-f[1600]: PPC64LE implementation

`vg_keccak_f1600(state = r3, scratch = r4)`.

The x86-64 implementation's rounds (`VG.Impl.Sha3.X86_64`, after Andy
Polyakov's CRYPTOGAMS `keccak1600-x86_64`: the "lane complementing"
implementation, with the column parities and `D` in registers), with each
x86-64 instruction written as PPC64LE ones: an XOR with a lane of memory
is a load into `r0` and an XOR with it, a NOT is an XOR with all ones (kept
in `r18`), a rotation left by `n` is `rotrdi` by `64 - n`, and a `mov` of
registers is `mr`. The registers are x86-64's renamed: `rax, rbx, rcx, rdx,
rbp` (row 4) are `r5`–`r9`, `r8`–`r14` are `r10`–`r12` and `r14`–`r17`, and
`rdi, rsi` (the two states) are `r3, r4`.

**Lane complementing.** While the rounds run, the lanes `1, 2, 8, 12, 17, 20`
(`complLanes`) of the state are kept complemented: that turns most of χ's
`¬a ∧ b` into an `∧` or an `∨` of the lanes as they are, so that χ needs one
NOT per plane instead of five. The prologue complements those lanes and the
epilogue complements them back.

`scratch` (512 bytes) is laid out as:

* `[0, 200)`: a second state, which the rounds alternate with `state`: the
  first round of each iteration reads `state` (`r3`) and writes the second
  state (`r4`), the second the other way round, so after the 24 rounds the
  result is back in `state`;
* `[200, 392)`: the 24 round constants, stored by the prologue;
* `[392, 448)`: the saved `r14`–`r20`.

The round constant of round `2i + k` is at `8k(r19)`, where `r19` is
`scratch + 200 + 16i`; `r20` counts the iterations left, which ends the
loop. Every address is a pointer plus a constant, and the only branch is the
round loop's, so only the pointers can affect timing.
-/

@[expose] public section

namespace VG.Impl.Sha3.PPC64LE

open VG.PPC64LE
open VG.Impl.Sha3 (complLanes)

/-- The temporary that lanes are loaded into. -/
def T : Reg := .r0
/-- All ones, for NOT. -/
def ONES : Reg := .r18

/-! ## Instructions of a round, as on x86-64 -/

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
/-- A rotation left by `0 < n < 64`. -/
def rol (r : Reg) (n : Nat) : List Instr := [.rotr .d r r (64 - n)]
/-- `r = ¬r`. -/
def nt (r : Reg) : List Instr := [.logic .xor r r ONES]

/-- A round from the state at `s`, up to ι: θ, the `B[x]` of plane 0 and
the first lane of its χ. -/
def roundA (s : Reg) : List Instr := List.flatten [
    -- C[x] = A[x, 4] ⊕ … ⊕ A[x, 0], loading A[0, 0], A[1, 1], A[2, 2], A[3, 3] (sources of
    -- plane 0) into r10–r12, r14 and A[4, 4] into r15 on the way
    ld .r10 s 0, ld .r11 s 6, ld .r12 s 12, ld .r14 s 18,
    xl .r7 s 2, xl .r8 s 3, xr .r5 .r10, xl .r6 s 1,
    xl .r7 s 7, xl .r5 s 5, mv .r15 .r9, xl .r9 s 4,
    xr .r7 .r12, xl .r5 s 10, xl .r8 s 8, xr .r6 .r11,
    xl .r9 s 9, xl .r7 s 17, xl .r5 s 15, xl .r8 s 13,
    xl .r6 s 11, xl .r9 s 14,
    -- D[x] = ROTL¹(C[x + 1]) ⊕ C[x - 1], in place: D[1] in r7, D[4] in r5, D[2] in r8,
    -- D[0] in r6, D[3] in r9
    mv .r16 .r7, rol .r7 1,
    xr .r7 .r5, xr .r8 .r14, rol .r5 1, xr .r5 .r8,
    xl .r6 s 16, rol .r8 1, xr .r8 .r6, xl .r9 s 19,
    rol .r6 1, xr .r6 .r9, rol .r9 1, xr .r9 .r16,
    -- plane 0: B[x] = ROTL^ρ(A[x, x] ⊕ D[x]) in r10–r12, r14, r15, and lane 0 of χ in r11
    xr .r11 .r7, xr .r12 .r8, rol .r11 44, xr .r14 .r9,
    xr .r15 .r5, rol .r12 43, xr .r10 .r6, mv .r16 .r11,
    rol .r14 21, orr .r11 .r12, xr .r11 .r10, rol .r15 14]

/-- The rest of the round from the state at `s` to the state at `d`, after ι. -/
def roundB (s d : Reg) : List Instr := List.flatten [
    -- the rest of plane 0's χ, loading plane 1's sources
    mv .r17 .r15, an .r15 .r14, st d 0 .r11, xr .r15 .r12,
    nt .r12, st d 2 .r15, orr .r12 .r14, ld .r15 s 22,
    xr .r12 .r16, st d 1 .r12, an .r16 .r10, ld .r11 s 9,
    xr .r16 .r17, ld .r12 s 10, st d 4 .r16, orr .r17 .r10,
    ld .r10 s 3, xr .r17 .r14, ld .r14 s 16, st d 3 .r17,
    -- plane 1
    xr .r10 .r9, xr .r15 .r8, rol .r10 28, xr .r14 .r7,
    xr .r11 .r5, rol .r15 61, rol .r14 45, xr .r12 .r6,
    rol .r11 20, mv .r16 .r10, orr .r10 .r15, rol .r12 3,
    xr .r10 .r14, st d 8 .r10, mv .r17 .r11, an .r11 .r16,
    ld .r10 s 1, xr .r11 .r15, nt .r15, st d 9 .r11,
    orr .r15 .r14, ld .r11 s 7, xr .r15 .r12, st d 7 .r15,
    an .r14 .r12, ld .r15 s 20, xr .r14 .r17, st d 6 .r14,
    orr .r17 .r12, ld .r12 s 13, xr .r17 .r16, ld .r14 s 19,
    st d 5 .r17,
    -- plane 2
    xr .r12 .r9, xr .r14 .r5, rol .r12 25,
    xr .r11 .r8, rol .r14 8, xr .r15 .r6, rol .r11 6,
    xr .r10 .r7, rol .r15 18, mv .r16 .r12, an .r12 .r14,
    rol .r10 1, nt .r14, xr .r12 .r11, st d 11 .r12,
    mv .r17 .r15, an .r15 .r14, ld .r12 s 11, xr .r15 .r16,
    st d 12 .r15, orr .r16 .r11, ld .r15 s 23, xr .r16 .r10,
    st d 10 .r16, an .r11 .r10, xr .r11 .r17, st d 14 .r11,
    orr .r17 .r10, ld .r11 s 5, xr .r17 .r14, ld .r14 s 17,
    st d 13 .r17,
    -- plane 3
    ld .r10 s 4, xr .r12 .r7, xr .r14 .r8,
    rol .r12 10, xr .r11 .r6, rol .r14 15, xr .r15 .r9,
    rol .r11 36, xr .r10 .r5, rol .r15 56, mv .r16 .r12,
    orr .r12 .r14, rol .r10 27, nt .r14, xr .r12 .r11,
    st d 16 .r12, mv .r17 .r15, orr .r15 .r14, xr .r15 .r16,
    st d 17 .r15, an .r16 .r11, xr .r16 .r10, st d 15 .r16,
    orr .r11 .r10, xr .r11 .r17, st d 19 .r11, an .r10 .r17,
    xr .r10 .r14, st d 18 .r10,
    -- plane 4, its B[x] computed in place in the registers of D, which are no longer needed
    xl .r8 s 2, xl .r9 s 8,
    rol .r8 62, xl .r7 s 21, rol .r9 55, xl .r5 s 14,
    rol .r7 2, xl .r6 s 15, rol .r5 39, rol .r6 41,
    mv .r16 .r8, an .r8 .r9, nt .r9, xr .r8 .r7,
    st d 24 .r8, mv .r17 .r5, an .r5 .r9, xr .r5 .r16,
    st d 20 .r5, orr .r16 .r7, xr .r16 .r6, st d 23 .r16,
    an .r7 .r6, xr .r7 .r17, st d 22 .r7, orr .r6 .r17,
    xr .r6 .r9, st d 21 .r6,
    -- row 4 of the output back in r5–r9
    mv .r9 .r8, mv .r8 .r16]

/-- ι in the `k`-th round of an iteration: the round constant, XORed into
lane 0 of the output. -/
def iota (k : Nat) : List Instr := [.load .d T .r19 (8 * k), .logic .xor .r11 .r11 T]

/-- A round from the state at `s` to the state at `d`. -/
def round (s d : Reg) (k : Nat) : List Instr := roundA s ++ iota k ++ roundB s d

/-- Two rounds, from `state` to the second state and back, then the next pair
of round constants and one iteration fewer. -/
def body : List Instr :=
  round .r3 .r4 0 ++ round .r4 .r3 1 ++ ([.addi .r19 .r19 16, .subi .r20 .r20 1] : List Instr)

/-- The nonvolatile registers we use, and where they are saved. -/
def saved : List (Reg × Nat) :=
  [(.r14, 392), (.r15, 400), (.r16, 408), (.r17, 416), (.r18, 424), (.r19, 432), (.r20, 440)]

/-- `d := v` for a 64-bit constant: the high word with `lis` and `ori`,
shifted up by `sldi`, then the low word with `oris` and `ori`. -/
def movImm64 (d : Reg) (v : BitVec 64) : List Instr :=
  [.lis d (v.extractLsb' 48 16), .ori d d (v.extractLsb' 32 16), .lsl d d 32,
   .oris d d (v.extractLsb' 16 16), .ori d d (v.extractLsb' 0 16)]

/-- Complement the lanes `complLanes` of the state at `r3`. -/
def complement : List Instr :=
  complLanes.flatMap fun i => ld .r5 .r3 i ++ nt .r5 ++ st .r3 i .r5

/-- Load row 4 of the state at `r3`, after `complement`, which leaves
lane 20 (the last it complements) in `r5`. -/
def loadRow : List Instr := ld .r6 .r3 21 ++ ld .r7 .r3 22 ++ ld .r8 .r3 23 ++ ld .r9 .r3 24

/-- Save the registers, store the round constants, and set `ONES`, `r19`
and `r20`. -/
def setup : List Instr :=
  saved.map (fun (r, d) => .store .d r .r4 d) ++
  (List.range 24).flatMap (fun k => movImm64 .r5 (Spec.Sha3.RC k) ++ ([.store .d .r5 .r4 (200 + 8 * k)] : List Instr)) ++
  ([.lis ONES 0xffff, .ori ONES ONES 0xffff, .addi .r19 .r4 200, .li .r20 12] : List Instr)

/-- Restore the registers (`r14`–`r20`). -/
def restore : List Instr := saved.map fun (r, d) => .load .d r .r4 d

def permute : Prog isa :=
  .seq (.block (setup ++ complement ++ loadRow))
    (.seq (.loop (.block body) (.nonzero .d .r20)) (.block (complement ++ restore)))

end VG.Impl.Sha3.PPC64LE
