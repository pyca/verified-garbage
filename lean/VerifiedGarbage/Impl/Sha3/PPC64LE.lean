module

public import VerifiedGarbage.Spec.Sha3
public import VerifiedGarbage.Impl.Sha3.Tables
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# Keccak-f[1600]: PPC64LE implementation

`vg_keccak_f1600(state = r3, scratch = r4)`.

The 25 lanes stay in general registers for the 24 rounds (`lane`), as in
CRYPTOGAMS' `keccak1600-ppc64` (Andy Polyakov): they are loaded once and
stored once. `r3` and `r4` keep the two pointers, and `r0`, `r5` and `r6`
are the temporaries; the other 25 registers, `r2`, `r7`–`r12` and
`r14`–`r31`, hold the lanes.

**A round** (`core`, then `iota`) computes in place:

* θ: the column parities `C[0]`–`C[2]` in the temporaries; `C[3]` and
  `C[4]` in the registers of `A[3]` and `A[4]`, and `D[1]` in that of
  `A[9]`, which are first spilled to the scratch space. Each `D[x]` is
  XORed into its column as soon as it is computed, and the three spilled
  lanes are loaded back, with their `D`, into the temporaries.
* ρ and π: each lane, rotated, is written to the register of the lane that
  π moves it to, once that register's lane has been read: three chains of
  `rotrdi`, from the registers of `A[3]`, `A[4]` and `A[9]`, which θ left
  free, and ending at the temporaries, which they leave free.
* χ, plane by plane, with the "lane complementing" transform (the Keccak
  team's implementation overview, §2.2): while the rounds run, the lanes
  `1, 2, 8, 12, 17, 20` (`complLanes`) of the state are kept complemented,
  which turns most of χ's `¬a ∧ b` into an `∧` or an `∨` of the lanes as
  they are, with one NOT (an XOR with all ones, loaded from the scratch
  space) per plane. A plane's five `b ∧ c` (or `b ∨ c`) are computed into
  the temporaries, and each XORed into its lane once the lane has been
  read for the others.
* ι: the round constant, built in `r5` from immediates (`movImm64`),
  XORed into lane 0.

The rounds are unrolled: the round constants are immediates, and the code
needs no loop counter, which would need a register.

`scratch` (512 bytes) is laid out as:

* `[0, 24)`: the three lanes θ spills;
* `[24, 32)`: all ones, for χ's NOTs;
* `[32, 184)`: the saved `r2` and `r14`–`r31`.

Every address is a pointer plus a constant, and there is no branch, so only
the pointers can affect timing.
-/

@[expose] public section

namespace VG.Impl.Sha3.PPC64LE

open VG.PPC64LE
open VG.Impl.Sha3 (complLanes)

/-- The register of lane `i`. -/
def lane (i : Nat) : Reg :=
  [Reg.r2, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22,
    .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31].getD i .r2

/-- The temporaries. -/
def T0 : Reg := .r0
def T1 : Reg := .r5
def T2 : Reg := .r6

/-- Where in the scratch space the spilled lanes are, and all ones. -/
def spillOff (k : Nat) : Nat := 8 * k
def onesOff : Nat := 24

/-! ## Instructions -/

def xr (d a b : Reg) : Instr := .logic .xor d a b
def an (d a b : Reg) : Instr := .logic .and d a b
def orr (d a b : Reg) : Instr := .logic .or d a b
/-- `d` set to `n` rotated left by `0 < k < 64`. -/
def rol (d n : Reg) (k : Nat) : Instr := .rotr .d d n (64 - k)
/-- `d` loaded from, or `r` stored to, scratch offset `off`. -/
def lds (d : Reg) (off : Nat) : Instr := .load .d d .r4 off
def sts (r : Reg) (off : Nat) : Instr := .store .d r .r4 off

/-! ## θ -/

/-- `d = C[x]`, the parity of column `x`. -/
def column (d : Reg) (x : Nat) : List Instr :=
  [xr d (lane x) (lane (x + 5)), xr d d (lane (x + 10)), xr d d (lane (x + 15)), xr d d (lane (x + 20))]

/-- `C[x]` in the register of `A[x]`, once `A[x]` is spilled. -/
def columnIn (x : Nat) : List Instr :=
  [xr (lane x) (lane x) (lane (x + 5)), xr (lane x) (lane x) (lane (x + 10)),
    xr (lane x) (lane x) (lane (x + 15)), xr (lane x) (lane x) (lane (x + 20))]

/-- `D[x]` (in `d`) XORed into the lanes `ks`. -/
def addD (d : Reg) (ks : List Nat) : List Instr := ks.map fun k => xr (lane k) (lane k) d

/-- θ. `C[0]`–`C[2]` in `T0`–`T2`; `C[3]`, `C[4]` in the registers of the
spilled `A[3]`, `A[4]`. Then `D[x] = ROTL¹(C[x + 1]) ⊕ C[x - 1]`: `D[1]` in
the register of the spilled `A[9]`, and the others in place of the `C`
that no later `D` needs. The spilled lanes come back, with their `D`, in
`T1` (`A[4]`), `T2` (`A[3]`) and `T0` (`A[9]`). -/
def theta : List Instr :=
  column T0 0 ++ column T1 1 ++ column T2 2 ++
  [sts (lane 3) (spillOff 0)] ++ columnIn 3 ++ [sts (lane 4) (spillOff 1)] ++ columnIn 4 ++
  [sts (lane 9) (spillOff 2),
    -- D[1] = ROTL¹(C[2]) ⊕ C[0]
    rol (lane 9) T2 1, xr (lane 9) (lane 9) T0] ++ addD (lane 9) [1, 6, 11, 16, 21] ++
  -- D[4] = ROTL¹(C[0]) ⊕ C[3]
  [rol T0 T0 1, xr T0 T0 (lane 3)] ++ addD T0 [14, 19, 24] ++
  -- D[2] = ROTL¹(C[3]) ⊕ C[1]
  [rol (lane 3) (lane 3) 1, xr (lane 3) (lane 3) T1] ++ addD (lane 3) [2, 7, 12, 17, 22] ++
  -- D[0] = ROTL¹(C[1]) ⊕ C[4]
  [rol T1 T1 1, xr T1 T1 (lane 4)] ++ addD T1 [0, 5, 10, 15, 20] ++
  -- D[3] = ROTL¹(C[4]) ⊕ C[2]
  [rol (lane 4) (lane 4) 1, xr (lane 4) (lane 4) T2] ++ addD (lane 4) [8, 13, 18, 23] ++
  -- the spilled lanes, with their D
  [lds T1 (spillOff 1), xr T1 T1 T0, lds T2 (spillOff 0), xr T2 T2 (lane 4),
    lds (lane 9) (spillOff 2), xr T0 T0 (lane 9)]

/-! ## ρ and π -/

/-- The lane `B[i] = ROTL^ρ(A[s])` that π moves to `i`, from the register `r`
holding `A[s]`. -/
def rp (i s : Nat) (r : Reg) : Instr := rol (lane i) r (VG.Impl.Sha3.rhoOff s)

/-- ρ and π: three chains, each writing a register after reading its lane,
from the registers θ left free (of `A[3]`, `A[4]`, `A[9]`) to the
temporaries holding those lanes. -/
def rhoPi : List Instr :=
  [rp 3 18 (lane 18), rp 18 17 (lane 17), rp 17 11 (lane 11), rp 11 7 (lane 7), rp 7 10 (lane 10),
    rp 10 1 (lane 1), rp 1 6 (lane 6), rp 6 9 T0,
    rp 4 24 (lane 24), rp 24 21 (lane 21), rp 21 8 (lane 8), rp 8 16 (lane 16), rp 16 5 (lane 5),
    rp 5 3 T2,
    rp 9 22 (lane 22), rp 22 14 (lane 14), rp 14 20 (lane 20), rp 20 2 (lane 2), rp 2 12 (lane 12),
    rp 12 13 (lane 13), rp 13 19 (lane 19), rp 19 23 (lane 23), rp 23 15 (lane 15), rp 15 4 T1]

/-! ## χ -/

/-- χ on plane `y`, whose lanes are `b x = A[x + 5y]`: lane `x` of the output
is `b x ⊕ (¬b (x+1) ∧ b (x+2))`, which, on the lanes as stored, is
`b x ⊕ (b (x+1) ∧ b (x+2))`, `b x ⊕ (b (x+1) ∨ b (x+2))`, or one of those with
one operand complemented (`ld` of all ones, and an XOR with it). -/
def chi0 : List Instr :=
  let b := fun x => lane x
  [an T0 (b 0) (b 1), orr T1 (b 4) (b 0), orr T2 (b 1) (b 2), xr (b 0) (b 0) T2,
    lds T2 onesOff, xr T2 T2 (b 2), orr T2 T2 (b 3), xr (b 1) (b 1) T2,
    an T2 (b 3) (b 4), xr (b 2) (b 2) T2, xr (b 3) (b 3) T1, xr (b 4) (b 4) T0]

def chi1 : List Instr :=
  let b := fun x => lane (5 + x)
  [an T0 (b 0) (b 1), orr T1 (b 4) (b 0), orr T2 (b 1) (b 2), xr (b 0) (b 0) T2,
    an T2 (b 2) (b 3), xr (b 1) (b 1) T2,
    lds T2 onesOff, xr T2 T2 (b 4), orr T2 T2 (b 3), xr (b 2) (b 2) T2,
    xr (b 3) (b 3) T1, xr (b 4) (b 4) T0]

/-- Planes 2–4 complement one lane `b k` in place, which then serves as
`¬b k` both as an operand and as lane `k` of the output's first term. -/
def chi2 : List Instr :=
  let b := fun x => lane (10 + x)
  [orr T0 (b 1) (b 2), an T1 (b 2) (b 3), an T2 (b 0) (b 1), xr (b 1) (b 1) T1,
    orr T1 (b 4) (b 0), xr (b 0) (b 0) T0,
    lds T0 onesOff, xr (b 3) (b 3) T0, an T0 (b 3) (b 4), xr (b 2) (b 2) T0,
    xr (b 3) (b 3) T1, xr (b 4) (b 4) T2]

def chi3 : List Instr :=
  let b := fun x => lane (15 + x)
  [an T0 (b 1) (b 2), orr T1 (b 2) (b 3), orr T2 (b 0) (b 1), xr (b 1) (b 1) T1,
    an T1 (b 4) (b 0), xr (b 0) (b 0) T0,
    lds T0 onesOff, xr (b 3) (b 3) T0, orr T0 (b 3) (b 4), xr (b 2) (b 2) T0,
    xr (b 3) (b 3) T1, xr (b 4) (b 4) T2]

def chi4 : List Instr :=
  let b := fun x => lane (20 + x)
  [orr T0 (b 2) (b 3), an T1 (b 3) (b 4), orr T2 (b 4) (b 0), xr (b 3) (b 3) T2,
    an T2 (b 0) (b 1), xr (b 4) (b 4) T2,
    lds T2 onesOff, xr (b 1) (b 1) T2, an T2 (b 1) (b 2), xr (b 0) (b 0) T2,
    xr (b 1) (b 1) T0, xr (b 2) (b 2) T1]

/-- A round up to ι. -/
def core : List Instr := theta ++ rhoPi ++ chi0 ++ chi1 ++ chi2 ++ chi3 ++ chi4

/-! ## ι, the rounds, and the prologue and epilogue -/

/-- `d := v` for a 64-bit constant: the high word with `lis` and `ori`,
shifted up by `sldi`, then the low word with `oris` and `ori`. -/
def movImm64 (d : Reg) (v : BitVec 64) : List Instr :=
  [.lis d (v.extractLsb' 48 16), .ori d d (v.extractLsb' 32 16), .lsl d d 32,
   .oris d d (v.extractLsb' 16 16), .ori d d (v.extractLsb' 0 16)]

/-- ι in round `r`: its round constant, built in `T1`, XORed into lane 0. -/
def iota (r : Nat) : List Instr := movImm64 T1 (Spec.Sha3.RC r) ++ [xr (lane 0) (lane 0) T1]

/-- Round `r`. -/
def round (r : Nat) : List Instr := core ++ iota r

/-- The 24 rounds. -/
def rounds : List Instr := (List.range 24).flatMap round

/-- The nonvolatile registers, and where they are saved. -/
def saved : List (Reg × Nat) :=
  [(.r2, 32), (.r14, 40), (.r15, 48), (.r16, 56), (.r17, 64), (.r18, 72), (.r19, 80), (.r20, 88),
    (.r21, 96), (.r22, 104), (.r23, 112), (.r24, 120), (.r25, 128), (.r26, 136), (.r27, 144),
    (.r28, 152), (.r29, 160), (.r30, 168), (.r31, 176)]

/-- Save the registers, and store all ones (left in `T0`). -/
def setup : List Instr :=
  saved.map (fun (r, d) => .store .d r .r4 d) ++ [.lis T0 0xffff, .ori T0 T0 0xffff, sts T0 onesOff]

/-- A NOT of `r` (with all ones in `T0`) if lane `i` is kept complemented. -/
def cmplLane (r : Reg) (i : Nat) : List Instr := if complLanes.contains i then [xr r r T0] else []

/-- Load the lanes, complementing `complLanes` (all ones in `T0`). -/
def loadLanes : List Instr :=
  (List.range 25).flatMap fun i => .load .d (lane i) .r3 (8 * i) :: cmplLane (lane i) i

/-- Store the lanes, complementing `complLanes` back. -/
def storeLanes : List Instr :=
  lds T0 onesOff :: (List.range 25).flatMap fun i => cmplLane (lane i) i ++ [.store .d (lane i) .r3 (8 * i)]

/-- Restore the registers. -/
def restore : List Instr := saved.map fun (r, d) => .load .d r .r4 d

def permute : Prog isa := .block (setup ++ loadLanes ++ rounds ++ storeLanes ++ restore)

end VG.Impl.Sha3.PPC64LE
