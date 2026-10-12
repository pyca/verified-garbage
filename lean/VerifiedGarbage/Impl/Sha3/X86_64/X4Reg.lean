module

public import VerifiedGarbage.Impl.Sha3.Tables
public import VerifiedGarbage.TCB.X86_64.Isa
public import VerifiedGarbage.Impl.Sha3.X86_64

/-!
# Keccak-f[1600] on four states at once, in registers: x86-64 with AVX-512VL

The four interleaved states of `X4.lean` (lane `j` of state `k` the `u64`
at byte `32 j + 8 k` of the 800 bytes at `rdi`), held in the thirty-two
`ymm` registers of AVX-512 (`VReg`) for the 24 rounds: lane `i` in `ymm i`
(`lreg`), the five column parities `C[x]` of θ in `ymm25`–`ymm29` (`creg`)
and a temporary in `ymm30` (`T`), with the EVEX-encoded instructions of
`TCB/X86_64/Evex.lean`, each on 256 bits (four 64-bit elements, one per
state). `permute4R` loads the 25 lanes, runs the rounds, one per iteration
of its loop, and stores them back; it reads the table of round constants
at `rdx` (each in the four elements of a `u256`, as `X4.rcTable` stores it)
up to `rcx`, and so has the interface of `X4.permute4` (it does not use the
second buffer at `rsi`).

A round:

* θ: `C[x]` (`vpxorq`, then `vpternlogq` with `0x96`, the XOR of its three
  operands, and `vpxorq`), then, for each `x`, `ROTL¹(C[x + 1])` into `T`
  (`vprorq` by 63) and each lane `(x, y)` XORed with it and `C[x - 1]`
  (`vpternlogq`, `0x96`);
* ρ and π at once: π is a cycle of the 24 lanes but `(0, 0)` (`piChain`),
  and each of them takes the value of the next, rotated: `T` keeps the
  first, and each `vprorq` writes the rotation of a lane to the register of
  the lane π moves it to, after that one's own value has been moved on;
* χ: in each plane, the first two lanes copied to `ymm25` and `ymm26`
  (`vporq` of a register with itself), and each lane `B[x]` becomes
  `B[x] ⊕ (¬B[x+1] ∧ B[x+2])` in place (`vpternlogq` with `0xD2`), reading
  the copies for the lanes already written;
* ι: the round constant at `rdx`, loaded into `T`, XORed into lane 0.

It writes only `rdx`, the flags and the vector registers. Every address is
a pointer plus a constant, and the only branch is the round loop's, so only
the pointers can affect timing.
-/

@[expose] public section

namespace VG.Impl.Sha3.X86_64.X4R

open VG.X86_64
open VG.Impl.Sha3 (rhoOff piSrc)
open VG.Impl.Sha3.X86_64 (at_)

/-- `ymm i`, for `i < 32`. -/
def vreg (i : Nat) : VReg :=
  match i with
  | 0 => .lo .xmm0 | 1 => .lo .xmm1 | 2 => .lo .xmm2 | 3 => .lo .xmm3 | 4 => .lo .xmm4 | 5 => .lo .xmm5
  | 6 => .lo .xmm6 | 7 => .lo .xmm7 | 8 => .lo .xmm8 | 9 => .lo .xmm9 | 10 => .lo .xmm10
  | 11 => .lo .xmm11 | 12 => .lo .xmm12 | 13 => .lo .xmm13 | 14 => .lo .xmm14 | 15 => .lo .xmm15
  | 16 => .hi .xmm16 | 17 => .hi .xmm17 | 18 => .hi .xmm18 | 19 => .hi .xmm19 | 20 => .hi .xmm20
  | 21 => .hi .xmm21 | 22 => .hi .xmm22 | 23 => .hi .xmm23 | 24 => .hi .xmm24 | 25 => .hi .xmm25
  | 26 => .hi .xmm26 | 27 => .hi .xmm27 | 28 => .hi .xmm28 | 29 => .hi .xmm29 | 30 => .hi .xmm30
  | _ => .hi .xmm31

/-- The register of lane `i`. -/
def lreg (i : Nat) : VReg := vreg i

/-- The register of `C[x]`, and, in χ, of the copies. -/
def creg (x : Nat) : VReg := vreg (25 + x)

/-- The temporary. -/
def T : VReg := vreg 30

/-- `op d, a, b`. -/
def eb (op : EBinOp) (d a b : VReg) : Instr := .eop (.bin op d a b)

/-- `vpternlogq d, a, b, imm`. -/
def tern (d a b : VReg) (imm : BitVec 8) : Instr := .eop (.vpternlogq d a b imm)

/-- `vprorq d, a, n`. -/
def ror (d a : VReg) (n : Nat) : Instr := .eop (.vprorq d a (BitVec.ofNat 8 n))

/-- `d := a`. -/
def copy (d a : VReg) : Instr := eb .vporq d a a

/-- `C[x] = A[x, 0] ⊕ … ⊕ A[x, 4]`. -/
def column (x : Nat) : List Instr :=
  [eb .vpxorq (creg x) (lreg x) (lreg (x + 5)), tern (creg x) (lreg (x + 10)) (lreg (x + 15)) 0x96,
    eb .vpxorq (creg x) (creg x) (lreg (x + 20))]

/-- Each lane of column `x` XORed with `D[x] = ROTL¹(C[x + 1]) ⊕ C[x - 1]`. -/
def dcol (x : Nat) : List Instr :=
  ror T (creg ((x + 1) % 5)) 63 :: (List.range 5).map fun y => tern (lreg (x + 5 * y)) (creg ((x + 4) % 5)) T 0x96

/-- The 24 lanes but `(0, 0)`, each the lane π moves the next one to: lane
`piChain[j]` of `π(A)` is lane `piChain[j + 1]` of `A`, and lane 1 that of
lane `piChain[23]`. -/
def piChain : List Nat := [1, 6, 9, 22, 14, 20, 2, 12, 13, 19, 23, 15, 4, 24, 21, 8, 16, 5, 3, 18, 17, 11, 7, 10]

/-- `ROTR^(64 - ρ)`, the rotation of ρ of lane `i` (none is 0 but lane 0's). -/
def rhoR (i : Nat) : Nat := 64 - rhoOff i

/-- ρ and π. -/
def rhoPi : List Instr :=
  copy T (lreg 1) ::
    ((List.range 23).map fun j => ror (lreg (piChain.getD j 0)) (lreg (piChain.getD (j + 1) 0))
      (rhoR (piChain.getD (j + 1) 0))) ++
    [ror (lreg 10) T (rhoR 1)]

/-- χ on plane `y`. -/
def chi (y : Nat) : List Instr :=
  [copy (creg 0) (lreg (5 * y)), copy (creg 1) (lreg (5 * y + 1)),
    tern (lreg (5 * y)) (lreg (5 * y + 1)) (lreg (5 * y + 2)) 0xD2,
    tern (lreg (5 * y + 1)) (lreg (5 * y + 2)) (lreg (5 * y + 3)) 0xD2,
    tern (lreg (5 * y + 2)) (lreg (5 * y + 3)) (lreg (5 * y + 4)) 0xD2,
    tern (lreg (5 * y + 3)) (lreg (5 * y + 4)) (creg 0) 0xD2,
    tern (lreg (5 * y + 4)) (creg 0) (creg 1) 0xD2]

/-- ι, and the next round constant (setting ZF after the last). -/
def iota : List Instr :=
  [.evLoad T (at_ .rdx 0), eb .vpxorq (lreg 0) (lreg 0) T, .alu .add .rdx (.imm 32), .alu .cmp .rdx (.reg .rcx)]

/-- One round. -/
def round : List Instr :=
  (List.range 5).flatMap column ++ (List.range 5).flatMap dcol ++ rhoPi ++ (List.range 5).flatMap chi ++ iota

/-- The 25 lanes of the four states at `rdi` into their registers. -/
def load : List Instr := (List.range 25).map fun i => .evLoad (lreg i) (at_ .rdi (32 * i))

/-- The 25 lanes back to the four states at `rdi`. -/
def store : List Instr := (List.range 25).map fun i => .evStore (at_ .rdi (32 * i)) (lreg i)

/-- The 24 rounds on the four states at `rdi`, with the table at `rdx` and
its end in `rcx`. -/
def permute4R : Prog isa := .seq (.block load) (.seq (.loop (.block round) .ne) (.block store))

end VG.Impl.Sha3.X86_64.X4R
