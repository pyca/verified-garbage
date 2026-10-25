module

public import VerifiedGarbage.Spec.Md5
public import VerifiedGarbage.Impl.Words.RISCV64

/-!
# MD5 compression function: RISC-V implementation

`vg_md5_compress(state = a0, blocks = a1, n = a2, scratch = a3)`.

The structure of the PPC64LE implementation (`Impl/Md5/PPC64LE.lean`), for
RV64I, which has neither rotates nor `andc`/`orc`, and faults on misaligned
accesses:
* The MD buffer `a … d` lives in the low words of `t0`–`t3`; the fully
  unrolled operations rename the words: in operation `t`, word `k` is in
  `var t k`. The additions act on all 64 bits, so the high words hold
  carries, which the word shifts and the stores ignore.
* The words of a block (little-endian) and of the MD buffer (`state`, an
  array of `u32`) are in argument buffers, whose alignment the contract
  does not state, so they are read and written a byte at a time
  (`Impl/Words/RISCV64.lean`): each operation loads its word `X[k]` from
  the block. `scratch` is not used.
* `¬d` is `xori d, -1`; a rotation left by `s` is `slliw` by `s` and
  `srliw` by `32 - s`, combined by `or`.
* Only temporaries are used, so nothing is saved.
* `a0`–`a2` (the pointers and the block count) are public; no address and
  no branch depends on anything else.
-/

@[expose] public section

namespace VG.Impl.Md5.RISCV64

open VG.RISCV64
open VG.Impl.Words.RISCV64
open VG.Spec.Md5 (ks ss Ts)

/-- The registers holding the MD buffer. -/
def work : List Reg := [.t0, .t1, .t2, .t3]

/-- The register holding word `k` (`a = 0, …, d = 3`) at the start of operation `t`. -/
def var (t k : Nat) : Reg := work.getD ((k + 4 - t % 4) % 4) .t0

/-- Temporaries: `T0` holds the auxiliary function's terms and the rotated
bits, `T1` the word `X[k]` and then the constant `T[t+1]`, `T2` the bytes
of `X[k]`. -/
def T0 : Reg := .t4
def T1 : Reg := .t5
def T2 : Reg := .t6

/-- `a := a + fn(b, c, d)`, the auxiliary function of round `r`, using `T0`:
`F = ((c ⊕ d) ∧ b) ⊕ d`, `G = (¬d ∧ c) + (d ∧ b)`, `H = (c ⊕ d) ⊕ b` and
`I = (¬d ∨ b) ⊕ c`. -/
def fn (r : Nat) (a b c d : Reg) : List Instr :=
  match r with
  | 0 => [.logic .xor T0 c d, .logic .and T0 T0 b, .logic .xor T0 T0 d, .add a a T0]
  | 1 => [.logicImm .xor T0 d (-1), .logic .and T0 T0 c, .add a a T0, .logic .and T0 d b,
      .add a a T0]
  | 2 => [.logic .xor T0 c d, .logic .xor T0 T0 b, .add a a T0]
  | _ => [.logicImm .xor T0 d (-1), .logic .or T0 T0 b, .logic .xor T0 T0 c, .add a a T0]

/-- The rotation amount `s` of operation `t`. -/
def rot (t : Nat) : Nat := (ss.getD (t / 16) []).getD (t % 4) 0

/-- Operation `t`: `a := b + ((a + X[k] + T[t+1] + fn(b,c,d)) <<< s)`. -/
def step (t : Nat) : List Instr :=
  let a := var t 0; let b := var t 1; let c := var t 2; let d := var t 3
  loadLE32 T1 T2 .a1 (4 * ks.getD t 0) ++ [.add a a T1] ++ li32 T1 (Ts.getD t 0) ++
  ([.add a a T1] : List Instr) ++ fn (t / 16) a b c d ++
  ([.shift .sll .w T0 a (rot t), .shift .srl .w a a (32 - rot t), .logic .or a a T0,
    .add a a b] : List Instr)

/-- Operations `0 … n-1`. -/
def steps : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (steps n) (.block (step n))

/-- Load the MD buffer (`64 % 4 = 0`, so the words are in the same registers
after the 64 operations). -/
def load : List Instr := (List.range 4).flatMap fun k => loadLE32 (var 0 k) T0 .a0 (4 * k)

/-- Add word `k` of the MD buffer into its register, and store the result. -/
def updateW (k : Nat) : List Instr :=
  loadLE32 T0 T1 .a0 (4 * k) ++ [.add (var 0 k) (var 0 k) T0] ++ storeLE32 (var 0 k) T0 .a0 (4 * k)

/-- Advance to the next block and decrement the count. -/
def advance : List Instr := [.addi .a1 .a1 64, .addi .a2 .a2 (-1)]

/-- One block. -/
def body : Prog isa :=
  .seq (.block load) (.seq (steps 64) (.block ((List.range 4).flatMap updateW ++ advance)))

def compress : Prog isa := .ite (.zero .a2) (.block []) (.loop body (.nonzero .a2))

end VG.Impl.Md5.RISCV64
