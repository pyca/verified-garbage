module

public import VerifiedGarbage.Impl.Bignum.RISCV64.MontMul

/-! # The native FFDH key-generation controller's blocks on RISC-V

As on PPC64LE (`Impl/Ffdh/PPC64LE/KeyGeneration/Search.lean`), the blocks of
the controller that repeats an attempt on successive `p_len` octets of the
random tape until it gives a key, a budget runs out, or the tape does
(`Impl/Ffdh/RISCV64/CachedSearch.lean`). The first four state words are the
budgets, the width and the next request; the rest are private working space,
whose base is kept in the callee-saved `s0` (the caller's `s0` saved in word
4). The tape is short when its length left is below `p_len`, unsigned
(`bltu`).

The controller's arguments: `x = a0, x_len = a1, y = a2, y_len = a3,
used = a4, domain = a5, domain_len = a6, p_len = a7, rand = [sp],
rand_len = [sp + 8], scratch = [sp + 16], scratch_len = [sp + 24],
state = [sp + 32]`.
-/

@[expose] public section

namespace VG.Impl.Ffdh.RISCV64.KeyGeneration.Search

open VG VG.RISCV64 VG.Impl.Bignum.RISCV64

/-- State word `j`: the key and scalar budgets, `p_len`, the request; the
saved `s0`; `x`, `y`, `domain` and `domain_len`; the tape's current pointer
and length and the octets consumed; `scratch` and `scratch_len`; the status;
`used`. -/
def ldf (t : Reg) (j : Nat) : Instr := .load .d t .s0 (8 * j)
def stf (t : Reg) (j : Nat) : Instr := .store .d t .s0 (8 * j)

/-- The state's address and the stack arguments loaded, the caller's `s0`
saved, then the arguments stored. -/
def entry : List Instr :=
  [.addSp .t1 0, .load .d .t2 .t1 32, .load .d .t3 .t1 0, .load .d .t4 .t1 8,
    .load .d .t5 .t1 16, .load .d .t6 .t1 24, .store .d .s0 .t2 32, .addi .s0 .t2 0,
    stf .a0 5, stf .a2 6, stf .a5 7, stf .a6 8, stf .a4 15,
    stf .t3 9, stf .t4 10, .li .t1 0, stf .t1 11, stf .t5 12, stf .t6 13]

/-- The attempt's arguments, for `p_len` octets at the tape's current
pointer: its first three stack arguments at the frame's base (`t2`). -/
def arguments : List Instr :=
  [ldf .a0 5, ldf .a1 2, ldf .a2 6, ldf .a3 2, ldf .a4 7, ldf .a5 8, ldf .a6 2, ldf .a7 9,
    ldf .t0 12, ldf .t1 13, .addSp .t2 0, .store .d .a1 .t2 0, .store .d .t0 .t2 8,
    .store .d .t1 .t2 16]

/-- Zero the budgets and the request and finish with `status`. -/
def terminal (status : Nat) : List Instr :=
  [.li .t0 0, .li .t1 status, stf .t0 0, stf .t0 1, stf .t0 3, stf .t1 14]

/-- `p_len` zeros at the pointer in word `j`. -/
def zeroOut (j : Nat) : Prog isa :=
  .seq (.block [ldf .t0 j, ldf .t1 2, .li .t2 0]) (countLoop .t1 [.store .b .t2 .t0 0, .addi .t0 .t0 1])

/-- Zeros at `x` and `y`. -/
def zeroOutputs : Prog isa := .seq (zeroOut 5) (zeroOut 6)

def exhausted : Prog isa := .seq (.block (terminal 3)) zeroOutputs

/-- The status, its low 32 bits, into `t0`; the attempt's `p_len` octets
consumed. -/
def advance : List Instr :=
  [.shift .sll .d .t0 .a0 32, .shift .srl .d .t0 .t0 32, ldf .t1 2, ldf .t2 9, ldf .t3 10, ldf .t4 11,
    .add .t2 .t2 .t1, .sub .t3 .t3 .t1, .add .t4 .t4 .t1, stf .t2 9, stf .t3 10, stf .t4 11]

/-- A scalar out of range: one fewer scalar left. -/
def rejectedScalar : List Instr := [ldf .t1 1, .addi .t1 .t1 (-1), .li .t2 4, stf .t1 1, stf .t2 14]

/-- A degenerate public value: one fewer key left, and the scalar budget
again. -/
def rejectedPublic : List Instr :=
  [ldf .t1 0, .addi .t1 .t1 (-1), .li .t2 128, .li .t3 4, stf .t1 0, stf .t2 1, stf .t3 14]

/-- The status `t0` minus `k`, in `t1`. -/
def test (k : Nat) : List Instr := [.addi .t1 .t0 (-(k : Int))]

def classify : Prog isa := .seq (.block (advance ++ test 1))
  (.ite (.zero .t1) (.block (terminal 1))
    (.seq (.block (test 2))
      (.ite (.zero .t1) (.block rejectedScalar)
        (.seq (.block (test 3)) (.ite (.zero .t1) (.block rejectedPublic) exhausted)))))

/-- Ask for `p_len` octets: the tape holds less than an attempt. -/
def request : Prog isa := .seq (.block [ldf .t1 2, .li .t2 0, stf .t1 3, stf .t2 14]) zeroOutputs

/-- The tape's length left (`t0`) and `p_len` (`t1`). -/
def room : List Instr := [ldf .t0 10, ldf .t1 2]

/-- `used`, the status, and the caller's `s0` restored. -/
def finish : List Instr := [ldf .t0 15, ldf .t1 11, ldf .a0 14, .store .d .t1 .t0 0, ldf .s0 4]

end VG.Impl.Ffdh.RISCV64.KeyGeneration.Search
