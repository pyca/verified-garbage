module

public import VerifiedGarbage.Impl.Bignum.AArch64.Core

/-! # The native FFDH key-generation controller on AArch64

As on x86-64 (`Impl/Ffdh/X86_64/KeyGeneration/Search.lean`): repeats an
attempt of `vg_ffdh_generate_key` on successive `p_len` octets of the
random tape until it gives a key, a budget runs out, or the tape does. The
first four state words are the budgets, the width and the next request; the
rest are private working space, whose base is kept in the callee-saved
`x19` (the caller's `x19` saved in word 4). The loop runs in a frame saving
`x30`, which the calls change; each attempt in a frame of 32 bytes holding
its three stack arguments.

`vg_ffdh_generate_key_search(x = x0, x_len = x1, y = x2, y_len = x3,
used = x4, domain = x5, domain_len = x6, p_len = x7, rand = [sp],
rand_len = [sp + 8], scratch = [sp + 16], scratch_len = [sp + 24],
state = [sp + 32])`.
-/

@[expose] public section

namespace VG.Impl.Ffdh.AArch64.KeyGeneration.Search

open VG VG.AArch64 VG.Impl.Bignum.AArch64

/-- Controller word `j`: the key and scalar budgets, `p_len`, the request;
the saved `x19`; `x`, `y`, `domain` and `domain_len`; the tape's current
pointer and length and the octets consumed; `scratch` and `scratch_len`;
the status; `used`. -/
def ldf (t : Reg) (j : Nat) : Instr := .ldr .x t .x19 (8 * j)
def stf (t : Reg) (j : Nat) : Instr := .str .x t .x19 (8 * j)

/-- The stack arguments (from `x14 = sp`), then the caller's `x19` saved and the arguments
stored. -/
def entry : List Instr := [
  .addSp .x14 0, ld .x8 .x14 32, ld .x9 .x14 0, ld .x10 .x14 8, ld .x11 .x14 16, ld .x12 .x14 24,
  .str .x .x19 .x8 32, mov .x19 .x8, movi .x13 0,
  stf .x0 5, stf .x2 6, stf .x5 7, stf .x6 8, stf .x9 9, stf .x10 10, stf .x13 11,
  stf .x11 12, stf .x12 13, stf .x4 15]

/-- `vg_ffdh_generate_key`'s arguments, for `p_len` octets at the tape's
current pointer: its stack arguments at the 32 bytes the attempt's frame
allocates. -/
def arguments : List Instr := [
  ldf .x0 5, ldf .x1 2, ldf .x2 6, ldf .x3 2, ldf .x4 7, ldf .x5 8, ldf .x6 2, ldf .x7 9,
  ldf .x9 12, ldf .x10 13, .addSp .x11 0,
  .str .x .x1 .x11 0, .str .x .x9 .x11 8, .str .x .x10 .x11 16]

/-- Zero the budgets and the request and finish with `status`. -/
def terminal (status : Nat) : List Instr := [
  movi .x10 0, movi .x11 status, stf .x10 0, stf .x10 1, stf .x10 3, stf .x11 14]

/-- `p_len` zeros at the pointer in word `j`. -/
def zeroOut (j : Nat) : Prog isa :=
  .seq (.block [ldf .x1 j, ldf .x2 2, movi .x3 0]) (countLoop .x2 [.strb .x3 .x1 0, .addImm .x .x1 .x1 1])

/-- Zeros at `x` and `y`. -/
def zeroOutputs : Prog isa := .seq (zeroOut 5) (zeroOut 6)

def exhausted : Prog isa := .seq (.block (terminal 3)) zeroOutputs

/-- The status, zero-extended, into `x9`; the attempt's `p_len` octets
consumed. -/
def advance : List Instr := [
  .addImm .w .x9 .x0 0, ldf .x11 2, ldf .x12 9, ldf .x13 10, ldf .x14 11,
  .add .x .x12 .x12 .x11, .sub .x .x13 .x13 .x11, .add .x .x14 .x14 .x11,
  stf .x12 9, stf .x13 10, stf .x14 11]

/-- A scalar out of range: one fewer scalar left. -/
def rejectedScalar : List Instr := [
  ldf .x10 1, .subImm .x .x10 .x10 1, movi .x11 4, stf .x10 1, stf .x11 14]

/-- A degenerate public value: one fewer key left, and the scalar budget
again. -/
def rejectedPublic : List Instr := [
  ldf .x10 0, .subImm .x .x10 .x10 1, movi .x11 128, movi .x12 4, stf .x10 0, stf .x11 1, stf .x12 14]

/-- The status `x9` minus `k`, in `x10`. -/
def test (k : Nat) : List Instr := [.subImm .x .x10 .x9 k]

def classify : Prog isa := .seq (.block (advance ++ test 1))
  (.ite (.zero .x .x10) (.block (terminal 1))
    (.seq (.block (test 2))
      (.ite (.zero .x .x10) (.block rejectedScalar)
        (.seq (.block (test 3)) (.ite (.zero .x .x10) (.block rejectedPublic) exhausted)))))

/-- Ask for `p_len` octets: the tape holds less than an attempt. -/
def request : Prog isa := .seq (.block [ldf .x10 2, movi .x11 0, stf .x10 3, stf .x11 14]) zeroOutputs

/-- `x12 := 1` if the tape holds an attempt, else 0. -/
def room : List Instr := [
  ldf .x9 10, ldf .x10 2, movi .x13 0, movi .x14 1, .subs .x .x11 .x9 .x10, .csel .x .x12 .x14 .x13]

variable (attempt : Prog isa)

/-- The attempt, a call of `vg_ffdh_generate_key`, in a frame of its stack
arguments. -/
def attemptRun : Prog isa := .frame (.alloc 32) (.seq (.block arguments) attempt) (.free 32)

def attemptOrRequest : Prog isa := .seq (.block room)
  (.ite (.zero .x .x12) request (.seq (attemptRun attempt) classify))

def branch : Prog isa :=
  .ite (.zero .x .x9) exhausted (.seq (.block [ldf .x9 1])
    (.ite (.zero .x .x9) exhausted (attemptOrRequest attempt)))

/-- The loop goes on while the status is 4, a rejection: `x9 := status − 4`. -/
def iteration : Prog isa :=
  .seq (.block [ldf .x9 0]) (.seq (branch attempt) (.block [ldf .x9 14, .subImm .x .x9 .x9 4]))

def search : Prog isa := .frame (.push .x30) (.loop (iteration attempt) (.zero .x .x9)) (.pop .x30)

/-- All loads before the store of `used`, and the caller's `x19` restored. -/
def finish : List Instr := [ldf .x1 15, ldf .x2 11, ldf .x0 14, ldf .x19 4, .str .x .x2 .x1 0]

def code : Prog isa := .seq (.block entry) (.seq (search attempt) (.block finish))

end VG.Impl.Ffdh.AArch64.KeyGeneration.Search
