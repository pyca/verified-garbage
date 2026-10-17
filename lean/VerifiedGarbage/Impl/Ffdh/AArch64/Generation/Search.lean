module

public import VerifiedGarbage.Impl.Bignum.AArch64.Core

/-! # The native FFDH parameter-search controller on AArch64

As on x86-64 (`Impl/Ffdh/X86_64/Generation/Search.lean`): repeats
`vg_ffdh_parameter_candidate` on the tape until a candidate is accepted,
the attempts run out, or the tape does, consuming the octets of each
rejected candidate. The first four state words are the attempts left, the
width, the entropy cap and the next request; the rest are private working
space, whose base is kept in the callee-saved `x19` (the caller's `x19`
saved in word 4). The loop runs in a frame saving `x30`, which the calls
change; each candidate in a frame of 16 bytes holding its stack argument.

`vg_ffdh_generate_parameters(out = x0, out_len = x1, used = x2, bits = x3,
generator = w4, rand = x5, rand_len = x6, scratch = x7,
scratch_len = [sp], state = [sp + 8])`.
-/

@[expose] public section

namespace VG.Impl.Ffdh.AArch64.Generation.Search

open VG VG.AArch64 VG.Impl.Bignum.AArch64

/-- Controller word `j`: the attempts left, the width, the entropy cap, the
request; the saved `x19`; `out`, `out_len`, `used`, `bits`, the generator;
the tape's current pointer and length and the octets consumed; `scratch`;
the status; `scratch_len`. -/
def ldf (t : Reg) (j : Nat) : Instr := .ldr .x t .x19 (8 * j)
def stf (t : Reg) (j : Nat) : Instr := .str .x t .x19 (8 * j)

/-- The stack arguments (from `x14 = sp`), then the caller's `x19` saved and
the arguments stored. -/
def entry : List Instr := [
  .addSp .x14 0, ld .x8 .x14 8, ld .x9 .x14 0, .addImm .w .x4 .x4 0, .str .x .x19 .x8 32, mov .x19 .x8,
  movi .x13 0, stf .x0 5, stf .x1 6, stf .x2 7, stf .x3 8, stf .x4 9, stf .x5 10, stf .x6 11, stf .x13 12,
  stf .x7 13, stf .x9 15]

/-- `vg_ffdh_parameter_candidate`'s arguments, for the tape's current
pointer and length: its stack argument at the 16 bytes the candidate's
frame allocates. -/
def arguments : List Instr := [
  ldf .x0 5, ldf .x1 6, ldf .x2 7, ldf .x3 8, ldf .x4 9, ldf .x5 10, ldf .x6 11, ldf .x7 13, ldf .x9 15,
  .addSp .x11 0, .str .x .x9 .x11 0]

/-- Zero the attempts and the request and finish with `status`. -/
def terminal (status : Nat) : List Instr := [
  movi .x10 0, movi .x11 status, stf .x10 0, stf .x10 3, stf .x11 14]

/-- `out_len` zeros at `out`. -/
def zeroOut : Prog isa :=
  .seq (.block [ldf .x1 5, ldf .x2 6, movi .x3 0]) (countLoop .x2 [.strb .x3 .x1 0, .addImm .x .x1 .x1 1])

def exhausted : Prog isa := .seq (.block (terminal 3)) zeroOut

/-- The status, zero-extended, into `x9`; the octets the candidate read
(`used`) into `x10`. -/
def head : List Instr := [.addImm .w .x9 .x0 0, ldf .x11 7, ld .x10 .x11]

/-- An accepted candidate: its octets consumed, and the controller done. -/
def accept : List Instr := [ldf .x11 12, .add .x .x11 .x11 .x10, stf .x11 12] ++ terminal 1

/-- A rejected candidate: its octets consumed, one fewer attempt left, and
on to the next. -/
def reject : List Instr := [
  ldf .x11 12, ldf .x12 10, ldf .x13 11, ldf .x14 0, .add .x .x11 .x11 .x10, .add .x .x12 .x12 .x10,
  .sub .x .x13 .x13 .x10, .subImm .x .x14 .x14 1, movi .x15 4, stf .x11 12, stf .x12 10, stf .x13 11, stf .x14 0,
  stf .x15 14]

/-- The next request, `parameterRequest`: twice the larger of the octets
left and 256 per octet of `p`, at most the entropy cap. -/
def request : List Instr := [
  ldf .x10 11, ldf .x11 6, ldf .x12 2, .lsl .x .x11 .x11 8, .subs .x .x13 .x10 .x11, .csel .x .x10 .x10 .x11,
  .add .x .x10 .x10 .x10, .subs .x .x13 .x10 .x12, .csel .x .x10 .x12 .x10, movi .x11 0, stf .x10 3, stf .x11 14]

/-- The tape ran out: exhausted once it holds the entropy cap, else a
request. -/
def short : Prog isa := .seq
  (.block [ldf .x10 11, ldf .x11 2, .subs .x .x12 .x10 .x11, movi .x13 0, movi .x14 1, .csel .x .x12 .x14 .x13])
  (.ite (.zero .x .x12) (.block request) exhausted)

def classify : Prog isa := .seq (.block (head ++ [.subImm .x .x12 .x9 1]))
  (.ite (.zero .x .x12) (.block accept)
    (.seq (.block [.subImm .x .x12 .x9 2]) (.ite (.zero .x .x12) (.block reject) short)))

variable (candidate : Prog isa)

/-- The candidate, a call of `vg_ffdh_parameter_candidate`, in a frame of
its stack argument. -/
def candidateRun : Prog isa := .frame (.alloc 16) (.seq (.block arguments) candidate) (.free 16)

/-- The loop goes on while the status is 4, a rejection: `x9 := status − 4`. -/
def iteration : Prog isa :=
  .seq (.block [ldf .x9 0]) (.seq (.ite (.zero .x .x9) exhausted (.seq (candidateRun candidate) classify))
    (.block [ldf .x9 14, .subImm .x .x9 .x9 4]))

def search : Prog isa := .frame (.push .x30) (.loop (iteration candidate) (.zero .x .x9)) (.pop .x30)

/-- All loads before the store of `used`, and the caller's `x19` restored. -/
def finish : List Instr := [ldf .x1 7, ldf .x2 12, ldf .x0 14, ldf .x19 4, .str .x .x2 .x1 0]

def code : Prog isa := .seq (.block entry) (.seq (search candidate) (.block finish))

end VG.Impl.Ffdh.AArch64.Generation.Search
