module

public import VerifiedGarbage.Impl.Bignum.AArch64.Core

/-! # The RSA prime search on AArch64

`vg_rsa_prime_search`, as on x86-64 (`Impl/RsaKeyGen/X86_64/Search.lean`):
calls `vg_rsa_keygen_candidate` on the tape's successive candidates until one
is accepted, the budget of counted candidates or the tape's entropy runs
out, or the tape ends inside a candidate (`VG.Spec.RsaKeyGen.primeSearch`).
Its working state is in a frame of its own, of 160 bytes, whose base is kept
in the callee-saved `x19` (the caller's `x19` saved in word 4): the state the
caller gives it holds only the four public words, read at the entry and
written back at the exit. The loop runs in a frame saving `x30`, which the
calls change; each candidate in a frame of 32 bytes holding its three stack
arguments, as the FFDH parameter search does
(`Impl/Ffdh/AArch64/Generation/Search.lean`).

`vg_rsa_prime_search(out = x0, out_len = x1, used = x2, e = x3, e_len = x4,
p = x5, p_len = x6, rand = x7, rand_len = [sp], scratch = [sp + 8],
scratch_len = [sp + 16], state = [sp + 24])`.
-/

@[expose] public section

namespace VG.Impl.RsaKeyGen.AArch64.Search

open VG VG.AArch64 VG.Impl.Bignum.AArch64

/-- Frame word `j`: the four public words (counted candidates left, the
prime's width, the entropy budget, the request); the caller's `x19`; the
candidate's arguments `out`, `out_len`, `used`, `e`, `e_len`, `p`, `p_len`,
the tape's current pointer and length, `scratch` and `scratch_len`; the
octets consumed; the status (4 while the search goes on); the state's
pointer. -/
def ldf (t : Reg) (j : Nat) : Instr := .ldr .x t .x19 (8 * j)
def stf (t : Reg) (j : Nat) : Instr := .str .x t .x19 (8 * j)

/-- The frame's size: 20 words. -/
def frameBytes : Nat := 160

/-- The frame's base in `x14`, the caller's `x19` saved and the register
arguments stored; then the stack arguments, above the frame, and the
public words: the state's first, then `out_len` and
`primeEntropy out_len = 32769 out_len`, which the precondition says the
state holds; no request yet, and nothing consumed. -/
def entry : List Instr := [
  .addSp .x14 0, .str .x .x19 .x14 32, mov .x19 .x14,
  stf .x0 5, stf .x1 6, stf .x2 7, stf .x3 8, stf .x4 9, stf .x5 10, stf .x6 11, stf .x7 12,
  ld .x8 .x14 160, ld .x9 .x14 168, ld .x10 .x14 176, ld .x11 .x14 184,
  stf .x8 13, stf .x9 14, stf .x10 15, stf .x11 18,
  ld .x12 .x11 0, stf .x12 0, stf .x1 1, .lsl .x .x12 .x1 15, .add .x .x12 .x12 .x1, stf .x12 2,
  movi .x13 0, stf .x13 3, stf .x13 16]

/-- The candidate's arguments, for the rest of the tape: its stack
arguments at the 32 bytes the candidate's frame allocates. -/
def arguments : List Instr := [
  ldf .x0 5, ldf .x1 6, ldf .x2 7, ldf .x3 8, ldf .x4 9, ldf .x5 10, ldf .x6 11, ldf .x7 12,
  ldf .x9 13, ldf .x10 14, ldf .x12 15, .addSp .x11 0,
  .str .x .x9 .x11 0, .str .x .x10 .x11 8, .str .x .x12 .x11 16]

/-- No more candidates and no request, with `status`. -/
def terminal (status : Nat) : List Instr := [
  movi .x10 0, movi .x11 status, stf .x10 0, stf .x10 3, stf .x11 17]

/-- `out_len` zeros at `out`. -/
def zeroOut : Prog isa :=
  .seq (.block [ldf .x1 5, ldf .x2 6, movi .x3 0]) (countLoop .x2 [.strb .x3 .x1 0, .addImm .x .x1 .x1 1])

/-- Exhausted: zeros at `out`, which no candidate may have written. -/
def exhausted : Prog isa := .seq (.block (terminal 3)) zeroOut

/-- The status, zero-extended, into `x9`; the octets the candidate
consumed (`used`) into `x10`. -/
def head : List Instr := [.addImm .w .x9 .x0 0, ldf .x11 7, ld .x10 .x11]

/-- The prime: its candidate's octets consumed. -/
def accept : List Instr := [ldf .x11 16, .add .x .x11 .x11 .x10, stf .x11 16] ++ terminal 1

/-- Past a rejected candidate (`x10` octets, status in `x9`): the tape and
the octets consumed advance, and `x13 := status − 2`. -/
def advance : List Instr := [
  ldf .x11 12, ldf .x12 13, ldf .x13 16, .add .x .x11 .x11 .x10, .sub .x .x12 .x12 .x10,
  .add .x .x13 .x13 .x10, movi .x14 4, stf .x11 12, stf .x12 13, stf .x13 16, stf .x14 17,
  .subImm .x .x13 .x9 2]

/-- A counted rejection (status 3): one candidate fewer. -/
def count : List Instr := [ldf .x11 0, .subImm .x .x11 .x11 1, stf .x11 0]

/-- A candidate rejected, too close (2) or otherwise (3); one that consumed
nothing (which no valid width allows) exhausts the search, as the
specification's progress check does. -/
def reject : Prog isa := .ite (.zero .x .x10) exhausted
  (.seq (.block advance) (.ite (.zero .x .x13) (.block []) (.block count)))

/-- The next tape's length, `primeRequest`: twice the larger of the octets
left and 16 per octet of the prime, at most the entropy budget (octets
left in `x10`, the budget in `x11`). -/
def request : List Instr := [
  ldf .x12 1, .lsl .x .x12 .x12 4, .subs .x .x13 .x10 .x12, .csel .x .x10 .x10 .x12,
  .add .x .x10 .x10 .x10, .subs .x .x13 .x10 .x11, .csel .x .x10 .x11 .x10, movi .x12 0,
  stf .x10 3, stf .x12 17]

/-- The tape ended inside a candidate: ask for more, unless the candidate
already had the whole budget. The candidate wrote zeros at `out`. -/
def short : Prog isa := .seq
  (.block [ldf .x10 13, ldf .x11 2, .subs .x .x12 .x10 .x11, movi .x13 0, movi .x14 1,
    .csel .x .x12 .x14 .x13])
  (.ite (.zero .x .x12) (.block request) exhausted)

def classify : Prog isa := .seq (.block (head ++ [.subImm .x .x12 .x9 1]))
  (.ite (.zero .x .x12) (.block accept) (.ite (.zero .x .x9) short reject))

variable (candidate : Prog isa)

/-- The candidate, a call of `vg_rsa_keygen_candidate`, in a frame of its
stack arguments. -/
def candidateRun : Prog isa := .frame (.alloc 32) (.seq (.block arguments) candidate) (.free 32)

/-- The loop goes on while the status is 4: `x9 := status − 4`. -/
def iteration : Prog isa :=
  .seq (.block [ldf .x9 0]) (.seq (.ite (.zero .x .x9) exhausted (.seq (candidateRun candidate) classify))
    (.block [ldf .x9 17, .subImm .x .x9 .x9 4]))

def search : Prog isa := .frame (.push .x30) (.loop (iteration candidate) (.zero .x .x9)) (.pop .x30)

/-- The public words back to the state, the octets consumed to `used`, the
status returned and the caller's `x19` restored: every word loaded before
any is stored. -/
def finish : List Instr := [
  ldf .x8 18, ldf .x9 0, ldf .x10 1, ldf .x11 2, ldf .x12 3, ldf .x13 7, ldf .x14 16, ldf .x0 17,
  ldf .x19 4, st .x9 .x8 0, st .x10 .x8 8, st .x11 .x8 16, st .x12 .x8 24, st .x14 .x13 0]

def code : Prog isa := .frame (.alloc frameBytes)
  (.seq (.block entry) (.seq (search candidate) (.block finish))) (.free frameBytes)

end VG.Impl.RsaKeyGen.AArch64.Search
