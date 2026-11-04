module

public import VerifiedGarbage.Impl.Bignum.AArch64.Core

/-! # The RSA prime search on AArch64

`vg_rsa_prime_search`, as on x86-64 (`Impl/RsaKeyGen/X86_64/Search.lean`):
calls `vg_rsa_keygen_candidate` on the tape's successive candidates until
one is accepted, the budget of counted candidates or the tape's entropy
runs out, or the tape ends inside a candidate
(`VG.Spec.RsaKeyGen.primeSearch`). Its working state is in a frame of its
own, whose base it keeps in the callee-saved `x19` (the caller's `x19` saved
in word 4), laid out as FFDH's parameter search's controller
(`Impl/Ffdh/AArch64/Generation/Search.lean`): the state the caller gives it
holds only the four public words, which it reads at its entry and writes
back at its exit. The loop runs in a frame saving `x30`, which the calls
change; each candidate in a frame of 32 bytes holding its three stack
arguments.

`vg_rsa_prime_search(out = x0, out_len = x1, used = x2, e = x3, e_len = x4,
p = x5, p_len = x6, rand = x7, rand_len = [sp], scratch = [sp + 8],
scratch_len = [sp + 16], state = [sp + 24])`.
-/

@[expose] public section

namespace VG.Impl.RsaKeyGen.AArch64.Search

open VG VG.AArch64 VG.Impl.Bignum.AArch64

/-- Frame word `j`: the counted candidates left, the width, the entropy
budget, the request; the saved `x19`; `out`, `out_len`, `used`, `e`,
`e_len`; the tape's current pointer and length and the octets consumed;
`scratch`; the status (4 while the search goes on); `scratch_len`; `p`,
`p_len`; the state's pointer. -/
def ldf (t : Reg) (j : Nat) : Instr := .ldr .x t .x19 (8 * j)
def stf (t : Reg) (j : Nat) : Instr := .str .x t .x19 (8 * j)

/-- The frame's size: 20 words. -/
def frameBytes : Nat := 160

/-- In the frame: the stack arguments (from `x14`, the caller's stack
pointer) and the state's first word, the counted candidates left; the
caller's `x19` saved, and the frame's base in `x19`. -/
def entryHead : List Instr := [
  .addSp .x14 frameBytes, ld .x9 .x14 0, ld .x10 .x14 8, ld .x11 .x14 16, ld .x12 .x14 24, ld .x13 .x12 0,
  .addSp .x8 0, .str .x .x19 .x8 32, mov .x19 .x8]

/-- The frame's words for registers: the arguments, the counted candidates
left and the width. -/
def entryStores : List (Reg × Nat) := [
  (.x0, 5), (.x1, 6), (.x2, 7), (.x3, 8), (.x4, 9), (.x7, 10), (.x9, 11), (.x10, 13), (.x11, 15),
  (.x5, 16), (.x6, 17), (.x12, 18), (.x13, 0), (.x1, 1)]

/-- The entropy budget `primeEntropy out_len = 32769 out_len`, which the
precondition says the state holds; no request yet, and nothing consumed. -/
def entryWords : List Instr := [
  .lsl .x .x13 .x1 15, .add .x .x13 .x13 .x1, stf .x13 2, movi .x13 0, stf .x13 3, stf .x13 12]

def entry : List Instr := entryHead ++ entryStores.map (fun e => stf e.1 e.2) ++ entryWords

/-- `vg_rsa_keygen_candidate`'s arguments, for the tape's current pointer
and length: its stack arguments at the 32 bytes the candidate's frame
allocates. -/
def arguments : List Instr := [
  ldf .x0 5, ldf .x1 6, ldf .x2 7, ldf .x3 8, ldf .x4 9, ldf .x5 16, ldf .x6 17, ldf .x7 10,
  ldf .x9 11, ldf .x10 13, ldf .x11 15, .addSp .x12 0, .str .x .x9 .x12 0, .str .x .x10 .x12 8,
  .str .x .x11 .x12 16]

/-- Zero the counted candidates and the request and finish with `status`. -/
def terminal (status : Nat) : List Instr := [
  movi .x10 0, movi .x11 status, stf .x10 0, stf .x10 3, stf .x11 14]

/-- `out_len` zeros at `out`, which no candidate may have written. -/
def zeroOut : Prog isa :=
  .seq (.block [ldf .x1 5, ldf .x2 6, movi .x3 0]) (countLoop .x2 [.strb .x3 .x1 0, .addImm .x .x1 .x1 1])

def exhausted : Prog isa := .seq (.block (terminal 3)) zeroOut

/-- The status, zero-extended, into `x9`; the octets the candidate read
(`used`) into `x10`. -/
def head : List Instr := [.addImm .w .x9 .x0 0, ldf .x11 7, ld .x10 .x11]

/-- An accepted candidate: its octets consumed, and the search done. -/
def accept : List Instr := [ldf .x11 12, .add .x .x11 .x11 .x10, stf .x11 12] ++ terminal 1

/-- Past a rejected candidate (status 2, too close, or 3, in `x9`): its
octets consumed, and one fewer counted candidate left for a counted
rejection (`x9 − 2` of them). -/
def reject : List Instr := [
  ldf .x11 12, ldf .x12 10, ldf .x13 11, ldf .x14 0, .add .x .x11 .x11 .x10, .add .x .x12 .x12 .x10,
  .sub .x .x13 .x13 .x10, .subImm .x .x15 .x9 2, .sub .x .x14 .x14 .x15, movi .x15 4,
  stf .x11 12, stf .x12 10, stf .x13 11, stf .x14 0, stf .x15 14]

/-- A rejected candidate that consumed nothing (which no valid width
allows) exhausts the search, as the specification's progress check does. -/
def rejected : Prog isa := .ite (.zero .x .x10) exhausted (.block reject)

/-- The next request, `primeRequest`: twice the larger of the octets left
and 16 per octet of the prime, at most the entropy budget. -/
def request : List Instr := [
  ldf .x10 11, ldf .x11 6, ldf .x12 2, .lsl .x .x11 .x11 4, .subs .x .x13 .x10 .x11, .csel .x .x10 .x10 .x11,
  .add .x .x10 .x10 .x10, .subs .x .x13 .x10 .x12, .csel .x .x10 .x12 .x10, movi .x11 0, stf .x10 3, stf .x11 14]

/-- The tape ended inside a candidate: ask for more, unless the candidate
already had the whole budget. The candidate wrote zeros at `out`. -/
def short : Prog isa := .seq
  (.block [ldf .x10 11, ldf .x11 2, .subs .x .x12 .x10 .x11, movi .x13 0, movi .x14 1, .csel .x .x12 .x14 .x13])
  (.ite (.zero .x .x12) (.block request) exhausted)

def classify : Prog isa := .seq (.block (head ++ [.subImm .x .x12 .x9 1]))
  (.ite (.zero .x .x12) (.block accept) (.ite (.zero .x .x9) short rejected))

variable (candidate : Prog isa)

/-- The candidate, a call of `vg_rsa_keygen_candidate`, in a frame of its
stack arguments. -/
def candidateRun : Prog isa := .frame (.alloc 32) (.seq (.block arguments) candidate) (.free 32)

/-- The loop goes on while the status is 4, a rejection: `x9 := status − 4`. -/
def iteration : Prog isa :=
  .seq (.block [ldf .x9 0]) (.seq (.ite (.zero .x .x9) exhausted (.seq (candidateRun candidate) classify))
    (.block [ldf .x9 14, .subImm .x .x9 .x9 4]))

def search : Prog isa := .frame (.push .x30) (.loop (iteration candidate) (.zero .x .x9)) (.pop .x30)

/-- The public words back to the state, the octets consumed to `used`, the
status returned and the caller's `x19` restored: every word loaded before
any is stored. -/
def finish : List Instr := [
  ldf .x12 18, ldf .x9 0, ldf .x10 1, ldf .x11 2, ldf .x13 3, ldf .x1 7, ldf .x2 12, ldf .x0 14, ldf .x19 4,
  st .x9 .x12 0, st .x10 .x12 8, st .x11 .x12 16, st .x13 .x12 24, st .x2 .x1 0]

def code : Prog isa := .frame (.alloc frameBytes)
  (.seq (.block entry) (.seq (search candidate) (.block finish))) (.free frameBytes)

end VG.Impl.RsaKeyGen.AArch64.Search
