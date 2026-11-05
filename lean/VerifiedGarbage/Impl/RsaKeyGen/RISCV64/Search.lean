module

public import VerifiedGarbage.Impl.Bignum.RISCV64.MontMul

/-! # The RSA prime search on RISC-V

`vg_rsa_prime_search`, as on AArch64 (`Impl/RsaKeyGen/AArch64/Search.lean`):
calls `vg_rsa_keygen_candidate` on the tape's successive candidates until one
is accepted, the budget of counted candidates or the tape's entropy runs
out, or the tape ends inside a candidate (`VG.Spec.RsaKeyGen.primeSearch`).
Its working state is in a frame of its own, of 160 bytes, whose base is kept
in the callee-saved `s0` (the caller's `s0` saved in word 4): the state the
caller gives it holds only the four public words, read at the entry and
written back at the exit. The loop runs in a frame saving `ra`, which the
calls change; each candidate in a frame of 32 bytes holding its three stack
arguments. The comparisons are `sltu`, the selections masks of them.

`vg_rsa_prime_search(out = a0, out_len = a1, used = a2, e = a3, e_len = a4,
p = a5, p_len = a6, rand = a7, rand_len = [sp], scratch = [sp + 8],
scratch_len = [sp + 16], state = [sp + 24])`.
-/

@[expose] public section

namespace VG.Impl.RsaKeyGen.RISCV64.Search

open VG VG.RISCV64 VG.Impl.Bignum.RISCV64

/-- Frame word `j`: the four public words (counted candidates left, the
prime's width, the entropy budget, the request); the caller's `s0`; the
candidate's arguments `out`, `out_len`, `used`, `e`, `e_len`, `p`, `p_len`,
the tape's current pointer and length, `scratch` and `scratch_len`; the
octets consumed; the status (4 while the search goes on); the state's
pointer. -/
def ldf (t : Reg) (j : Nat) : Instr := .load .d t .s0 (8 * j)
def stf (t : Reg) (j : Nat) : Instr := .store .d t .s0 (8 * j)

/-- The frame's size: 20 words. -/
def frameBytes : Nat := 160

/-- The frame's base in `t6`; the stack arguments, above the frame, and the
state's first word, all loaded before any store; the caller's `s0` saved and
the arguments stored; then the public words: the state's first, then
`out_len` and `primeEntropy out_len = 32769 out_len`, which the precondition
says the state holds; no request yet, and nothing consumed. -/
def entry : List Instr := [
  .addSp .t6 0, .load .d .t0 .t6 160, .load .d .t1 .t6 168, .load .d .t2 .t6 176, .load .d .t3 .t6 184,
  .load .d .t4 .t3 0, .store .d .s0 .t6 32, .addi .s0 .t6 0,
  stf .a0 5, stf .a1 6, stf .a2 7, stf .a3 8, stf .a4 9, stf .a5 10, stf .a6 11, stf .a7 12,
  stf .t0 13, stf .t1 14, stf .t2 15, stf .t3 18,
  stf .t4 0, stf .a1 1, .shift .sll .d .t4 .a1 15, .add .t4 .t4 .a1, stf .t4 2,
  .li .t5 0, stf .t5 3, stf .t5 16]

/-- The candidate's arguments, for the rest of the tape: its stack
arguments at the 32 bytes the candidate's frame allocates. -/
def arguments : List Instr := [
  ldf .a0 5, ldf .a1 6, ldf .a2 7, ldf .a3 8, ldf .a4 9, ldf .a5 10, ldf .a6 11, ldf .a7 12,
  ldf .t1 13, ldf .t2 14, ldf .t3 15, .addSp .t0 0,
  .store .d .t1 .t0 0, .store .d .t2 .t0 8, .store .d .t3 .t0 16]

/-- No more candidates and no request, with `status`. -/
def terminal (status : Nat) : List Instr := [
  .li .t2 0, .li .t3 status, stf .t2 0, stf .t2 3, stf .t3 17]

/-- `out_len` zeros at `out`. -/
def zeroOut : Prog isa :=
  .seq (.block [ldf .a1 5, ldf .a2 6, .li .a3 0]) (countLoop .a2 [.store .b .a3 .a1 0, .addi .a1 .a1 1])

/-- Exhausted: zeros at `out`, which no candidate may have written. -/
def exhausted : Prog isa := .seq (.block (terminal 3)) zeroOut

/-- The status, its low 32 bits, into `t1`; the octets the candidate
consumed (`used`) into `t2`. -/
def head : List Instr :=
  [.shift .sll .d .t1 .a0 32, .shift .srl .d .t1 .t1 32, ldf .t3 7, .load .d .t2 .t3 0]

/-- The prime: its candidate's octets consumed. -/
def accept : List Instr := [ldf .t3 16, .add .t3 .t3 .t2, stf .t3 16] ++ terminal 1

/-- Past a rejected candidate (`t2` octets, status in `t1`): the tape and
the octets consumed advance, and `t5 := status − 2`. -/
def advance : List Instr := [
  ldf .t3 12, ldf .t4 13, ldf .t5 16, .add .t3 .t3 .t2, .sub .t4 .t4 .t2,
  .add .t5 .t5 .t2, .li .t6 4, stf .t3 12, stf .t4 13, stf .t5 16, stf .t6 17,
  .addi .t5 .t1 (-2)]

/-- A counted rejection (status 3): one candidate fewer. -/
def count : List Instr := [ldf .t3 0, .addi .t3 .t3 (-1), stf .t3 0]

/-- A candidate rejected, too close (2) or otherwise (3); one that consumed
nothing (which no valid width allows) exhausts the search, as the
specification's progress check does. -/
def reject : Prog isa := .ite (.zero .t2) exhausted
  (.seq (.block advance) (.ite (.zero .t5) (.block []) (.block count)))

/-- `d := a` if `a < b` (`lt`) or `b` (`¬lt`), through `t0`: `a < b` as a
mask. -/
def sel (d a b : Reg) (lt : Bool) : List Instr :=
  [.sltu .t0 a b, .li d 0, .sub .t0 d .t0, .logic .xor d a b, .logic .and d d .t0,
    .logic .xor d d (if lt then b else a)]

/-- The next tape's length, `primeRequest`: twice the larger of the octets
left and 16 per octet of the prime, at most the entropy budget (octets
left in `t2`, the budget in `t3`). -/
def request : List Instr :=
  [ldf .t4 1, .shift .sll .d .t4 .t4 4] ++ sel .t5 .t2 .t4 false ++ [.add .t5 .t5 .t5] ++
    sel .t6 .t5 .t3 true ++ [.li .t4 0, stf .t6 3, stf .t4 17]

/-- The tape ended inside a candidate: ask for more, unless the candidate
already had the whole budget. The candidate wrote zeros at `out`. -/
def short : Prog isa :=
  .seq (.block [ldf .t2 13, ldf .t3 2, .sltu .t4 .t2 .t3]) (.ite (.zero .t4) exhausted (.block request))

def classify : Prog isa := .seq (.block (head ++ [.addi .t4 .t1 (-1)]))
  (.ite (.zero .t4) (.block accept) (.ite (.zero .t1) short reject))

variable (candidate : Prog isa)

/-- The candidate, a call of `vg_rsa_keygen_candidate`, in a frame of its
stack arguments. -/
def candidateRun : Prog isa := .frame (.alloc 32) (.seq (.block arguments) candidate) (.free 32)

/-- The loop goes on while the status is 4: `t1 := status − 4`. -/
def iteration : Prog isa :=
  .seq (.block [ldf .t1 0]) (.seq (.ite (.zero .t1) exhausted (.seq (candidateRun candidate) classify))
    (.block [ldf .t1 17, .addi .t1 .t1 (-4)]))

def search : Prog isa := .frame (.push .ra) (.loop (iteration candidate) (.zero .t1)) (.pop .ra)

/-- The public words back to the state, the octets consumed to `used`, the
status returned and the caller's `s0` restored: every word loaded before
any is stored. -/
def finish : List Instr := [
  ldf .t0 18, ldf .t1 0, ldf .t2 1, ldf .t3 2, ldf .t4 3, ldf .t5 7, ldf .t6 16, ldf .a0 17,
  ldf .s0 4, .store .d .t1 .t0 0, .store .d .t2 .t0 8, .store .d .t3 .t0 16, .store .d .t4 .t0 24,
  .store .d .t6 .t5 0]

def code : Prog isa := .frame (.alloc frameBytes)
  (.seq (.block entry) (.seq (search candidate) (.block finish))) (.free frameBytes)

end VG.Impl.RsaKeyGen.RISCV64.Search
