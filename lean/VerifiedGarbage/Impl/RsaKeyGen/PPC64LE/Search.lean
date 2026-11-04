module

public import VerifiedGarbage.Impl.Bignum.PPC64LE.MontMul

/-! # The RSA prime search on PPC64LE

`vg_rsa_prime_search`, as on AArch64 (`Impl/RsaKeyGen/AArch64/Search.lean`):
calls `vg_rsa_keygen_candidate` on the tape's successive candidates until one
is accepted, the budget of counted candidates or the tape's entropy runs
out, or the tape ends inside a candidate (`VG.Spec.RsaKeyGen.primeSearch`).
Its working state is in a frame of its own, of 192 bytes, whose 160 bytes
above the back chain's 32 hold 20 words at `sp − 160`, with their base kept
in the callee-saved `r31` (the caller's `r31` saved in word 4): the state the
caller gives it holds only the four public words, read at the entry and
written back at the exit. The loop runs in a frame saving the link register,
which the calls change; each candidate in a frame of 128 bytes holding its
three stack arguments at offset 96, as the FFDH parameter search does
(`Impl/Ffdh/PPC64LE/Generation/Search.lean`). The comparisons are the sign
bits of differences of numbers below `2^63`, without the carry bit.

`vg_rsa_prime_search(out = r3, out_len = r4, used = r5, e = r6, e_len = r7,
p = r8, p_len = r9, rand = r10, rand_len = [sp + 96], scratch = [sp + 104],
scratch_len = [sp + 112], state = [sp + 120])`.
-/

@[expose] public section

namespace VG.Impl.RsaKeyGen.PPC64LE.Search

open VG VG.PPC64LE VG.Impl.Bignum.PPC64LE

/-- Frame word `j`: the four public words (counted candidates left, the
prime's width, the entropy budget, the request); the caller's `r31`; the
candidate's arguments `out`, `out_len`, `used`, `e`, `e_len`, `p`, `p_len`,
the tape's current pointer and length, `scratch` and `scratch_len`; the
octets consumed; the status (4 while the search goes on); the state's
pointer. Word 32 on is the caller's stack arguments. -/
def ldf (t : Reg) (j : Nat) : Instr := .load .d t .r31 (8 * j)
def stf (t : Reg) (j : Nat) : Instr := .store .d t .r31 (8 * j)

/-- The frame's size, with the back chain's 32 bytes: 20 words above them. -/
def frameBytes : Nat := 192

/-- The frame's words' base in `r31`, the caller's `r31` saved in word 4,
and the register arguments stored. -/
def entrySave : List Instr := [
  .addSp .r11 32, .store .d .r31 .r11 32, .addi .r31 .r11 0,
  stf .r3 5, stf .r4 6, stf .r5 7, stf .r6 8, stf .r7 9, stf .r8 10, stf .r9 11, stf .r10 12]

/-- The stack arguments, above the frame, and the state's first word; then
the public words: the state's first, `out_len` and
`primeEntropy out_len = 32769 out_len`, which the precondition says the
state holds; no request yet, and nothing consumed. -/
def entryLoad : List Instr := [
  ldf .r8 32, ldf .r9 33, ldf .r10 34, ldf .r11 35, .load .d .r12 .r11 0,
  stf .r8 13, stf .r9 14, stf .r10 15, stf .r11 18, stf .r12 0, stf .r4 1,
  .lsl .r12 .r4 15, .add .r12 .r12 .r4, stf .r12 2, .li .r12 0, stf .r12 3, stf .r12 16]

/-- The candidate's stack arguments, for the rest of the tape, at offset 96
of its frame: the tape's length, `scratch` and `scratch_len`. -/
def stackArguments : List Instr := [
  .addSp .r12 96, ldf .r9 13, ldf .r10 14, ldf .r11 15,
  .store .d .r9 .r12 0, .store .d .r10 .r12 8, .store .d .r11 .r12 16]

/-- Its register arguments. -/
def arguments : List Instr := [
  ldf .r3 5, ldf .r4 6, ldf .r5 7, ldf .r6 8, ldf .r7 9, ldf .r8 10, ldf .r9 11, ldf .r10 12]

/-- No more candidates and no request, with `status`. -/
def terminal (status : Nat) : List Instr := [
  .li .r10 0, .li .r11 status, stf .r10 0, stf .r10 3, stf .r11 17]

/-- `out_len` zeros at `out`. -/
def zeroOut : Prog isa :=
  .seq (.block [ldf .r3 5, ldf .r4 6, .li .r5 0]) (countLoop .r4 [.stb .r5 .r3 0, .addi .r3 .r3 1])

/-- Exhausted: zeros at `out`, which no candidate may have written. -/
def exhausted : Prog isa := .seq (.block (terminal 3)) zeroOut

/-- The status, its low 32 bits, into `r9`; the octets the candidate
consumed (`used`) into `r10`. -/
def head : List Instr := [.lsr .w .r9 .r3 0, ldf .r11 7, .load .d .r10 .r11 0]

/-- The prime: its candidate's octets consumed. -/
def accept : List Instr := [ldf .r11 16, .add .r11 .r11 .r10, stf .r11 16] ++ terminal 1

/-- Past a rejected candidate (`r10` octets, status in `r9`): the tape and
the octets consumed advance, and `r8 := status − 2`. -/
def advance : List Instr := [
  ldf .r11 12, ldf .r12 13, ldf .r6 16, .add .r11 .r11 .r10, .sub .r12 .r12 .r10,
  .add .r6 .r6 .r10, .li .r7 4, stf .r11 12, stf .r12 13, stf .r6 16, stf .r7 17, .subi .r8 .r9 2]

/-- A counted rejection (status 3): one candidate fewer. -/
def count : List Instr := [ldf .r11 0, .subi .r11 .r11 1, stf .r11 0]

/-- A candidate rejected, too close (2) or otherwise (3); one that consumed
nothing (which no valid width allows) exhausts the search, as the
specification's progress check does. -/
def reject : Prog isa := .ite (.zero .d .r10) exhausted
  (.seq (.block advance) (.ite (.zero .d .r8) (.block []) (.block count)))

/-- `d := a` if `a < b` (`lt`) or `b` (`¬lt`) for numbers below `2^63`,
through `r0`: the sign of `a − b` as a mask. -/
def sel (d a b : Reg) (lt : Bool) : List Instr :=
  [.sub .r0 a b, .lsr .d .r0 .r0 63, .li d 0, .sub .r0 d .r0] ++
    (if lt then [.logic .xor d a b, .logic .and d d .r0, .logic .xor d d b]
      else [.logic .xor d a b, .logic .and d d .r0, .logic .xor d d a])

/-- The next tape's length, `primeRequest`: twice the larger of the octets
left and 16 per octet of the prime, at most the entropy budget (octets
left in `r10`, the budget in `r11`). -/
def request : List Instr :=
  [ldf .r12 1, .lsl .r12 .r12 4] ++ sel .r6 .r10 .r12 false ++ [.add .r6 .r6 .r6] ++
    sel .r7 .r6 .r11 true ++ [.li .r8 0, stf .r7 3, stf .r8 17]

/-- The tape ended inside a candidate: ask for more, unless the candidate
already had the whole budget. The candidate wrote zeros at `out`. -/
def short : Prog isa :=
  .seq (.block [ldf .r10 13, ldf .r11 2, .sub .r12 .r10 .r11, .lsr .d .r12 .r12 63])
    (.ite (.zero .d .r12) exhausted (.block request))

def classify : Prog isa := .seq (.block (head ++ [.subi .r12 .r9 1]))
  (.ite (.zero .d .r12) (.block accept) (.ite (.zero .d .r9) short reject))

variable (candidate : Prog isa)

/-- The candidate, a call of `vg_rsa_keygen_candidate`, in a frame of its
stack arguments. -/
def candidateRun : Prog isa :=
  .frame (.alloc 128) (.seq (.block stackArguments) (.seq (.block arguments) candidate)) (.free 128)

/-- The loop goes on while the status is 4: `r9 := status − 4`. -/
def iteration : Prog isa :=
  .seq (.block [ldf .r9 0]) (.seq (.ite (.zero .d .r9) exhausted (.seq (candidateRun candidate) classify))
    (.block [ldf .r9 17, .subi .r9 .r9 4]))

def search : Prog isa :=
  .seq (.block [.mflr .r0])
    (.seq (.frame (.push .r0) (.loop (iteration candidate) (.zero .d .r9)) (.pop .r0)) (.block [.mtlr .r0]))

/-- The public words back to the state, the octets consumed to `used`, the
status returned and the caller's `r31` restored: every word loaded before
any is stored. -/
def finish : List Instr := [
  ldf .r8 18, ldf .r9 0, ldf .r10 1, ldf .r11 2, ldf .r12 3, ldf .r7 7, ldf .r6 16, ldf .r3 17,
  ldf .r31 4, .store .d .r9 .r8 0, .store .d .r10 .r8 8, .store .d .r11 .r8 16, .store .d .r12 .r8 24,
  .store .d .r6 .r7 0]

def code : Prog isa := .frame (.alloc frameBytes)
  (.seq (.block entrySave) (.seq (.block entryLoad) (.seq (search candidate) (.block finish)))) (.free frameBytes)

end VG.Impl.RsaKeyGen.PPC64LE.Search
