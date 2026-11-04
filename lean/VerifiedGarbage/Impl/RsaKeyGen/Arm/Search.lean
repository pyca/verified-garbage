module

public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey

/-! # The RSA prime search on ARMv7

`vg_rsa_prime_search`, as on AArch64 (`Impl/RsaKeyGen/AArch64/Search.lean`):
calls `vg_rsa_keygen_candidate` on the tape's successive candidates until one
is accepted, the budget of counted candidates or the tape's entropy runs
out, or the tape ends inside a candidate (`VG.Spec.RsaKeyGen.primeSearch`).

Its working state is in the callee-saved registers, which the candidate
keeps: `r4 = out`, `r5 = out_len`, `r6 = used`, `r7 = e`, the octets
consumed in `r8`, the counted candidates left in `r9`, the next tape's length
in `r10` and the status in `r11` (4 while the search goes on). It saves
them, `r12` (for the alignment of the stack) and `lr` in a frame of 40
bytes; the candidate's other arguments it reads from its own stack
arguments each time, and stores them in a frame of 32 bytes. The state's
`u64` words, which are all below `2 ^ 32`, are read and written as their
halves.

`vg_rsa_prime_search(out = r0, out_len = r1, used = r2, e = r3, e_len = [sp],
p = [sp + 4], p_len = [sp + 8], rand = [sp + 12], rand_len = [sp + 16],
scratch = [sp + 20], scratch_len = [sp + 24], state = [sp + 28])`.
-/

@[expose] public section

namespace VG.Impl.RsaKeyGen.Arm.Search

open VG VG.Arm

/-- The bytes the search pushes. -/
def pushBytes : Nat := 40

/-- The stack argument `j` of the search, below `extra` more bytes of frame. -/
def arg (t : Reg) (extra j : Nat) : Instr := .ldrSp t (pushBytes + extra + 4 * j)

/-- The arguments saved; the counted candidates left, the low half of the
state's first word; nothing consumed, no request, and the search goes on. -/
def entry : List Instr := [
  .mov .r4 (.reg .r0), .mov .r5 (.reg .r1), .mov .r6 (.reg .r2), .mov .r7 (.reg .r3),
  arg .r12 0 7, .ldr .r9 .r12 0, .mov .r8 (.imm 0), .mov .r10 (.imm 0), .mov .r11 (.imm 4)]

/-- The candidate's stack argument `j`: the search's, `adjust`ed. -/
def argWord (j : Nat) (adjust : List Instr) : List Instr :=
  arg .r12 32 j :: adjust ++ [.str .r12 .lr (4 * j)]

/-- The candidate's arguments, for the rest of the tape: its stack
arguments at the 32 bytes the candidate's frame allocates (`lr` its base). -/
def arguments : List Instr :=
  [.mov .r0 (.reg .r4), .mov .r1 (.reg .r5), .mov .r2 (.reg .r6), .mov .r3 (.reg .r7), .addSp .lr 0] ++
    argWord 0 [] ++ argWord 1 [] ++ argWord 2 [] ++ argWord 3 [.dp .add .r12 .r12 (.reg .r8)] ++
    argWord 4 [.dp .sub .r12 .r12 (.reg .r8)] ++ argWord 5 [] ++ argWord 6 []

/-- No more candidates and no request, with `status`. -/
def terminal (status : Nat) : List Instr := [
  .mov .r9 (.imm 0), .mov .r10 (.imm 0), .mov .r11 (.imm (BitVec.ofNat 32 status))]

/-- `out_len` zeros at `out`. -/
def zeroOut : Prog isa := .seq (.block [.mov .r0 (.reg .r4), .mov .lr (.reg .r5), .mov .r2 (.imm 0)])
  Impl.Ffdh.Arm.Domain.GenerateKey.zeros

/-- Exhausted: zeros at `out`, which no candidate may have written. -/
def exhausted : Prog isa := .seq (.block (terminal 3)) zeroOut

/-- The prime: its candidate's octets (`r12`) consumed. -/
def accept : List Instr := .dp .add .r8 .r8 (.reg .r12) :: terminal 1

/-- `r0 := r2` if `r0 < r2`; `r3` clobbered. -/
def raise : Prog isa := .seq (.block [.cmp .r0 (.reg .r2), .mov .r3 (.imm 0), .adc .r3 .r3 (.imm 0),
  .cmp .r3 (.imm 0)]) (.ite .eq (.block [.mov .r0 (.reg .r2)]) (.block []))

/-- `r0 := r1` if `r1 ≤ r0`; `r3` clobbered. -/
def cap : Prog isa := .seq (.block [.cmp .r0 (.reg .r1), .mov .r3 (.imm 0), .adc .r3 .r3 (.imm 0),
  .cmp .r3 (.imm 0)]) (.ite .eq (.block []) (.block [.mov .r0 (.reg .r1)]))

/-- The next tape's length, `primeRequest`: twice the larger of the octets
left (`r0`) and 16 per octet of the prime, at most the entropy budget
(`r1`); the search stops, asking for it. -/
def request : Prog isa := .seq (.block [.mov .r2 (.shifted .r5 .lsl 4)])
  (.seq raise (.seq (.block [.dp .add .r0 .r0 (.reg .r0)])
    (.seq cap (.block [.mov .r10 (.reg .r0), .mov .r11 (.imm 0)]))))

/-- The tape ended inside a candidate: ask for more, unless the candidate
already had the whole budget, `32769 out_len`. The candidate wrote zeros at
`out`. -/
def short : Prog isa := .seq
  (.block [arg .r0 0 4, .dp .sub .r0 .r0 (.reg .r8), .mov .r1 (.shifted .r5 .lsl 15),
    .dp .add .r1 .r1 (.reg .r5), .cmp .r0 (.reg .r1)])
  (.ite .eq exhausted request)

/-- A candidate rejected, too close (2) or otherwise (3), after `r12`
octets: they are consumed, and a counted rejection is one candidate fewer;
one that consumed nothing (which no valid width allows) exhausts the search,
as the specification's progress check does. -/
def reject : Prog isa := .seq (.block [.cmp .r12 (.imm 0)]) (.ite .eq exhausted
  (.seq (.block [.dp .add .r8 .r8 (.reg .r12), .cmp .r0 (.imm 3)])
    (.ite .eq (.block [.dp .sub .r9 .r9 (.imm 1)]) (.block []))))

/-- The candidate's status in `r0`, the octets it consumed (the low half of
`used`) in `r12`. -/
def classify : Prog isa := .seq (.block [.ldr .r12 .r6 0, .cmp .r0 (.imm 1)])
  (.ite .eq (.block accept) (.seq (.block [.cmp .r0 (.imm 0)]) (.ite .eq short reject)))

variable (candidate : Prog isa)

/-- The candidate, a call of `vg_rsa_keygen_candidate`, in a frame of its
stack arguments. -/
def candidateRun : Prog isa := .frame (.alloc 32) (.seq (.block arguments) candidate) (.free 32)

/-- The candidate, unless fewer than `out_len` octets are left, which no
candidate fits in: then the tape ended inside one (status 0, as the
candidate would return), with zeros at `out`, and the candidate is not
called, which keeps the tape's pointer within it. -/
def candidateStep : Prog isa := .seq
  (.block [arg .r0 0 4, .dp .sub .r0 .r0 (.reg .r8), .cmp .r0 (.reg .r5), .mov .r12 (.imm 0),
    .adc .r12 .r12 (.imm 0), .cmp .r12 (.imm 0)])
  (.ite .eq (.seq zeroOut short) (.seq (candidateRun candidate) classify))

/-- The loop goes on while the status is 4. -/
def iteration : Prog isa :=
  .seq (.block [.cmp .r9 (.imm 0)]) (.seq (.ite .eq exhausted (candidateStep candidate))
    (.block [.cmp .r11 (.imm 4)]))

/-- The state's words (the counted candidates left, `out_len`, the budget
`32769 out_len` and the request, high halves zero), the octets consumed to
`used`, the status returned and the callee-saved registers restored. -/
def finish : List Instr := [
  arg .r12 0 7, .mov .r0 (.imm 0), .mov .r1 (.shifted .r5 .lsl 15), .dp .add .r1 .r1 (.reg .r5),
  .str .r9 .r12 0, .str .r0 .r12 4, .str .r5 .r12 8, .str .r0 .r12 12, .str .r1 .r12 16,
  .str .r0 .r12 20, .str .r10 .r12 24, .str .r0 .r12 28, .str .r8 .r6 0, .str .r0 .r6 4,
  .mov .r0 (.reg .r11),
  .ldrSp .r5 4, .ldrSp .r6 8, .ldrSp .r7 12, .ldrSp .r8 16, .ldrSp .r9 20, .ldrSp .r10 24,
  .ldrSp .r11 28, .ldrSp .lr 36]

def body : Prog isa := .seq (.block entry) (.seq (.loop (iteration candidate) .eq) (.block finish))

def code : Prog isa :=
  .frame (.push [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) (body candidate) (.pop .r4 pushBytes)

end VG.Impl.RsaKeyGen.Arm.Search
