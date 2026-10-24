module

public import VerifiedGarbage.Impl.Bignum.PPC64LE.MontMul

/-! # The native FFDH parameter-search controller on PPC64LE

As on AArch64 (`Impl/Ffdh/AArch64/Generation/Search.lean`): repeats
`vg_ffdh_parameter_candidate` on the tape until a candidate is accepted,
the attempts run out, or the tape does, consuming the octets of each
rejected candidate. The first four state words are the attempts left, the
width, the entropy cap and the next request; the rest are private working
space, whose base is kept in the callee-saved `r31` (the caller's `r31`
saved in word 4). The loop runs in a frame saving the link register, which
the calls change; each candidate in a frame of 112 bytes holding its stack
argument at offset 96. The model has no carry bit, so the comparisons are
the sign bits of differences of numbers below `2^63`.

`vg_ffdh_generate_parameters(out = r3, out_len = r4, used = r5, bits = r6,
generator = r7, rand = r8, rand_len = r9, scratch = r10,
scratch_len = [sp + 96], state = [sp + 104])`.
-/

@[expose] public section

namespace VG.Impl.Ffdh.PPC64LE.Generation.Search

open VG VG.PPC64LE VG.Impl.Bignum.PPC64LE

/-- State word `j`: the attempts left, the width, the entropy cap, the
request; the saved `r31`; `out`, `out_len`, `used`, `bits`, the generator;
the tape's current pointer and length and the octets consumed; `scratch`;
the status; `scratch_len`. -/
def ldf (t : Reg) (j : Nat) : Instr := .load .d t .r31 (8 * j)
def stf (t : Reg) (j : Nat) : Instr := .store .d t .r31 (8 * j)

/-- The stack arguments, then the caller's `r31` saved and the arguments
stored, the generator (a `u32`) zero-extended. -/
def entry : List Instr :=
  [.addSp .r11 96, .load .d .r12 .r11 8, .load .d .r11 .r11 0, .store .d .r31 .r12 32, .addi .r31 .r12 0,
    stf .r3 5, stf .r4 6, stf .r5 7, stf .r6 8, .lsr .w .r7 .r7 0, stf .r7 9, stf .r8 10, stf .r9 11, .li .r0 0,
    stf .r0 12, stf .r10 13, stf .r11 15]

/-- `vg_ffdh_parameter_candidate`'s arguments, for the tape's current
pointer and length: its stack argument at offset 96 of the frame. -/
def arguments : List Instr :=
  [ldf .r3 5, ldf .r4 6, ldf .r5 7, ldf .r6 8, ldf .r7 9, ldf .r8 10, ldf .r9 11, ldf .r10 13, ldf .r12 15,
    .addSp .r11 96, .store .d .r12 .r11 0]

/-- Zero the attempts and the request and finish with `status`. -/
def terminal (status : Nat) : List Instr :=
  [.li .r10 0, .li .r11 status, stf .r10 0, stf .r10 3, stf .r11 14]

/-- `out_len` zeros at `out`. -/
def zeroOut : Prog isa :=
  .seq (.block [ldf .r3 5, ldf .r4 6, .li .r5 0]) (countLoop .r4 [.stb .r5 .r3 0, .addi .r3 .r3 1])

def exhausted : Prog isa := .seq (.block (terminal 3)) zeroOut

/-- The status, its low 32 bits, into `r9`; the octets the candidate read
(`used`) into `r10`. -/
def head : List Instr := [.lsl .r9 .r3 32, .lsr .d .r9 .r9 32, ldf .r11 7, .load .d .r10 .r11 0]

/-- An accepted candidate: its octets consumed, and the controller done. -/
def accept : List Instr := [ldf .r11 12, .add .r11 .r11 .r10, stf .r11 12] ++ terminal 1

/-- A rejected candidate: its octets consumed, one fewer attempt left, and
on to the next. -/
def reject : List Instr :=
  [ldf .r11 12, ldf .r12 10, ldf .r3 11, ldf .r4 0, .add .r11 .r11 .r10, .add .r12 .r12 .r10, .sub .r3 .r3 .r10,
    .subi .r4 .r4 1, .li .r5 4, stf .r11 12, stf .r12 10, stf .r3 11, stf .r4 0, stf .r5 14]

/-- `d := a` if `a < b` (`lt`) or `b` (`¬lt`) for numbers below `2^63`,
through `r0`: the sign of `a − b` as a mask. -/
def sel (d a b : Reg) (lt : Bool) : List Instr :=
  [.sub .r0 a b, .lsr .d .r0 .r0 63, .li d 0, .sub .r0 d .r0] ++
    (if lt then [.logic .xor d a b, .logic .and d d .r0, .logic .xor d d b]
      else [.logic .xor d a b, .logic .and d d .r0, .logic .xor d d a])

/-- The next request, `parameterRequest`: twice the larger of the octets
left and 256 per octet of p, at most the entropy cap. -/
def request : List Instr :=
  [ldf .r3 11, ldf .r4 6, ldf .r5 2, .lsl .r4 .r4 8] ++ sel .r6 .r3 .r4 false ++ [.add .r6 .r6 .r6] ++
    sel .r7 .r6 .r5 true ++ [.li .r8 0, stf .r7 3, stf .r8 14]

/-- The tape ran out: exhausted once it holds the entropy cap, else a
request. -/
def short : Prog isa :=
  .seq (.block [ldf .r3 11, ldf .r4 2, .sub .r5 .r3 .r4, .lsr .d .r5 .r5 63])
    (.ite (.zero .d .r5) exhausted (.block request))

def classify : Prog isa := .seq (.block (head ++ [.subi .r12 .r9 1]))
  (.ite (.zero .d .r12) (.block accept)
    (.seq (.block [.subi .r12 .r9 2]) (.ite (.zero .d .r12) (.block reject) short)))

variable (candidate : Prog isa)

/-- The candidate, a call of `vg_ffdh_parameter_candidate`, in a frame of
its stack argument. -/
def candidateRun : Prog isa := .frame (.alloc 112) (.seq (.block arguments) candidate) (.free 112)

/-- The loop goes on while the status is 4, a rejection: `r9 := status − 4`. -/
def iteration : Prog isa :=
  .seq (.block [ldf .r9 0]) (.seq (.ite (.zero .d .r9) exhausted (.seq (candidateRun candidate) classify))
    (.block [ldf .r9 14, .subi .r9 .r9 4]))

def search : Prog isa :=
  .seq (.block [.mflr .r0])
    (.seq (.frame (.push .r0) (.loop (iteration candidate) (.zero .d .r9)) (.pop .r0)) (.block [.mtlr .r0]))

/-- `used`, the status, and the caller's `r31` restored. -/
def finish : List Instr := [ldf .r4 7, ldf .r5 12, ldf .r3 14, .store .d .r5 .r4 0, ldf .r31 4]

def code : Prog isa := .seq (.block entry) (.seq (search candidate) (.block finish))

end VG.Impl.Ffdh.PPC64LE.Generation.Search
