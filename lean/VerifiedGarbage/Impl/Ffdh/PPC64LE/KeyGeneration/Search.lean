module

public import VerifiedGarbage.Impl.Bignum.PPC64LE.MontMul

/-! # The native FFDH key-generation controller on PPC64LE

As on AArch64 (`Impl/Ffdh/AArch64/KeyGeneration/Search.lean`): repeats an
attempt of `vg_ffdh_generate_key` on successive `p_len` octets of the
random tape until it gives a key, a budget runs out, or the tape does. The
first four state words are the budgets, the width and the next request; the
rest are private working space, whose base is kept in the callee-saved
`r31` (the caller's `r31` saved in word 4). The loop runs in a frame saving
the link register, which the calls change; each attempt in a frame of 128
bytes holding its three stack arguments at offset 96. The model has no carry
bit: the tape is short when `len − p_len` is negative and `len` is below
`2^63`.

`vg_ffdh_generate_key_search(x = r3, x_len = r4, y = r5, y_len = r6,
used = r7, domain = r8, domain_len = r9, p_len = r10, rand = [sp + 96],
rand_len = [sp + 104], scratch = [sp + 112], scratch_len = [sp + 120],
state = [sp + 128])`.
-/

@[expose] public section

namespace VG.Impl.Ffdh.PPC64LE.KeyGeneration.Search

open VG VG.PPC64LE VG.Impl.Bignum.PPC64LE

/-- State word `j`: the key and scalar budgets, `p_len`, the request; the
saved `r31`; `x`, `y`, `domain` and `domain_len`; the tape's current pointer
and length and the octets consumed; `scratch` and `scratch_len`; the status;
`used`. -/
def ldf (t : Reg) (j : Nat) : Instr := .load .d t .r31 (8 * j)
def stf (t : Reg) (j : Nat) : Instr := .store .d t .r31 (8 * j)

/-- The state's address from the stack, the caller's `r31` saved, then the
arguments stored. -/
def entry : List Instr :=
  [.addSp .r11 96, .load .d .r12 .r11 32, .store .d .r31 .r12 32, .addi .r31 .r12 0,
    stf .r3 5, stf .r5 6, stf .r8 7, stf .r9 8, stf .r7 15,
    .load .d .r3 .r11 0, .load .d .r4 .r11 8, .load .d .r5 .r11 16, .load .d .r6 .r11 24,
    stf .r3 9, stf .r4 10, .li .r0 0, stf .r0 11, stf .r5 12, stf .r6 13]

/-- `vg_ffdh_generate_key`'s arguments, for `p_len` octets at the tape's
current pointer: its stack arguments at offset 96 of the frame. -/
def arguments : List Instr :=
  [ldf .r3 5, ldf .r4 2, ldf .r5 6, ldf .r6 2, ldf .r7 7, ldf .r8 8, ldf .r9 2, ldf .r10 9,
    ldf .r12 12, ldf .r0 13, .addSp .r11 96, .store .d .r4 .r11 0, .store .d .r12 .r11 8,
    .store .d .r0 .r11 16]

/-- Zero the budgets and the request and finish with `status`. -/
def terminal (status : Nat) : List Instr :=
  [.li .r10 0, .li .r11 status, stf .r10 0, stf .r10 1, stf .r10 3, stf .r11 14]

/-- `p_len` zeros at the pointer in word `j`. -/
def zeroOut (j : Nat) : Prog isa :=
  .seq (.block [ldf .r3 j, ldf .r4 2, .li .r5 0]) (countLoop .r4 [.stb .r5 .r3 0, .addi .r3 .r3 1])

/-- Zeros at `x` and `y`. -/
def zeroOutputs : Prog isa := .seq (zeroOut 5) (zeroOut 6)

def exhausted : Prog isa := .seq (.block (terminal 3)) zeroOutputs

/-- The status, its low 32 bits, into `r9`; the attempt's `p_len` octets
consumed. -/
def advance : List Instr :=
  [.lsl .r9 .r3 32, .lsr .d .r9 .r9 32, ldf .r11 2, ldf .r12 9, ldf .r3 10, ldf .r4 11,
    .add .r12 .r12 .r11, .sub .r3 .r3 .r11, .add .r4 .r4 .r11, stf .r12 9, stf .r3 10, stf .r4 11]

/-- A scalar out of range: one fewer scalar left. -/
def rejectedScalar : List Instr := [ldf .r10 1, .subi .r10 .r10 1, .li .r11 4, stf .r10 1, stf .r11 14]

/-- A degenerate public value: one fewer key left, and the scalar budget
again. -/
def rejectedPublic : List Instr :=
  [ldf .r10 0, .subi .r10 .r10 1, .li .r11 128, .li .r12 4, stf .r10 0, stf .r11 1, stf .r12 14]

/-- The status `r9` minus `k`, in `r10`. -/
def test (k : Nat) : List Instr := [.subi .r10 .r9 k]

def classify : Prog isa := .seq (.block (advance ++ test 1))
  (.ite (.zero .d .r10) (.block (terminal 1))
    (.seq (.block (test 2))
      (.ite (.zero .d .r10) (.block rejectedScalar)
        (.seq (.block (test 3)) (.ite (.zero .d .r10) (.block rejectedPublic) exhausted)))))

/-- Ask for `p_len` octets: the tape holds less than an attempt. -/
def request : Prog isa := .seq (.block [ldf .r10 2, .li .r11 0, stf .r10 3, stf .r11 14]) zeroOutputs

/-- `r12 := 1` if the tape's length is below `p_len`, else 0: the sign of
the difference, unless the length's top bit is set. -/
def room : List Instr :=
  [ldf .r9 10, ldf .r10 2, .sub .r12 .r9 .r10, .lsr .d .r12 .r12 63, .lsr .d .r11 .r9 63,
    .logic .and .r11 .r11 .r12, .logic .xor .r12 .r12 .r11]

variable (attempt : Prog isa)

/-- The attempt, a call of `vg_ffdh_generate_key`, in a frame of its stack
arguments. -/
def attemptRun : Prog isa := .frame (.alloc 128) (.seq (.block arguments) attempt) (.free 128)

def attemptOrRequest : Prog isa := .seq (.block room)
  (.ite (.zero .d .r12) (.seq (attemptRun attempt) classify) request)

def branch : Prog isa :=
  .ite (.zero .d .r9) exhausted (.seq (.block [ldf .r9 1])
    (.ite (.zero .d .r9) exhausted (attemptOrRequest attempt)))

/-- The loop goes on while the status is 4, a rejection: `r9 := status − 4`. -/
def iteration : Prog isa :=
  .seq (.block [ldf .r9 0]) (.seq (branch attempt) (.block [ldf .r9 14, .subi .r9 .r9 4]))

def search : Prog isa :=
  .seq (.block [.mflr .r0])
    (.seq (.frame (.push .r0) (.loop (iteration attempt) (.zero .d .r9)) (.pop .r0)) (.block [.mtlr .r0]))

/-- `used`, the status, and the caller's `r31` restored. -/
def finish : List Instr := [ldf .r4 15, ldf .r5 11, ldf .r3 14, .store .d .r5 .r4 0, ldf .r31 4]

def code : Prog isa := .seq (.block entry) (.seq (search attempt) (.block finish))

end VG.Impl.Ffdh.PPC64LE.KeyGeneration.Search
