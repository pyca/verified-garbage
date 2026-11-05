module

public import VerifiedGarbage.Impl.Bignum.RISCV64.MontMul

/-! # The native FFDH parameter-search controller on RISC-V

As on PPC64LE (`Impl/Ffdh/PPC64LE/Generation/Search.lean`): repeats
`vg_ffdh_parameter_candidate_sieved` on the tape until a candidate is accepted,
the attempts run out, or the tape does, consuming the octets of each
rejected candidate. The first four state words are the attempts left, the
width, the entropy cap and the next request; the rest are private working
space, whose base is kept in the callee-saved `s0` (the caller's `s0` saved
in word 4). The loop runs in a frame saving `ra`, which the calls change;
each candidate in a frame of 16 bytes holding its stack argument at its
base. The comparisons are unsigned (`sltu`, `bltu`).

`vg_ffdh_generate_parameters(out = a0, out_len = a1, used = a2, bits = a3,
generator = a4, rand = a5, rand_len = a6, scratch = a7,
scratch_len = [sp], state = [sp + 8])`.
-/

@[expose] public section

namespace VG.Impl.Ffdh.RISCV64.Generation.Search

open VG VG.RISCV64 VG.Impl.Bignum.RISCV64

/-- State word `j`: the attempts left, the width, the entropy cap, the
request; the saved `s0`; `out`, `out_len`, `used`, `bits`, the generator;
the tape's current pointer and length and the octets consumed; `scratch`;
the status; `scratch_len`. -/
def ldf (t : Reg) (j : Nat) : Instr := .load .d t .s0 (8 * j)
def stf (t : Reg) (j : Nat) : Instr := .store .d t .s0 (8 * j)

/-- The state's address and `scratch_len` loaded, the caller's `s0` saved,
then the arguments stored, the generator (a `u32`) zero-extended. -/
def entry : List Instr :=
  [.addSp .t1 0, .load .d .t2 .t1 8, .load .d .t3 .t1 0, .store .d .s0 .t2 32, .addi .s0 .t2 0,
    stf .a0 5, stf .a1 6, stf .a2 7, stf .a3 8, .shift .sll .d .t4 .a4 32, .shift .srl .d .t4 .t4 32,
    stf .t4 9, stf .a5 10, stf .a6 11, .li .t1 0, stf .t1 12, stf .a7 13, stf .t3 15]

/-- `vg_ffdh_parameter_candidate_sieved`'s arguments, for the tape's current
pointer and length: its stack argument at the frame's base. -/
def arguments : List Instr :=
  [ldf .a0 5, ldf .a1 6, ldf .a2 7, ldf .a3 8, ldf .a4 9, ldf .a5 10, ldf .a6 11, ldf .a7 13, ldf .t0 15,
    .addSp .t1 0, .store .d .t0 .t1 0]

/-- Zero the attempts and the request and finish with `status`. -/
def terminal (status : Nat) : List Instr :=
  [.li .t4 0, .li .t5 status, stf .t4 0, stf .t4 3, stf .t5 14]

/-- `out_len` zeros at `out`. -/
def zeroOut : Prog isa :=
  .seq (.block [ldf .t0 5, ldf .t1 6, .li .t2 0]) (countLoop .t1 [.store .b .t2 .t0 0, .addi .t0 .t0 1])

def exhausted : Prog isa := .seq (.block (terminal 3)) zeroOut

/-- The status, its low 32 bits, into `t0`; the octets the candidate read
(`used`) into `t2`. -/
def head : List Instr := [.shift .sll .d .t0 .a0 32, .shift .srl .d .t0 .t0 32, ldf .t2 7, .load .d .t2 .t2 0]

/-- The status `t0` minus `k`, in `t1`. -/
def test (k : Nat) : List Instr := [.addi .t1 .t0 (-(k : Int))]

/-- An accepted candidate: its octets consumed, and the controller done. -/
def accept : List Instr := [ldf .t3 12, .add .t3 .t3 .t2, stf .t3 12] ++ terminal 1

/-- A rejected candidate: its octets consumed, one fewer attempt left, and
on to the next. -/
def reject : List Instr :=
  [ldf .t3 12, ldf .t4 10, ldf .t5 11, ldf .t6 0, .add .t3 .t3 .t2, .add .t4 .t4 .t2, .sub .t5 .t5 .t2,
    .addi .t6 .t6 (-1), .li .t1 4, stf .t3 12, stf .t4 10, stf .t5 11, stf .t6 0, stf .t1 14]

/-- `d :=` the smaller of `a` and `b` (`lt`), or the larger, unsigned,
through `t4`: `a < b` less one as a mask, all ones unless `a < b`. -/
def sel (d a b : Reg) (lt : Bool) : List Instr :=
  [.sltu .t4 a b, .addi .t4 .t4 (-1), .logic .xor d a b, .logic .and d d .t4] ++
    (if lt then [.logic .xor d d a] else [.logic .xor d d b])

/-- The next request, `VG.Proof.Ffdh.parameterRequest`: twice the larger of the octets
left and 256 per octet of p, at most the entropy cap. -/
def request : List Instr :=
  [ldf .t0 11, ldf .t1 6, ldf .t2 2, .shift .sll .d .t1 .t1 8] ++ sel .t3 .t0 .t1 false ++
    [.add .t3 .t3 .t3] ++ sel .t5 .t3 .t2 true ++ [.li .t6 0, stf .t5 3, stf .t6 14]

/-- The tape ran out: exhausted once it holds the entropy cap, else a
request. -/
def short : Prog isa :=
  .seq (.block [ldf .t0 11, ldf .t1 2]) (.ite (.ltu .t0 .t1) (.block request) exhausted)

def classify : Prog isa := .seq (.block (head ++ test 1))
  (.ite (.zero .t1) (.block accept)
    (.seq (.block (test 2)) (.ite (.zero .t1) (.block reject) short)))

variable (candidate : Prog isa)

/-- The candidate, a call of `vg_ffdh_parameter_candidate_sieved`, in a frame of
its stack argument. -/
def candidateRun : Prog isa := .frame (.alloc 16) (.seq (.block arguments) candidate) (.free 16)

/-- The loop goes on while the status is 4, a rejection: `t0 := status − 4`. -/
def iteration : Prog isa :=
  .seq (.block [ldf .t0 0]) (.seq (.ite (.zero .t0) exhausted (.seq (candidateRun candidate) classify))
    (.block [ldf .t0 14, .addi .t0 .t0 (-4)]))

def search : Prog isa := .frame (.push .ra) (.loop (iteration candidate) (.zero .t0)) (.pop .ra)

/-- `used`, the status, and the caller's `s0` restored. -/
def finish : List Instr := [ldf .t0 7, ldf .t1 12, ldf .a0 14, .store .d .t1 .t0 0, ldf .s0 4]

def code : Prog isa := .seq (.block entry) (.seq (search candidate) (.block finish))

end VG.Impl.Ffdh.RISCV64.Generation.Search
