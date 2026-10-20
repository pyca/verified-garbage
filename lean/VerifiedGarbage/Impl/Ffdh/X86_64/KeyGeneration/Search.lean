module

public import VerifiedGarbage.Impl.Rsa.X86_64.Keys

/-! # The native FFDH key-generation controller

Repeats an attempt of `vg_ffdh_generate_key` on successive `p_len` octets of
the random tape until it gives a key, a budget runs out, or the tape does:
range and degenerate-public-value rejections never return to the host. The
first four state words are the budgets, the width and the next request; the
rest are private working space.
-/

@[expose] public section

namespace VG.Impl.Ffdh.X86_64.KeyGeneration.Search

open VG VG.X86_64 VG.Impl.Bignum.X86_64

/-- Controller slots: the key and scalar budgets, `p_len`, the request; the
saved r12; `x`, `y`, `domain` and `domain_len`; the tape's current pointer
and length and the octets consumed; `scratch` and `scratch_len`; the status;
`used`. -/
def field (j : Nat) : MemOp := { base := .r12, disp := (8 * j : Nat) }

/-- `state` is the seventh argument on the stack. -/
def entryHead : List Instr := [
  .mov .rax (.mem { base := .rsp, disp := 56 }), .store { base := .rax, disp := 32 } .r12,
  .mov .r12 (.reg .rax), .store (field 5) .rdi, .store (field 6) .rdx,
  .store (field 15) .r8, .store (field 7) .r9]

def entryTail : List Instr := [
  .mov .r10 (.mem { base := .rsp, disp := 8 }), .mov .r11 (.mem { base := .rsp, disp := 24 }),
  .mov .rax (.mem { base := .rsp, disp := 32 }), .mov .rcx (.mem { base := .rsp, disp := 40 }),
  .mov .rsi (.mem { base := .rsp, disp := 48 }),
  .store (field 8) .r10, .store (field 9) .r11, .store (field 10) .rax,
  .store (field 12) .rcx, .store (field 13) .rsi,
  .mov32 .rax (.imm 0), .store (field 11) .rax]

def entry : List Instr := entryHead ++ entryTail

/-- `vg_ffdh_generate_key`'s arguments, for `p_len` octets at the tape's
current pointer: its stack arguments at the 40 octets the attempt's frame
allocates, where the callee finds them above its return address. -/
def arguments : List Instr := [
  .mov .rdi (.mem (field 5)), .mov .rsi (.mem (field 2)), .mov .rdx (.mem (field 6)),
  .mov .rcx (.mem (field 2)), .mov .r8 (.mem (field 7)), .mov .r9 (.mem (field 8)),
  .mov .rax (.mem (field 9)), .mov .r10 (.mem (field 12)), .mov .r11 (.mem (field 13)),
  .store { base := .rsp } .rsi, .store { base := .rsp, disp := 16 } .rsi,
  .store { base := .rsp, disp := 8 } .rax, .store { base := .rsp, disp := 24 } .r10,
  .store { base := .rsp, disp := 32 } .r11]

/-- Zero the budgets and the request and finish with `status`. -/
def terminal (status : Nat) : List Instr := [
  .mov32 .rax (.imm 0), .store (field 0) .rax, .store (field 1) .rax, .store (field 3) .rax,
  .mov32 .rax (.imm (BitVec.ofNat 32 status)), .store (field 14) .rax]

/-- Zeros at `x` and `y`. -/
def zeroOutputs : Prog isa := .seq (.block [.mov .rdi (.reg .r12)])
  (.seq (VG.Impl.Rsa.X86_64.Keys.zeroOut 5 2) (VG.Impl.Rsa.X86_64.Keys.zeroOut 6 2))

def exhausted : Prog isa := .seq (.block (terminal 3)) zeroOutputs

/-- Consume the attempt's `p_len` octets. -/
def advance : List Instr := [
  .mov .rcx (.mem (field 2)), .mov .rdx (.mem (field 9)), .mov .rsi (.mem (field 10)),
  .mov .r8 (.mem (field 11)),
  .alu .add .rdx (.reg .rcx), .alu .sub .rsi (.reg .rcx), .alu .add .r8 (.reg .rcx),
  .store (field 9) .rdx, .store (field 10) .rsi, .store (field 11) .r8]

/-- A scalar out of range: one fewer scalar left. -/
def rejectedScalar : List Instr := [
  .mov .rax (.mem (field 1)), .alu .sub .rax (.imm 1), .store (field 1) .rax,
  .mov32 .rax (.imm 4), .store (field 14) .rax]

/-- A degenerate public value: one fewer key left, and the scalar budget
again. -/
def rejectedPublic : List Instr := [
  .mov .rax (.mem (field 0)), .alu .sub .rax (.imm 1), .store (field 0) .rax,
  .mov32 .rax (.imm 128), .store (field 1) .rax,
  .mov32 .rax (.imm 4), .store (field 14) .rax]

def classify : Prog isa := .seq (.block ([.mov32 .rax (.reg .rax)] ++ advance ++ [.alu .cmp .rax (.imm 1)]))
  (.ite .e (.block (terminal 1))
    (.seq (.block [.alu .cmp .rax (.imm 2)])
      (.ite .e (.block rejectedScalar)
        (.seq (.block [.alu .cmp .rax (.imm 3)]) (.ite .e (.block rejectedPublic) exhausted)))))

/-- Ask for `p_len` octets: the tape holds less than an attempt. -/
def request : Prog isa := .seq (.block [
  .mov .rax (.mem (field 2)), .store (field 3) .rax,
  .mov32 .rax (.imm 0), .store (field 14) .rax]) zeroOutputs

variable (attempt : Prog isa)

/-- The attempt, a call of `vg_ffdh_generate_key`, in a frame of its
arguments; 40 octets keep the callee's stack pointer as the ABI aligns it. -/
def attemptRun : Prog isa := .frame (.alloc 40)
  (.seq (.block arguments) attempt) (.free 40)

def attemptOrRequest : Prog isa := .seq
  (.block [.mov .rax (.mem (field 10)), .alu .cmp .rax (.mem (field 2))])
  (.ite .b request (.seq (attemptRun attempt) classify))

def iteration : Prog isa := seqs [
  .block [.mov .rax (.mem (field 0)), .alu .test .rax (.reg .rax)],
  .ite .e exhausted (.seq (.block [.mov .rax (.mem (field 1)), .alu .test .rax (.reg .rax)])
    (.ite .e exhausted (attemptOrRequest attempt))),
  .block [.mov .rax (.mem (field 14)), .alu .cmp .rax (.imm 4)]]

def finish : List Instr := [
  .mov .rdx (.mem (field 15)), .mov .rcx (.mem (field 11)),
  .mov .rax (.mem (field 14)), .mov .r12 (.mem (field 4)), .store { base := .rdx } .rcx]

def code : Prog isa := seqs [.block entry, .loop (iteration attempt) .e, .block finish]

end VG.Impl.Ffdh.X86_64.KeyGeneration.Search
