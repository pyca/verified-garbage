module

public import VerifiedGarbage.Impl.Rsa.X86_64.Keys

/-! # The RSA prime search on x86-64

`vg_rsa_prime_search`: calls `vg_rsa_keygen_candidate` on the tape's
successive candidates until one is accepted, the budget of counted
candidates or the tape's entropy runs out, or the tape ends inside a
candidate (`VG.Spec.RsaKeyGen.primeSearch`). Its working state is in a
frame of its own: the state the caller gives it holds only the four public
words, which it reads at its entry and writes back at its exit.
-/

@[expose] public section

namespace VG.Impl.RsaKeyGen.X86_64.Search

open VG VG.X86_64 VG.Impl.Bignum.X86_64

/-- The frame: the four public words (counted candidates left, the prime's
width, the entropy budget, the request); the caller's r12; the candidate's
eleven arguments, with the tape's current pointer and length; the octets
consumed; the status (4 while the search goes on); the state's pointer. -/
def field (j : Nat) : MemOp := { base := .r12, disp := (8 * j : Nat) }

/-- The frame's size: 20 words. -/
def frameBytes : Nat := 160

/-- The caller's stack argument `k`, above the frame and the return address. -/
def callerArg (k : Nat) : MemOp := { base := .rsp, disp := (frameBytes + 8 + 8 * k : Nat) }

def entryHead : List Instr := [
  .store { base := .rsp, disp := 32 } .r12, .mov .r12 (.reg .rsp),
  .store (field 5) .rdi, .store (field 6) .rsi, .store (field 7) .rdx,
  .store (field 8) .rcx, .store (field 9) .r8, .store (field 10) .r9]

def entryArgs : List Instr := [
  .mov .rax (.mem (callerArg 0)), .store (field 11) .rax,
  .mov .rax (.mem (callerArg 1)), .store (field 12) .rax,
  .mov .rax (.mem (callerArg 2)), .store (field 13) .rax,
  .mov .rax (.mem (callerArg 3)), .store (field 14) .rax,
  .mov .rax (.mem (callerArg 4)), .store (field 15) .rax,
  .mov .rax (.mem (callerArg 5)), .store (field 18) .rax]

/-- The public words: the state's first, then `out_len` and
`primeEntropy out_len = 32769 out_len`, which the precondition says the
state holds; no request yet, and nothing consumed. -/
def entryWords : List Instr := [
  .mov .rcx (.mem { base := .rax }), .store (field 0) .rcx, .store (field 1) .rsi,
  .mov .rcx (.reg .rsi), .shift .shl .rcx 15, .alu .add .rcx (.reg .rsi), .store (field 2) .rcx,
  .mov32 .rax (.imm 0), .store (field 3) .rax, .store (field 16) .rax]

def entry : List Instr := entryHead ++ entryArgs ++ entryWords

/-- The candidate's arguments, for the rest of the tape: its stack
arguments at the 40 octets the call's frame allocates. -/
def arguments : List Instr := [
  .mov .rdi (.mem (field 5)), .mov .rsi (.mem (field 6)), .mov .rdx (.mem (field 7)),
  .mov .rcx (.mem (field 8)), .mov .r8 (.mem (field 9)), .mov .r9 (.mem (field 10)),
  .mov .rax (.mem (field 11)), .store { base := .rsp } .rax,
  .mov .rax (.mem (field 12)), .store { base := .rsp, disp := 8 } .rax,
  .mov .rax (.mem (field 13)), .store { base := .rsp, disp := 16 } .rax,
  .mov .rax (.mem (field 14)), .store { base := .rsp, disp := 24 } .rax,
  .mov .rax (.mem (field 15)), .store { base := .rsp, disp := 32 } .rax]

/-- No more candidates and no request, with `status`. -/
def terminal (status : Nat) : List Instr := [
  .mov32 .rax (.imm 0), .store (field 0) .rax, .store (field 3) .rax,
  .mov32 .rax (.imm (BitVec.ofNat 32 status)), .store (field 17) .rax]

/-- Exhausted: zeros at `out`, which no candidate may have written. -/
def exhausted : Prog isa := .seq (.block (terminal 3 ++ [.mov .rdi (.reg .r12)]))
  (VG.Impl.Rsa.X86_64.Keys.zeroOut 5 6)

/-- The octets the candidate consumed, from `used`, in rcx. -/
def loadUsed : List Instr := [.mov .rcx (.mem (field 7)), .mov .rcx (.mem { base := .rcx })]

/-- The prime: its candidate's octets consumed. -/
def accept : List Instr := loadUsed ++ [
  .mov .rax (.mem (field 16)), .alu .add .rax (.reg .rcx), .store (field 16) .rax] ++ terminal 1

/-- Past a rejected candidate (rcx octets, status in rdx): the tape and the
octets consumed advance, and a counted rejection (status 3) takes one
candidate from the budget. -/
def advance : List Instr := [
  .mov .rax (.mem (field 12)), .alu .add .rax (.reg .rcx), .store (field 12) .rax,
  .mov .rax (.mem (field 13)), .alu .sub .rax (.reg .rcx), .store (field 13) .rax,
  .mov .rax (.mem (field 16)), .alu .add .rax (.reg .rcx), .store (field 16) .rax,
  .mov32 .rax (.imm 4), .store (field 17) .rax]

def count : List Instr := [.mov .rax (.mem (field 0)), .alu .sub .rax (.imm 1), .store (field 0) .rax]

/-- A candidate rejected, too close (2) or otherwise (3), in rdx; one that
consumed nothing (which no valid width allows) exhausts the search, as the
specification's progress check does. -/
def reject : Prog isa := .seq (.block ([.mov .rdx (.reg .rax)] ++ loadUsed ++ [.alu .test .rcx (.reg .rcx)]))
  (.ite .e exhausted (.seq (.block (advance ++ [.alu .cmp .rdx (.imm 2)]))
    (.ite .e (.block []) (.block count))))

/-- The next tape's length, `primeRequest`: twice the larger of the octets
left and 16 per octet of the prime, at most the entropy budget. -/
def request : List Instr := [
  .mov .rcx (.mem (field 1)), .shift .shl .rcx 4, .alu .cmp .rax (.reg .rcx),
  .cmov .b .rax (.reg .rcx),
  .shift .shl .rax 1, .mov .rcx (.mem (field 2)), .alu .cmp .rax (.reg .rcx),
  .cmov .ae .rax (.reg .rcx), .store (field 3) .rax,
  .mov32 .rax (.imm 0), .store (field 17) .rax]

/-- The tape ended inside a candidate: ask for more, unless the candidate
already had the whole budget. The candidate wrote zeros at `out`. -/
def short : Prog isa := .seq
  (.block [.mov .rax (.mem (field 13)), .alu .cmp .rax (.mem (field 2))])
  (.ite .ae exhausted (.block request))

def classify : Prog isa := .seq (.block [.mov32 .rax (.reg .rax), .alu .cmp .rax (.imm 1)])
  (.ite .e (.block accept) (.seq (.block [.alu .test .rax (.reg .rax)])
    (.ite .e short reject)))

variable (candidate : Prog isa)

/-- The candidate, a call of `vg_rsa_keygen_candidate`, in a frame of its
stack arguments. -/
def candidateRun : Prog isa := .frame (.alloc 40)
  (.seq (.block arguments) candidate) (.free 40)

def iteration : Prog isa := seqs [
  .block [.mov .rax (.mem (field 0)), .alu .test .rax (.reg .rax)],
  .ite .e exhausted (.seq (candidateRun candidate) classify),
  .block [.mov .rax (.mem (field 17)), .alu .cmp .rax (.imm 4)]]

/-- The public words back to the state, the octets consumed to `used`, the
status returned and r12 restored. -/
def finish : List Instr := [
  .mov .rax (.mem (field 18)),
  .mov .rcx (.mem (field 0)), .store { base := .rax } .rcx,
  .mov .rcx (.mem (field 1)), .store { base := .rax, disp := 8 } .rcx,
  .mov .rcx (.mem (field 2)), .store { base := .rax, disp := 16 } .rcx,
  .mov .rcx (.mem (field 3)), .store { base := .rax, disp := 24 } .rcx,
  .mov .rdx (.mem (field 7)), .mov .rcx (.mem (field 16)), .store { base := .rdx } .rcx,
  .mov .rax (.mem (field 17)), .mov .r12 (.mem (field 4))]

def code : Prog isa := .frame (.alloc frameBytes)
  (seqs [.block entry, .loop (iteration candidate) .e, .block finish]) (.free frameBytes)

end VG.Impl.RsaKeyGen.X86_64.Search
