module

public import VerifiedGarbage.Impl.Ffdh.X86_64.GenerateKey

/-! # Complete native private-key generation control

Both retry counters live in native state. A return of zero asks only for
more entropy; range rejection and degenerate-public-value rejection never
return to Rust. Rejected random scalars remain secret under the key contract.
-/

@[expose] public section

namespace VG.Impl.Ffdh.X86_64.Generation.KeySearch

open VG VG.X86_64 VG.Impl.Bignum.X86_64

def field (j : Nat) : MemOp := { base := .r12, disp := (8 * j : Nat) }

/-- Persistent words: key attempts, scalar attempts, byte width, request.
Other words retain ABI arguments and the current tape position. -/
def entryHead : List Instr := [
  .mov .rax (.mem { base := .rsp, disp := 48 }), .store { base := .rax, disp := 32 } .r12,
  .mov .r12 (.reg .rax), .store (field 5) .rdi, .store (field 6) .rsi,
  .store (field 7) .rdx, .store (field 8) .rcx, .store (field 9) .r8,
  .store (field 10) .r9]

def entryTail : List Instr := [
  .mov .r10 (.mem { base := .rsp, disp := 16 }),
  .mov .r11 (.mem { base := .rsp, disp := 24 }),
  .mov .rcx (.mem { base := .rsp, disp := 32 }),
  .mov .rax (.mem { base := .rsp, disp := 40 }),
  .store (field 11) .r10, .store (field 12) .r11,
  .store (field 3) .rcx, .store (field 15) .rax,
  .mov32 .rax (.imm 0), .store (field 13) .rax]

def entry : List Instr := entryHead ++ entryTail

def arguments : List Instr := [
  .mov .rdi (.mem (field 5)), .mov .rsi (.mem (field 6)), .mov .rdx (.mem (field 7)),
  .mov .rcx (.mem (field 8)), .mov .r8 (.mem (field 9)), .mov .r9 (.mem (field 10)),
  .mov .rax (.mem (field 11)), .store { base := .rsp, disp := 16 } .rax,
  .mov .rax (.mem (field 2)), .store { base := .rsp, disp := 8 } .rax, .store { base := .rsp, disp := 24 } .rax,
  .mov .rax (.mem (field 3)), .store { base := .rsp, disp := 32 } .rax,
  .mov .rax (.mem (field 15)), .store { base := .rsp, disp := 40 } .rax]

def terminal (status : Nat) : List Instr := [
  .mov32 .rax (.imm 0), .store (field 0) .rax, .store (field 1) .rax, .store (field 3) .rax,
  .mov32 .rax (.imm (BitVec.ofNat 32 status)), .store (field 14) .rax]

def exhausted : Prog isa := seqs [
  .block (terminal 3 ++ [.mov .rdi (.reg .r12)]),
  VG.Impl.Rsa.X86_64.Keys.zeroOut 5 6, VG.Impl.Rsa.X86_64.Keys.zeroOut 7 8]

/-- Consume one full-width scalar draw while keeping the attempt's status. -/
def advance : List Instr := [
  .mov .rcx (.mem (field 2)), .mov .rdx (.mem (field 11)),
  .alu .add .rdx (.reg .rcx), .store (field 11) .rdx,
  .mov .rdx (.mem (field 12)), .alu .sub .rdx (.reg .rcx), .store (field 12) .rdx,
  .mov .rdx (.mem (field 13)), .alu .add .rdx (.reg .rcx), .store (field 13) .rdx]

def rejectedScalar : List Instr := [
  .mov .rax (.mem (field 1)), .alu .sub .rax (.imm 1), .store (field 1) .rax,
  .mov32 .rax (.imm 4), .store (field 14) .rax]

def rejectedPublic : List Instr := [
  .mov .rax (.mem (field 0)), .alu .sub .rax (.imm 1), .store (field 0) .rax,
  .mov32 .rax (.imm 128), .store (field 1) .rax,
  .mov32 .rax (.imm 4), .store (field 14) .rax]

def classify : Prog isa := .seq (.block ([.mov32 .rax (.reg .rax)] ++ advance ++ [.alu .cmp .rax (.imm 1)]))
  (.ite .e (.block (terminal 1))
    (.seq (.block [.alu .cmp .rax (.imm 2)])
      (.ite .e (.block rejectedScalar)
        (.seq (.block [.alu .cmp .rax (.imm 3)]) (.ite .e (.block rejectedPublic) exhausted)))))

def request : List Instr := [
  .mov .rax (.mem (field 2)), .store (field 3) .rax,
  .mov32 .rax (.imm 0), .store (field 14) .rax]

variable (attempt : Prog isa)

def attemptRun : Prog isa := .frame (.alloc 48)
  (.seq (.block arguments) attempt) (.free 48)

def attemptOrRequest : Prog isa := .seq
  (.block [.mov .rax (.mem (field 12)), .alu .cmp .rax (.mem (field 2))])
  (.ite .b (seqs [.block (request ++ [.mov .rdi (.reg .r12)]),
    VG.Impl.Rsa.X86_64.Keys.zeroOut 5 6, VG.Impl.Rsa.X86_64.Keys.zeroOut 7 8])
    (.seq (attemptRun attempt) classify))

def iteration : Prog isa := seqs [
  .block [.mov .rax (.mem (field 0)), .alu .test .rax (.reg .rax)],
  .ite .e exhausted (.seq (.block [.mov .rax (.mem (field 1)), .alu .test .rax (.reg .rax)])
    (.ite .e exhausted (attemptOrRequest attempt))),
  .block [.mov .rax (.mem (field 14)), .alu .cmp .rax (.imm 4)]]

def finish : List Instr := [
  .mov .rcx (.mem (field 13)), .store (field 15) .rcx,
  .mov .rax (.mem (field 14)), .mov .r12 (.mem (field 4))]

def code : Prog isa := seqs [
  .block entry, .loop (iteration attempt) .e, .block finish]

end VG.Impl.Ffdh.X86_64.Generation.KeySearch
