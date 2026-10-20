module
public import VerifiedGarbage.Impl.Rsa.X86_64.Keys


/-! # The complete native FFDH parameter-search controller

The first four state words are persistent policy; the rest are private
workspace. A loop consumes rejected candidates without returning to Rust.
Only a genuine entropy request, success, or exhaustion returns to the host.
-/

@[expose] public section

namespace VG.Impl.Ffdh.X86_64.Generation.Search

open VG VG.X86_64 VG.Impl.Bignum.X86_64

/-- Controller slots: remaining attempts, width, entropy cap, request; saved
r12; original ABI inputs; current tape pointer/length; total consumed; status. -/
def field (j : Nat) : MemOp := { base := .r12, disp := (8 * j : Nat) }

def entryHead : List Instr := [
  .mov32 .r8 (.reg .r8), .mov .rax (.mem { base := .rsp, disp := 32 }),
  .store { base := .rax, disp := 32 } .r12,
  .mov .r12 (.reg .rax), .store (field 5) .rdi, .store (field 6) .rsi,
  .store (field 7) .rdx, .store (field 8) .rcx, .store (field 9) .r8,
  .store (field 10) .r9]

def entryTail : List Instr := [
  .mov .r10 (.mem { base := .rsp, disp := 8 }),
  .mov .r11 (.mem { base := .rsp, disp := 16 }),
  .mov .rax (.mem { base := .rsp, disp := 24 }),
  .store (field 11) .r10, .store (field 13) .r11, .store (field 15) .rax,
  .mov32 .rax (.imm 0), .store (field 12) .rax]

def entry : List Instr := entryHead ++ entryTail

def arguments : List Instr := [
  .mov .rdi (.mem (field 5)), .mov .rsi (.mem (field 6)), .mov .rdx (.mem (field 7)),
  .mov .rcx (.mem (field 8)), .mov .r8 (.mem (field 9)), .mov .r9 (.mem (field 10)),
  .mov .rax (.mem (field 11)), .mov .r10 (.mem (field 13)), .mov .r11 (.mem (field 15)),
  .store { base := .rsp, disp := 8 } .rax, .store { base := .rsp, disp := 16 } .r10,
  .store { base := .rsp, disp := 24 } .r11]

/-- Zero policy counters and finish with the selected terminal status. -/
def terminal (status : Nat) : List Instr := [
  .mov32 .rax (.imm 0), .store (field 0) .rax, .store (field 3) .rax,
  .mov32 .rax (.imm (BitVec.ofNat 32 status)), .store (field 14) .rax]

def exhausted : Prog isa := .seq (.block (terminal 3 ++ [.mov .rdi (.reg .r12)]))
  (VG.Impl.Rsa.X86_64.Keys.zeroOut 5 6)

/-- Advance the byte stream and decrement the attempt count inside native code. -/
def reject : List Instr := [
  .mov .rax (.mem (field 7)), .mov .rcx (.mem { base := .rax }),
  .mov .rax (.mem (field 12)), .alu .add .rax (.reg .rcx), .store (field 12) .rax,
  .mov .rax (.mem (field 10)), .alu .add .rax (.reg .rcx), .store (field 10) .rax,
  .mov .rax (.mem (field 11)), .alu .sub .rax (.reg .rcx), .store (field 11) .rax,
  .mov .rax (.mem (field 0)), .alu .sub .rax (.imm 1), .store (field 0) .rax,
  .mov32 .rax (.imm 4), .store (field 14) .rax]

/-- Success consumes the final candidate's prefix and marks the controller done. -/
def accept : List Instr := [
  .mov .rax (.mem (field 7)), .mov .rcx (.mem { base := .rax }),
  .mov .rax (.mem (field 12)), .alu .add .rax (.reg .rcx), .store (field 12) .rax] ++ terminal 1

/-- The host receives the exact next length, `parameterRequest`: twice the larger of
the octets left and 256 per octet of p, at most the entropy cap. It owns no
entropy-limit policy. -/
def request : List Instr := [
  .mov .rcx (.mem (field 1)), .shift .shl .rcx 8, .alu .cmp .rax (.reg .rcx),
  .cmov .b .rax (.reg .rcx),
  .shift .shl .rax 1, .mov .rcx (.mem (field 2)), .alu .cmp .rax (.reg .rcx),
  .cmov .ae .rax (.reg .rcx), .store (field 3) .rax,
  .mov32 .rax (.imm 0), .store (field 14) .rax]

def short : Prog isa := .seq
  (.block [.mov .rax (.mem (field 11)), .alu .cmp .rax (.mem (field 2))])
  (.ite .ae exhausted (.block request))

def classify : Prog isa := .seq (.block [.mov32 .rax (.reg .rax), .alu .cmp .rax (.imm 1)])
  (.ite .e (.block accept) (.seq (.block [.alu .cmp .rax (.imm 2)])
    (.ite .e (.block reject) short)))

variable (candidate : Prog isa)

def candidateRun : Prog isa := .frame (.alloc 32)
  (.seq (.block arguments) candidate) (.free 32)

def iteration : Prog isa := seqs [
  .block [.mov .rax (.mem (field 0)), .alu .test .rax (.reg .rax)],
  .ite .e exhausted (.seq (candidateRun candidate) classify),
  .block [.mov .rax (.mem (field 14)), .alu .cmp .rax (.imm 4)]]

def finish : List Instr := [
  .mov .rdx (.mem (field 7)), .mov .rcx (.mem (field 12)),
  .mov .rax (.mem (field 14)), .mov .r12 (.mem (field 4)), .store { base := .rdx } .rcx]

def code : Prog isa := seqs [.block entry, .loop (iteration candidate) .e, .block finish]

end VG.Impl.Ffdh.X86_64.Generation.Search
