module

public import VerifiedGarbage.Impl.Rc2.X86_64.ExpandKey

/-! # Streaming RC2-CBC on baseline x86-64

`vg_rc2_cbc_init(key = rdi, key_len = rsi, effective_bits = rdx, iv = rcx,
iv_len = r8, ctx = r9, scratch = [rsp + 8])` checks the lengths, returning
1, 2 or 3 for the first that is invalid; otherwise it copies the IV to `ctx + 128` and
calls `vg_rc2_expand_key` to write the schedule to `ctx`, and returns 0.

Nothing is kept across the call, which is last, so only caller-saved
registers are used. Every branch and address depends only on the pointers
and lengths; the scratch pointer is loaded last before the call.
-/

@[expose] public section

namespace VG.Impl.Rc2.X86_64.Stream

open VG.X86_64

/-! ## `init` -/

def keyCall : Prog isa := .call "vg_rc2_expand_key" expandKey

/-- The IV to `ctx + 128`, and the arguments of `vg_rc2_expand_key`:
`schedule = ctx`, `scratch` from the stack. -/
def initArgs : List Instr :=
  [.mov .rax (.mem (memOp .rcx 0)), .store (memOp .r9 128) .rax, rr .rcx .r9,
   .mov .r8 (.mem (memOp .rsp 8))]

def initBody : Prog isa :=
  .seq (.block initArgs) (.seq keyCall (.block [.mov32 .rax (.imm 0)]))

/-- 1 unless `key_len` is in 1..=128 (CF clear: `key_len - 1 ≥ 128`). -/
def checkKey : List Instr :=
  [.mov32 .rax (.imm 1), rr .r10 .rsi, .alu .sub .r10 (.imm 1), .alu .cmp .r10 (.imm 128)]

/-- 2 unless `effective_bits` is in 1..=1024. -/
def checkBits : List Instr :=
  [.mov32 .rax (.imm 2), rr .r10 .rdx, .alu .sub .r10 (.imm 1), .alu .cmp .r10 (.imm 1024)]

/-- 3 unless `iv_len` is 8. -/
def checkIv : List Instr := [.mov32 .rax (.imm 3), .alu .cmp .r8 (.imm 8)]

/-- The return code in `rax`: 1, 2 or 3 for the first invalid length, else 0;
then ZF is set iff it is 0. -/
def checks : Prog isa :=
  .seq (.seq (.block checkKey) (.ite .ae (.block [])
    (.seq (.block checkBits) (.ite .ae (.block [])
      (.seq (.block checkIv) (.ite .ne (.block []) (.block [.mov32 .rax (.imm 0)])))))))
    (.block [.alu .test .rax (.reg .rax)])

def init : Prog isa := .seq checks (.ite .ne (.block []) initBody)

end VG.Impl.Rc2.X86_64.Stream
