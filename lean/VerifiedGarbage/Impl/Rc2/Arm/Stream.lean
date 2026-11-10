module

public import VerifiedGarbage.Impl.Rc2.Arm.ExpandKey

/-! # Streaming RC2-CBC on ARMv7

`vg_rc2_cbc_init(key = r0, key_len = r1, effective_bits = r2, iv = r3,
iv_len = [sp], ctx = [sp + 4], scratch = [sp + 8])` checks the lengths,
returning 1, 2 or 3 for the first that is invalid, copies the IV to
`ctx + 128` and calls `vg_rc2_expand_key(key, key_len, effective_bits,
ctx, scratch)` to write the schedule to `ctx`, and returns 0.

Only caller-saved registers are used. The key expansion takes its scratch
buffer on the stack: a frame pushes it (`push {r12, lr}`, the buffer in `r12`
at `[sp]`) around the call, so the function uses 8 bytes of stack. The return
address `lr`, which the code uses as a working register, is kept across the
call at `scratch + 512`, after the callee's 512 bytes of working space.
Every branch and address depends only on the pointers and lengths.
-/

@[expose] public section

namespace VG.Impl.Rc2.Arm.Stream

open VG.Arm

/-- `lr` to `scratch + 512`. -/
def saveLr : List Instr := [.ldrSp .r12 8, .str .lr .r12 512]

/-- `lr` back from `scratch + 512`. -/
def restoreLr : List Instr := [.ldrSp .r12 8, .ldr .lr .r12 512]

/-! ## `init` -/

def keyCall : Prog isa :=
  .frame (.push [.r12, .lr]) (.call "vg_rc2_expand_key" expandKey) (.pop .r12 8)

/-- The IV to `ctx + 128`, and the arguments of `vg_rc2_expand_key`:
`schedule = ctx` in `r3`, `scratch` in `r12`. -/
def initArgs : List Instr :=
  saveLr ++ ([.ldr .lr .r3 0, .ldr .r3 .r3 4, .ldrSp .r12 4, .str .lr .r12 128, .str .r3 .r12 132,
    .mov .r3 (.reg .r12), .ldrSp .r12 8] : List Instr)

def initBody : Prog isa :=
  .seq (.block initArgs) (.seq keyCall (.block (restoreLr ++ ([.mov .r0 (.imm 0)] : List Instr))))

/-- `Z` is clear unless `key_len` is in 1..=128 (`(key_len - 1) >> 7 = 0`). -/
def checkKey : List Instr :=
  [.dp .sub .r12 .r1 (.imm 1), .mov .r12 (.shifted .r12 .lsr 7), .cmp .r12 (.imm 0)]

/-- `Z` is clear unless `effective_bits` is in 1..=1024. -/
def checkBits : List Instr :=
  [.dp .sub .r12 .r2 (.imm 1), .mov .r12 (.shifted .r12 .lsr 10), .cmp .r12 (.imm 0)]

/-- `Z` is clear unless `iv_len` is 8. -/
def checkIv : List Instr := [.ldrSp .r12 0, .cmp .r12 (.imm 8)]

/-- The checks: `r0` is the error code of the first that fails, and `Z` is
set if none does. -/
def checks : Prog isa :=
  .seq (.block checkKey) (.ite .ne (.block [.mov .r0 (.imm 1)])
    (.seq (.block checkBits) (.ite .ne (.block [.mov .r0 (.imm 2)])
      (.seq (.block checkIv) (.ite .ne (.block [.mov .r0 (.imm 3)]) (.block []))))))

def init : Prog isa :=
  .seq checks (.ite .ne (.block []) initBody)

end VG.Impl.Rc2.Arm.Stream
