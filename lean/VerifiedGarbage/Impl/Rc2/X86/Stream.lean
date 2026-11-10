module

public import VerifiedGarbage.Impl.Rc2.X86.ExpandKey

/-! # Streaming RC2-CBC on baseline x86

Every argument is on the stack (cdecl), argument `i` at `[esp + 4 + 4i]`.

`vg_rc2_cbc_init(key, key_len, effective_bits, iv, iv_len, ctx, scratch)`
checks the lengths, leaving in `eax` 1, 2 or 3 for the first that is
invalid, or 0. If they are valid, it copies the IV to `ctx + 128` and calls
`vg_rc2_expand_key(key, key_len, effective_bits, ctx, scratch)` to write the
schedule to `ctx`, and returns 0.

The call pushes its five arguments in a frame of their own (`scratch` =
`ebx`, then `esi`, `edx`, `ecx`, `eax`), popped (into `eax`) when it
returns, so `ebx` and `esi` hold arguments: our caller's values of them are
saved in `scratch[512..520)`, beyond the callee's scratch space, and
restored after the call through `ebx`, which the callee preserves. Every
branch and address depends only on `esp`, the pointers and the lengths.
-/

@[expose] public section

namespace VG.Impl.Rc2.X86.Stream

open VG.X86

/-- Argument `i`, `[esp + 4 + 4i]`. -/
def argOp (i : Nat) : MemOp := memOp .esp (4 + 4 * i)

/-- Saves our caller's `ebx` and `esi` in `scratch[512..520)`, with `scratch` in `eax`. -/
def save : List Instr :=
  [.mov .eax (.mem (argOp 6)), .store (memOp .eax 512) .ebx, .store (memOp .eax 516) .esi]

/-- Restores them, with `scratch` in `ebx`. -/
def restore : List Instr :=
  [.mov .esi (.mem (memOp .ebx 516)), .mov .ebx (.mem (memOp .ebx 512))]

/-- A call with the arguments `eax`, `ecx`, `edx`, `esi`, `ebx`. -/
def call5 (name : String) (code : Prog isa) : Prog isa :=
  .frame (.push [.ebx, .esi, .edx, .ecx, .eax]) (.call name code) (.pop .eax 5)

/-! ## `init` -/

/-- 1 unless `key_len` is in 1..=128 (CF clear: `key_len - 1 ≥ 128`). -/
def checkKey : List Instr :=
  [imm .eax 1, .mov .ecx (.mem (argOp 1)), .alu .sub .ecx (.imm 1), .alu .cmp .ecx (.imm 128)]

/-- 2 unless `effective_bits` is in 1..=1024. -/
def checkBits : List Instr :=
  [imm .eax 2, .mov .ecx (.mem (argOp 2)), .alu .sub .ecx (.imm 1), .alu .cmp .ecx (.imm 1024)]

/-- 3 unless `iv_len` is 8. -/
def checkIv : List Instr := [imm .eax 3, .mov .ecx (.mem (argOp 4)), .alu .cmp .ecx (.imm 8)]

/-- `eax` := the error code, or 0. -/
def checks : Prog isa :=
  .seq (.block checkKey) (.ite .ae (.block [])
    (.seq (.block checkBits) (.ite .ae (.block [])
      (.seq (.block checkIv) (.ite .ne (.block []) (.block [imm .eax 0]))))))

/-- The IV to `ctx + 128`, our caller's registers saved, and the arguments of
`vg_rc2_expand_key(key, key_len, effective_bits, ctx, scratch)`. -/
def initArgs : List Instr :=
  ([.mov .eax (.mem (argOp 3)), .mov .ecx (.mem (argOp 5)), .mov .edx (.mem (memOp .eax 0)),
   .store (memOp .ecx 128) .edx, .mov .edx (.mem (memOp .eax 4)), .store (memOp .ecx 132) .edx] : List Instr) ++
  save ++
  [rr .ebx .eax, rr .esi .ecx, .mov .edx (.mem (argOp 2)), .mov .ecx (.mem (argOp 1)),
   .mov .eax (.mem (argOp 0))]

def keyCall : Prog isa := call5 "vg_rc2_expand_key" expandKey

def initBody : Prog isa :=
  .seq (.block initArgs) (.seq keyCall (.block (restore ++ [imm .eax 0])))

def init : Prog isa :=
  .seq checks (.seq (.block [.alu .test .eax (.reg .eax)]) (.ite .ne (.block []) initBody))

end VG.Impl.Rc2.X86.Stream
