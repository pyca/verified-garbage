module

public import VerifiedGarbage.TCB.X86_64.Isa

/-!
# Entering Intel's MXCSR mitigation of MCDT on x86-64

`vg_mcdt_enter` returns 1 at once if MXCSR holds `0x1FBF`, as it does after
any earlier call on the thread; otherwise it sets MXCSR's six status flags,
keeping its control bits, then `lfence` (see "MCDT" in
`TCB/X86_64/Isa.lean`), and returns 1 if MXCSR then holds `0x1FBF`, 0 if
not. Its contract makes MXCSR public (`Spec/Mcdt.lean`), so it may branch on
it. A frame pushes `rax` for a slot, the operand of `stmxcsr` and
`ldmxcsr`, and pops it into `rcx`:

```
push rax
mov eax, 0; mov [rsp], rax
stmxcsr [rsp]; mov eax, [rsp]; mov edx, eax; cmp edx, 0x1FBF
if equal:
  mov eax, 1
else:
  and eax, 0xFFFF; or eax, 0x3F; mov [rsp], eax; ldmxcsr [rsp]; lfence
  xor eax, 0x1FBF; mov eax, 1; mov edx, 0; cmovne rax, rdx
pop rcx
```

The slot is zeroed first: the push copied the caller's `rax` to it, which
may be secret, and the 4 bytes `stmxcsr` does not write would keep half of
it. The `and` clears MXCSR's reserved bits (31:16), as code that loads MXCSR
from a saved value does (see `TCB/X86_64/Isa.lean`). The slow path's result
is computed without a branch: `xor` sets ZF exactly when MXCSR is `0x1FBF`,
and neither `mov` changes the flags.
-/

@[expose] public section

namespace VG.Impl.Mcdt.X86_64

open VG.X86_64

/-- `[rsp]`. -/
def slot : MemOp := { base := .rsp }

/-- The slot zeroed, MXCSR to `eax` through it, and a copy of it in `edx` compared with
`0x1FBF` (comparing `eax` itself would drop what `RScrub.Mx.mx` knows of it). -/
def head : List Instr :=
  [.mov32 .rax (.imm 0), .store slot .rax, .stmxcsr slot, .mov32 .rax (.mem slot), .mov32 .rdx (.reg .rax),
    .alu32 .cmp .rdx (.imm 0x1FBF)]

/-- From MXCSR in `eax`: its status flags set, but for its reserved bits, and
`lfence`. -/
def raise : List Instr :=
  [.alu32 .and .rax (.imm 0xFFFF), .alu32 .or .rax (.imm 0x3F), .store32 slot .rax, .ldmxcsr slot,
    .lfence]

/-- 1 in `rax` if `eax` is `0x1FBF`, 0 if not. -/
def answer : List Instr :=
  [.alu32 .xor .rax (.imm 0x1FBF), .mov32 .rax (.imm 1), .mov32 .rdx (.imm 0),
    .cmov .ne .rax (.reg .rdx)]

/-- The frame's body: `head`, then 1 if MXCSR was `0x1FBF`, else `raise` and
`answer`. -/
def body : Prog isa :=
  .seq (.block head) (.ite .e (.block [.mov32 .rax (.imm 1)]) (.block (raise ++ answer)))

/-- `vg_mcdt_enter`. -/
def enter : Prog isa := .frame (.push [.rax]) body (.pop .rcx 1)

end VG.Impl.Mcdt.X86_64
