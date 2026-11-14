module

public import VerifiedGarbage.TCB.X86_64.Isa

/-!
# A call inside Intel's MXCSR prologue and epilogue (x86-64)

`mcdtCall n c` calls `c` (named `n`) with MXCSR `0x1FBF`, inside Intel's
sequence for the instructions affected by MXCSR-configuration-dependent
timing (see "MCDT" in `TCB/X86_64/Isa.lean`): one sequence around a whole
computation, whose functions then need none of their own
(`ci/check_mcdt.py` accepts a region's calls of internal functions that run
only inside regions, or never read or write MXCSR).

It saves MXCSR in `rbx`, which `c` keeps (it is callee-saved), so that `c`
may write every other register and memory: a frame pushes `rbx` twice, the
first copy the caller's `rbx`, which its pop reloads last, the second (at
`rsp`) the slot of the sequence's `stmxcsr` and `ldmxcsr`. So:

```
push rbx; push rbx
stmxcsr [rsp]; mov ebx, [rsp]; and ebx, 0xFFFF
mov eax, 0x1FBF; mov [rsp + 4], eax; ldmxcsr [rsp + 4]; lfence
call n
lfence; mov [rsp], ebx; ldmxcsr [rsp]
pop rbx; pop rbx
```

`rax` holds `0x1FBF` when `c` starts, and its result when the sequence
returns. MXCSR is then the caller's but for its reserved bits, which the
`and` clears.
-/

@[expose] public section

namespace VG.Impl.Mcdt.X86_64

open VG.X86_64

/-- `[rsp + d]`. -/
def sp (d : Nat) : MemOp := { base := .rsp, disp := d }

/-- The prologue, in the frame: MXCSR to `rbx` but for its reserved bits,
then `0x1FBF` to MXCSR. -/
def pro : List Instr :=
  [.stmxcsr (sp 0), .mov32 .rbx (.mem (sp 0)), .alu32 .and .rbx (.imm 0xFFFF),
    .mov32 .rax (.imm 0x1FBF), .store32 (sp 4) .rax, .ldmxcsr (sp 4), .lfence]

/-- The epilogue, in the frame: MXCSR from `rbx`. -/
def epi : List Instr := [.lfence, .store32 (sp 0) .rbx, .ldmxcsr (sp 0)]

/-- A call of `c`, named `n`, inside Intel's MXCSR prologue and epilogue. -/
def mcdtCall (n : String) (c : Prog isa) : Prog isa :=
  .frame (.push [.rbx, .rbx]) (.seq (.block pro) (.seq (.call n c) (.block epi))) (.pop .rbx 2)

end VG.Impl.Mcdt.X86_64
