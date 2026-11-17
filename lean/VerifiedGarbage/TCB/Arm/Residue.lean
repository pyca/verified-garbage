module

public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.TCB.Artifact

/-!
# Returning without secret residue (32-bit ARM)

**Trusted.** What it means for a function to leave no secret where its Rust
caller cannot clear it, as on x86-64 (`TCB/X86_64/Residue.lean`). The caller
owns its buffers (Rust objects, which it wipes itself, `src/zeroize.rs`) and
the result; it cannot reach what the function leaves in registers, in the
condition flags, or in the stack below its stack pointer, where the
function's frames were. The same model, and so the same property, serves
A32 and Thumb code.

`NoResidue c k retBits` is a property of two runs, as `ConstantTime` is: any
two runs of `c` from states that satisfy `k.pre`, agree on what `k.pub` says
is public, and agree on everything outside the buffers (`Outside 0`), end in
states that agree on everything outside the buffers but the result
(`Outside retBits`). What the function leaves there is therefore a function
of what its caller left there and of public data, and of nothing else: not
of the contents of its buffers that are not public. It is the same whether
the function clears a location or leaves in it what was there on entry, so
no choice of what to keep (zero, or the entry value) can carry a secret.

`Outside` names every register the model has, not only the ones a callee
may change. AAPCS §6.1.1 ("Core registers") makes `r0`–`r3` (the argument,
result and scratch registers) and `r12` (IP, the intra-procedure-call
scratch register) caller-saved, and the condition flags N, Z, C and V need
not be preserved (§6.1.3, "Processor Status Register"): these are where a
secret can be left. The callee-saved registers (`r4`–`r11`, `lr`, which
holds the return address, and `sp`) are what they were on entry
(`abiPreserved`), so the two runs agree on them anyway. A result of up to 64
bits is `r1 ++ r0`, the low word in `r0` (§6.4, "Result Return"), whose low
`retBits` bits only may differ: all of `r1` agrees for a result of 32 bits or
fewer. See https://github.com/ARM-software/abi-aa/blob/2025Q4/aapcs32/aapcs32.rst.

What was there on entry (all of the registers, and the memory outside the
buffers) is taken as given: a secret the caller passed in a register, or
left in one, is the caller's. So are the return addresses the code's calls
leave in `lr`, and what a linker veneer may leave in `r12` and the flags
(`State.unknowns`), which the two runs share: they are where the code is,
not data.

Not covered, because the model does not have them: the floating-point and
SIMD registers and the flags other than N, Z, C and V (which no modelled
instruction changes, see `TCB/Arm/Target.lean`), and microarchitectural
state.
-/

@[expose] public section

namespace VG.Arm

/-- Two states agree on everything outside the buffers: on which regions
the code may read and write, every core register (but the low `retBits`
bits of the result, `r1 ++ r0`), the stack pointer, the condition flags,
and every byte of memory outside those regions. -/
def Outside (retBits : Nat) (s₁ s₂ : State) : Prop :=
  s₁.rd = s₂.rd ∧ s₁.wr = s₂.wr ∧
  (∀ r, r ≠ .r0 → r ≠ .r1 → s₁.gpr r = s₂.gpr r) ∧
  (s₁.gpr .r1 ++ s₁.gpr .r0) >>> retBits = (s₂.gpr .r1 ++ s₂.gpr .r0) >>> retBits ∧
  s₁.sp = s₂.sp ∧
  s₁.n = s₂.n ∧ s₁.z = s₂.z ∧ s₁.c = s₂.c ∧ s₁.v = s₂.v ∧
  ∀ x, (∀ r ∈ s₁.rd ++ s₁.wr, ¬ r.Contains x 1) → s₁.mem x = s₂.mem x

/-- `c`, with contract `k` and a result of `retBits` bits, returns without
secret residue (see the module docs). -/
def NoResidue (c : Prog isa) (k : Contract isa) (retBits : Nat) : Prop :=
  ∀ s₁ s₂ t₁ t₂ s₁' s₂', k.pre s₁ → k.pre s₂ → k.pub s₁ s₂ → Outside 0 s₁ s₂ →
    s₁.unknowns = s₂.unknowns →
    Exec isa c s₁ t₁ s₁' → Exec isa c s₂ t₂ s₂' → Outside retBits s₁' s₂'

end VG.Arm
