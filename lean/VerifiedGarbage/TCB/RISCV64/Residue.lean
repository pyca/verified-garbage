module

public import VerifiedGarbage.TCB.RISCV64.Isa
public import VerifiedGarbage.TCB.Artifact

/-!
# Returning without secret residue (64-bit RISC-V)

**Trusted.** What it means for a function to leave no secret where its Rust
caller cannot clear it, as on x86-64 (`TCB/X86_64/Residue.lean`). The caller
owns its buffers (Rust objects, which it wipes itself, `src/zeroize.rs`) and
the result; it cannot reach what the function leaves in registers or in the
stack below its stack pointer, where the function's frames were. RISC-V has
no condition flags.

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
may change. The psABI's "Integer Register Convention" (RISC-V ABIs
Specification, Version 1.0, "RISC-V Calling Conventions") makes `a0`–`a7`
(the argument and result registers) and `t0`–`t6` (temporaries) not
preserved across calls: these are where a secret can be left. The preserved
registers (`s0`–`s11` and `sp`), and `ra`, which holds the return address,
are what they were on entry (`abiPreserved`), so the two runs agree on them
anyway. The integer result is in `a0` ("Values are returned in the same
manner as a first named argument of the same type would be passed"), whose
low `retBits` bits only may differ.

What was there on entry (all of the registers, and the memory outside the
buffers) is taken as given: a secret the caller passed in a register, or
left in one, is the caller's. So are the return addresses the code's calls
leave in `ra`, and what a PLT entry may leave in `t0`–`t6`
(`State.unknowns`), which the two runs share: they are where the code is,
not data.

Not covered, because the model does not have them: `gp` and `tp` (which no
modelled instruction changes), the floating-point and vector registers and
the CSRs (which no modelled instruction changes, see
`TCB/RISCV64/Target.lean`), and microarchitectural state.
-/

@[expose] public section

namespace VG.RISCV64

/-- Two states agree on everything outside the buffers: on which regions
the code may read and write, every integer register (but the low `retBits`
bits of `a0`, the result), the stack pointer, and every byte of memory
outside those regions. -/
def Outside (retBits : Nat) (s₁ s₂ : State) : Prop :=
  s₁.rd = s₂.rd ∧ s₁.wr = s₂.wr ∧
  (∀ r, r ≠ .a0 → s₁.gpr r = s₂.gpr r) ∧
  s₁.gpr .a0 >>> retBits = s₂.gpr .a0 >>> retBits ∧
  s₁.sp = s₂.sp ∧
  ∀ x, (∀ r ∈ s₁.rd ++ s₁.wr, ¬ r.Contains x 1) → s₁.mem x = s₂.mem x

/-- `c`, with contract `k` and a result of `retBits` bits, returns without
secret residue (see the module docs). -/
def NoResidue (c : Prog isa) (k : Contract isa) (retBits : Nat) : Prop :=
  ∀ s₁ s₂ t₁ t₂ s₁' s₂', k.pre s₁ → k.pre s₂ → k.pub s₁ s₂ → Outside 0 s₁ s₂ →
    s₁.unknowns = s₂.unknowns →
    Exec isa c s₁ t₁ s₁' → Exec isa c s₂ t₂ s₂' → Outside retBits s₁' s₂'

end VG.RISCV64
