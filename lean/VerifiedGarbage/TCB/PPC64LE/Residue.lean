module

public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.TCB.Artifact

/-!
# Returning without secret residue (64-bit little-endian PowerPC)

**Trusted.** What it means for a function to leave no secret where its Rust
caller cannot clear it, as on x86-64 (`TCB/X86_64/Residue.lean`). The caller
owns its buffers (Rust objects, which it wipes itself, `src/zeroize.rs`) and
the result; it cannot reach what the function leaves in registers, in
`XER`'s carry bit, or in the stack below its stack pointer, where the
function's frames were.

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
may change. The ELFv2 ABI (OpenPOWER, Revision 1.5, §2.2.2.1, "Register
Roles", Table 2.21) makes `r0` and `r3`–`r12` (the argument and result
registers, and those of the function linkage), the vector registers
`v0`–`v19` and `XER` (whose carry bit CA the model has) volatile: these are
where a secret can be left. The nonvolatile registers (`r14`–`r31`, `r1`,
the stack pointer, and `r2`, the TOC pointer) and `LR`, which holds the
return address, are what they were on entry (`abiPreserved`), so the two
runs agree on them anyway. The integer result is in `r3` (§2.2.6), whose low
`retBits` bits only may differ.

What was there on entry (all of the registers, and the memory outside the
buffers) is taken as given: a secret the caller passed in a register, or
left in one, is the caller's. So are the return addresses the code's calls
and `adrSym`s leave in `LR` and what linkage code may leave in `r0`, `r11`
and `r12` (`State.unknowns`), which the two runs share: they are where the
code is, not data.

A result the Power ISA leaves undefined, the low doubleword of `mtvsrd XT,
RA`'s target (Book I §3.3.18: "The contents of doubleword element 1 of
VSR[XT] are undefined"), is not taken as given, and is not the same in the
two runs for being undefined: the ISA does not say what an undefined value
may depend on (Book I §1.3.1), so an implementation may leave there a copy
of RA, or what XT held. The model makes it an
unknown function of both (`State.undef`), and the two runs share only the
function (and which execution of `mtvsrd` it is, the function's first
argument, one of the `unknowns`): the processor is the same in both. So
the two runs agree on that doubleword where they agree on RA and on what
XT held, and code that moves a secret with `mtvsrd`, or moves anything
into a register that holds one, must clear both doublewords of the target
before it returns.

Not covered, because the model does not have them: `r13`, the
floating-point registers, `v20`–`v31`, `CTR` and `XER` but CA (which no
modelled instruction changes, see `TCB/PPC64LE/Target.lean`), the condition
register (whose field 0 only the comparisons of branch conditions set, which
constant time makes public), and microarchitectural state.
-/

@[expose] public section

namespace VG.PPC64LE

/-- Two states agree on everything outside the buffers: on which regions
the code may read and write, every general-purpose register (but the low
`retBits` bits of `r3`, the result), every vector register, the link
register, the stack pointer, `XER`'s carry bit, and every byte of memory
outside those regions. -/
def Outside (retBits : Nat) (s₁ s₂ : State) : Prop :=
  s₁.rd = s₂.rd ∧ s₁.wr = s₂.wr ∧
  (∀ r, r ≠ .r3 → s₁.gpr r = s₂.gpr r) ∧
  s₁.gpr .r3 >>> retBits = s₂.gpr .r3 >>> retBits ∧
  s₁.vpr = s₂.vpr ∧ s₁.lr = s₂.lr ∧ s₁.sp = s₂.sp ∧ s₁.ca = s₂.ca ∧
  ∀ x, (∀ r ∈ s₁.rd ++ s₁.wr, ¬ r.Contains x 1) → s₁.mem x = s₂.mem x

/-- `c`, with contract `k` and a result of `retBits` bits, returns without
secret residue (see the module docs). -/
def NoResidue (c : Prog isa) (k : Contract isa) (retBits : Nat) : Prop :=
  ∀ s₁ s₂ t₁ t₂ s₁' s₂', k.pre s₁ → k.pre s₂ → k.pub s₁ s₂ → Outside 0 s₁ s₂ →
    s₁.unknowns = s₂.unknowns → s₁.undef = s₂.undef →
    Exec isa c s₁ t₁ s₁' → Exec isa c s₂ t₂ s₂' → Outside retBits s₁' s₂'

end VG.PPC64LE
