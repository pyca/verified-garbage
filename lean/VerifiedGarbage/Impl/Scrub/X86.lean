module

public import VerifiedGarbage.TCB.X86.Isa
public import VerifiedGarbage.Impl.StackScratch.X86

/-!
# Returning without secret residue (x86, 32-bit)

`scrubF retBits n c` runs `c`, then clears everything `c` may have left
where its Rust caller cannot clear it (`X86.NoResidue`):

* the `n` bytes of stack below `esp` (the stack `c`'s frames and calls use),
  in a frame of them (`wipeBelow`): `mov ecx, 0`, then `mov [esp + 4k], ecx`
  for every doubleword of the frame (`Impl.StackScratch.X86.wipe`);
* the result's bits above its `retBits` low ones (`edx`, or `edx` and `eax`,
  with `mov r, 0`), and the other caller-saved general-purpose register,
  `ecx`, with `xor ecx, ecx`, which also leaves known flags: CF and OF clear,
  ZF set, SF clear (`tail`);
* `xmm0`–`xmm7`, with `pxor x, x`.

`scrub retBits c` is the same without the stack, for code that calls
nothing and has no frame, which writes no stack. The MMX registers, the MMX
mode, MXCSR and the MCDT frames are not cleared: code that has no MMX
instruction leaves the first two as they were, and every run leaves the
others as they were (`Proof/Framework/X86/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.Scrub.X86

open VG.X86

/-- Zero what of the result `edx ++ eax` is above its `rb` bits. -/
def retFix (rb : Nat) : List Instr :=
  if rb = 0 then [.mov .eax (.imm 0), .mov .edx (.imm 0)]
  else if rb ≤ 32 then [.mov .edx (.imm 0)] else []

/-- `pxor x, x` for each of `xmm0`–`xmm7`. -/
def clearXmm : List Instr :=
  [.xop (.bin .pxor .xmm0 .xmm0), .xop (.bin .pxor .xmm1 .xmm1), .xop (.bin .pxor .xmm2 .xmm2),
   .xop (.bin .pxor .xmm3 .xmm3), .xop (.bin .pxor .xmm4 .xmm4), .xop (.bin .pxor .xmm5 .xmm5),
   .xop (.bin .pxor .xmm6 .xmm6), .xop (.bin .pxor .xmm7 .xmm7)]

/-- Set the caller-saved registers, but the result's `rb` bits, and the
flags to constants. -/
def tail (rb : Nat) : List Instr :=
  retFix rb ++ (.alu .xor .ecx (.reg .ecx) :: clearXmm)

/-- `c`, then `tail rb`. -/
def scrub (rb : Nat) (c : Prog isa) : Prog isa := .seq c (.block (tail rb))

/-- Zero the `n` bytes below `esp`, in a frame of them. -/
def wipeBelow (n : Nat) : Prog isa :=
  .frame (.alloc n) (.block (Impl.StackScratch.X86.wipe 0 (n / 4))) (.free n)

/-- `c`, then the `n` bytes below `esp` zeroed, then `tail rb`. -/
def scrubF (rb n : Nat) (c : Prog isa) : Prog isa := .seq c (.seq (wipeBelow n) (.block (tail rb)))

end VG.Impl.Scrub.X86
