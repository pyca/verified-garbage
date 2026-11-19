module

public import VerifiedGarbage.TCB.X86.Isa

/-!
# Returning without secret residue (x86, 32-bit)

`scrubF retBits n c` runs `c`, then clears everything `c` may have left
where its Rust caller cannot clear it (`X86.NoResidue`):

* the `n` bytes of stack below `esp` (the stack `c`'s frames and calls use),
  in nested frames of the sizes `chunks n` (`wipeBelow`), each of at most
  4080 bytes, as the model's frames are of less than a page: `pxor xmm0,
  xmm0` (and `mov ecx, 0` if a frame's size is not a multiple of 16), then,
  in each frame, `movdqu [esp + 16k], xmm0` for every 16 bytes of it, and
  `mov [esp + off], ecx` for each doubleword left over (`zeroFrame`);
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

/-- `movdqu [esp + 16k], xmm0` for `k` from `k₀` to `k₀ + n - 1`. -/
def stores16 (k₀ : Nat) : Nat → List Instr
  | 0 => []
  | n + 1 => .movdquStore ⟨.esp, 16 * k₀⟩ .xmm0 :: stores16 (k₀ + 1) n

/-- `mov [esp + 4k], ecx` for `k` from `k₀` to `k₀ + n - 1`. -/
def stores4 (k₀ : Nat) : Nat → List Instr
  | 0 => []
  | n + 1 => .store ⟨.esp, 4 * k₀⟩ .ecx :: stores4 (k₀ + 1) n

/-- Zero the `b` bytes at `esp` (a multiple of 4), with `xmm0` and `ecx`
zero: by 16 at a time, then the doublewords left over. -/
def zeroFrame (b : Nat) : List Instr := stores16 0 (b / 16) ++ stores4 (4 * (b / 16)) (b % 16 / 4)

/-- Zero the stack below `esp` in nested frames of the sizes `cs`. -/
def wipe : List Nat → Prog isa
  | [] => .block []
  | b :: bs => .frame (.alloc b) (.seq (.block (zeroFrame b)) (wipe bs)) (.free b)

/-- Frames of at most 4080 bytes (`fuel` of them at most) summing to `n`. -/
def chunksAux : Nat → Nat → List Nat
  | 0, _ => []
  | _ + 1, 0 => []
  | f + 1, n + 1 => if n + 1 ≤ 4080 then [n + 1] else 4080 :: chunksAux f (n + 1 - 4080)

def chunks (n : Nat) : List Nat := chunksAux (n / 4080 + 1) n

/-- Zero `xmm0`, and `ecx` if a frame of `cs` is not a multiple of 16 bytes. -/
def zeroRegs (cs : List Nat) : List Instr :=
  .xop (.bin .pxor .xmm0 .xmm0) :: if cs.all (· % 16 == 0) then [] else [.mov .ecx (.imm 0)]

/-- Zero the `n` bytes below `esp`, in nested frames of the sizes `chunks n`. -/
def wipeBelow (n : Nat) : Prog isa := .seq (.block (zeroRegs (chunks n))) (wipe (chunks n))

/-- `c`, then the `n` bytes below `esp` zeroed, then `tail rb`. -/
def scrubF (rb n : Nat) (c : Prog isa) : Prog isa := .seq c (.seq (wipeBelow n) (.block (tail rb)))

end VG.Impl.Scrub.X86
