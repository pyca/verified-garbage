module

public import VerifiedGarbage.TCB.RISCV64.Print
public import VerifiedGarbage.TCB.Artifact

/-!
# The 64-bit RISC-V target (LP64 integer calling convention)

**Trusted.** Functions are emitted as Rust `extern "C"` naked functions,
compiled for little-endian `riscv64` with the M extension (the model's
multiplies, see `Isa.lean`) and the C extension (the compressed encodings
the printer emits for the instructions that have one, `Encode.lean`'s
`compress`: every `riscv64gc` target has both), whose C calling convention is the
RISC-V ELF psABI's (RISC-V ABIs Specification, Version 1.0, "RISC-V Calling
Conventions"): its integer
calling convention, which every RV64 ABI (LP64, LP64F, LP64D, LP64Q; the
Linux targets' is LP64D) shares, since these functions take and return only
integers and pointers.

psABI, "Integer Register Convention": integer and pointer arguments arrive
in `a0`–`a7`; `s0`–`s11` are callee-saved ("Preserved across calls: Yes"), as
is `sp`; `ra` holds the return address, and the printer ends every function
with `ret`, which jumps to it, so `ra` must be unchanged on exit. `gp` and
`tp` are "unallocatable": the model never changes them.

Not modelled: the floating-point registers (never modified; `fs0`–`fs11`
are callee-saved in the LP64F, LP64D and LP64Q ABIs), the vector registers
and CSRs (never modified), and memory below `sp` (never granted to a
function; the frames' pushes write there, see `push`).
-/

@[expose] public section

namespace VG.RISCV64

def preserved : List Reg := [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11]

/-- Calling-convention obligations on return. -/
def abiPreserved (s s' : State) : Prop :=
  (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.gpr .ra = s.gpr .ra

/-- psABI argument registers, in order. -/
def argRegs : List Reg := [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7]

/-! ## The calling convention, for `Sig`

Each integer or pointer argument takes the next of `a0`–`a7` ("Integer
Calling Convention": "The base integer calling convention provides eight
argument registers, a0-a7"; "Scalars that are at most XLEN bits wide are
passed in a single argument register, or on the stack by value if none is
available"). A 32-bit argument is in the register's low half, whose upper
half the model does not rely on: "integer scalars narrower than XLEN bits
are widened according to the sign of their type up to 32 bits, then
sign-extended to XLEN bits", so even a `u32` has its bit 31 copied into the
upper half. Further arguments are in memory: "The first argument passed on
the stack is located at offset zero of the stack pointer on function entry;
following arguments are stored at correspondingly higher addresses", each in
an XLEN-bit (8-byte) slot "on the stack by value" (`stackArg`), a narrower
one widened as in a register, so its value is the slot's low bits. `abi`
only grants reading them, and assumes they do not wrap around the end of the
address space. The return address is in `ra`, not in memory; the integer
result is in `a0` ("Values are returned in the same manner as a first named
argument of the same type would be passed").

The stack pointer is 16-byte aligned on entry ("the stack pointer shall be
aligned to a 128-bit boundary upon procedure entry"), which `wf` states for
the model's alignment checks (see `Isa.lean`).
-/

/-- The address of the `i`-th (from 0) argument in memory, the one after the
first eight, on entry: `sp + 8 i`. -/
def stackArgAddr (s : State) (i : Nat) : Addr := s.sp + BitVec.ofNat 64 (8 * i)

/-- The `i`-th (from 0) argument in memory, on entry. -/
def stackArg (s : State) (i : Nat) : BitVec 64 := s.mem.readW (stackArgAddr s i) 64

def abi : Abi isa where
  ptrBits := 64
  args ws := if ws.length ≤ argRegs.length then
    some fun s => (argRegs.take ws.length).map s.gpr
  else if (ws.drop argRegs.length).all (· ≤ 64) then
    some fun s => argRegs.map s.gpr ++ (List.range (ws.length - argRegs.length)).map (stackArg s)
  else none
  argArea ws s := let n := ws.length - argRegs.length
    if n = 0 then [] else [(⟨stackArgAddr s 0, 8 * n⟩, false)]
  reserved n s := stackBelow s.sp n
  -- The stack pointer is aligned, and the stack the function's calls and
  -- frames use, and its arguments in memory, do not wrap around.
  wf ws n s := s.sp.toNat % 16 = 0 ∧
    (match n with
      | 0 => True
      | n => n ≤ s.sp.toNat) ∧
    (ws.length ≤ argRegs.length ∨ s.sp.toNat + 8 * (ws.length - argRegs.length) ≤ 2 ^ 64)
  pub s₁ s₂ := s₁.sp = s₂.sp
  mem s := s.mem
  rd s := s.rd
  wr s := s.wr
  ret s := s.gpr .a0
  argAreaDoc ws := if ws.length - argRegs.length = 0 then none else
    some ("the arguments on the stack", false)
  reservedDoc n := if n = 0 then none else some s!"the {n} bytes of stack below the stack pointer"
  sym := some fun s name => s.syms name
  -- `lhu`/`sh`, `lwu`/`sw` and `ld`/`sd` fault on an address not a multiple of 2,
  -- 4 and 8 (`TCB/RISCV64/Isa.lean`), and a `u16`'s, `u32`'s and `u64`'s alignments
  -- are 2, 4 and 8 (the RISC-V ELF psABI, "C/C++ type details").
  alignsBufs := true

abbrev target : Target where
  name := "riscv64"
  isa := isa
  printer := printer
  abiPreserved := abiPreserved
  rustCfg := "all(target_arch = \"riscv64\", target_endian = \"little\", target_feature = \"m\", \
    target_feature = \"c\")"
  rustAbi := "C"
  abi := abi

end VG.RISCV64
