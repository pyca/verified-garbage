module

public import VerifiedGarbage.TCB.PPC64LE.Print
public import VerifiedGarbage.TCB.Artifact

/-!
# The 64-bit little-endian PowerPC target (ELFv2)

**Trusted.** Functions are emitted as Rust `extern "C"` naked functions,
compiled for little-endian `powerpc64`, whose C calling convention is the
64-bit ELF V2 ABI (OpenPOWER, Revision 1.5).

ELFv2 (§2.2.2.1, "Register Roles"): integer and pointer arguments arrive in
`r3`–`r10`; `r14`–`r31` are nonvolatile, as is `r1`, the stack pointer, and
`r2`, the TOC pointer, must hold the same value on return (for a function
whose symbol's `st_other` entry-point bits are 0, as for a naked function,
which has a single entry point: §3.4.1, "Symbol Values"). `r13`, the thread
pointer, is reserved; the model never changes it. The printer ends every
function with `blr`, which returns to the address in the link register, so
`LR` must be unchanged on exit.

Only volatile vectors `v0`–`v19` (`VSR32`–`VSR51`) are modelled. Not
modelled: the floating-point registers and `v20`–`v31` (never modified;
`f14`–`f31` and `v20`–`v31` are nonvolatile), the condition register (only
field 0, which is volatile, is ever modified: the nonvolatile fields
`CR2`–`CR4` are not), `XER` except its carry bit CA, and `CTR` (never modified;
both volatile), and memory below `r1` (never granted to a
function; the frames' pushes write there, see `push`).
-/

@[expose] public section

namespace VG.PPC64LE

def preserved : List Reg := [.r2, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23,
  .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31]

/-- Calling-convention obligations on return. -/
def abiPreserved (s s' : State) : Prop :=
  (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.lr = s.lr

/-- ELFv2 argument registers, in order. -/
def argRegs : List Reg := [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10]

/-! ## The calling convention, for `Sig`

Each integer or pointer argument takes the next of `r3`–`r10` (§2.2.4, "Up
to eight arguments can be passed in general-purpose registers r3–r10"; a
32-bit argument in the low half, whose upper half the model does not rely
on). Further arguments are in memory, in the caller's Parameter Save Area
(§2.2.3.3, "Parameter Save Area"), which "must always start at SP + 32" and
"shall be at least 8 doublewords in length": the caller allocates it "for
function calls unless a prototype is provided for the callee indicating that
all parameters can be passed in registers", and it maps each simple integer
type and each pointer "to a single doubleword". Its first eight doublewords
stand for `r3`–`r10` ("The first 8 doublewords are located in general
registers r3–r10. Any additional doublewords are located in the stack
Parameter Save Area"), so the `i`-th (from 0) argument after the eighth is the
doubleword at `sp + 32 + 8 * (8 + i)` on entry (`stackArg`). A narrower
integer (`u32`) is in the doubleword's low bits: "Map simple integer types
(char, short, int, long, enum) to a single doubleword. Sign or zero extend
values shorter than a doubleword to a doubleword based on whether the source
data type is signed or unsigned" (§2.2.3.3), so its value is the low bits of
the doubleword, the model relying on the upper bits no more than for a
register. `abi` only grants reading them, and assumes they do not wrap around
the end of the address space. The return address is in `LR`, not in memory;
the integer result is in `r3` (§2.2.6).
-/

/-- The address of the `i`-th (from 0) argument in memory, the one after the
first eight, on entry: doubleword `8 + i` of the Parameter Save Area, at
`sp + 32`. -/
def stackArgAddr (s : State) (i : Nat) : Addr := s.sp + BitVec.ofNat 64 (32 + 8 * (8 + i))

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
  -- The stack the function's calls and frames use, and its arguments in
  -- memory, do not wrap around.
  wf ws n s := if ws.length ≤ argRegs.length then
      match n with
      | 0 => True
      | n => n ≤ s.sp.toNat
    else
      (match n with
      | 0 => True
      | n => n ≤ s.sp.toNat) ∧ s.sp.toNat + 32 + 8 * ws.length ≤ 2 ^ 64
  pub s₁ s₂ := s₁.sp = s₂.sp
  mem s := s.mem
  rd s := s.rd
  wr s := s.wr
  ret s := s.gpr .r3
  argAreaDoc ws := if ws.length - argRegs.length = 0 then none else
    some ("the arguments on the stack", false)
  reservedDoc n := if n = 0 then none else some s!"the {n} bytes of stack below the stack pointer"
  sym := some fun s name => s.syms name

/-- Reducible, as an `abbrev` would be, but not inlined: an `abbrev` is compiled into
every module that names it, which then builds a target of its own, so the emitter
would see one per registration module rather than this one (`Rust.printsAs`). -/
@[reducible] def target : Target where
  name := "powerpc64le"
  isa := isa
  printer := printer
  abiPreserved := abiPreserved
  rustCfg := "all(target_arch = \"powerpc64\", target_endian = \"little\")"
  rustAbi := "C"
  abi := abi

end VG.PPC64LE
