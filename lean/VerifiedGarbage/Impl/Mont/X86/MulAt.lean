module

public import VerifiedGarbage.Impl.Mont.X86.Window
public import VerifiedGarbage.Spec.Rsa.MontMulAt

/-! # Callable Montgomery multiplication in the context's layout (32-bit x86)

`vg_rsa_mont_mul_ctx_{n}` (`Spec/Rsa/MontMulAt.lean`) multiplies in the
Montgomery context of `Impl/Mont/X86/Context.lean`, at width `n`: the modulus
in slot 0, its inverse in the header's first word, slots 1 and 2 the
function's own. The operands and the result are at byte offsets passed as
cdecl arguments (`ws` at `[esp + 4]`, then `o`, `a` and `b`), so the RSA
functions call one copy of the multiplication per width.

The function saves the callee-saved registers in slot 1, copies `b` into
slot 1 too, and runs `mul`'s rows (`rowTail`) with each row's multiplier
read from `a` through its argument (`rowAt`); the reduction leaves the
product in the low half of the accumulator (slot 2), whence it is copied to
`o`. Every address is the workspace pointer, an argument, or a pointer that
moves by a public step, so the timing does not depend on the numbers.
-/

@[expose] public section

namespace VG.Impl.Mont.X86.Dynamic
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86

/-- The arguments on entry: `ws` at `[esp + 4]`, then the byte offsets `o`, `a`
and `b`. -/
def argWs : MemOp := at_ .esp 4
def argO : MemOp := at_ .esp 8
def argA : MemOp := at_ .esp 12
def argB : MemOp := at_ .esp 16

/-- `[mult] = a_i`, at `edi + a + 4i`, with `ebp = edi + 4i` and `a` the argument. -/
def loadArgA (mult : Nat) : List Instr :=
  [.mov .eax (.mem argA), .alu .add .eax (.reg .ebp), .mov .eax (.mem { base := .eax }),
    .store (sc mult) .eax]

/-- A row of `mul`, its multiplier read through the argument `a`. -/
def rowAt (N acc b mo inv mult : Nat) : Prog isa :=
  .seq (.block (loadArgA mult)) (rowTail N acc b mo inv mult)

/-- The `k` words from `esi` up into `[dst]`, `esi` past them. -/
def copyIn (k dst : Nat) : Prog isa :=
  wordLoop k [.mov .eax (.mem { base := .esi }), .store (at_ .ebp dst) .eax, .alu .add .esi (.imm 4)]

/-- `mul` of the argument `a` and the number at `b`, the result left in the
low words of the accumulator. -/
def mulAt (M : Mod) (inv acc b : Nat) : Prog isa :=
  .seq (zerosW acc (2 * words M + 1)) <|
  .seq (.block [.mov .ebp (.reg .edi)]) <|
  .seq (.loop (rowAt (words M) acc b M.mo inv M.tmp) .ne)
    (csubW M (acc + 4 * words M) acc)

/-- Where the copy of `b` goes: slot 1, after the rows' multiplier word. -/
def atB (n : Nat) : Nat := slot n 1 + 4

/-- Where the callee-saved registers go: slot 1, after the copy of `b`. -/
def atSave (n : Nat) : Nat := slot n 1 + 4 + 8 * n

def atSlots (n : Nat) : List (Reg × Nat) :=
  [(.ebx, atSave n), (.esi, atSave n + 4), (.ebp, atSave n + 8), (.edi, atSave n + 12)]

/-- `edi = ws`, the caller's registers saved. -/
def atSaveCode (n : Nat) : List Instr :=
  [.mov .eax (.mem argWs)] ++ (atSlots n).map (fun (r, d) => .store (at_ .eax d) r) ++ [.mov .edi (.reg .eax)]

def atRestore (n : Nat) : List Instr := (atSlots n).map fun (r, d) => .mov r (.mem (sc d))

/-- `esi = edi + ` the argument at `arg`. -/
def pointAt (arg : MemOp) : List Instr := [.mov .esi (.mem arg), .alu .add .esi (.reg .edi)]

def mulAtBody (n : Nat) : Prog isa :=
  .seq (.block (atSaveCode n ++ pointAt argB)) <|
  .seq (copyIn (2 * n) (atB n)) <|
  .seq (mulAt (contextMod n) 0 (slot n 2) (atB n)) <|
  .seq (.block (pointAt argO)) <|
  .seq (copyOut (2 * n) (slot n 2)) (.block (atRestore n))

/-- The layout of the context at width `n`. -/
def ctxLayout (n : Nat) : Spec.Rsa.MontMulAt.Layout where
  tag := "ctx"
  n := n
  modulus := slot n 0
  inv := 0
  scratch := [(slot n 1, 2 * stride n)]
  words := contextBytes n / 8

/-- The widths of the RSA functions' contexts: `PublicFn.widths` (8 to 128
words) and the CRT factors' halves. -/
def mulWidths : List Nat := (List.range 125).map (· + 4)

def mulAtName (n : Nat) : String := (Spec.Rsa.MontMulAt.mulApi (ctxLayout n)).name

/-- `[o] = [a] [b] R⁻¹ mod m` in the context at `edi`, by a call of
`vg_rsa_mont_mul_ctx_{n}`: the offsets `o`, `a` and `b` in `edx`, `ecx` and
`eax`, pushed with `edi` as its arguments. -/
def callMul (n o a b : Nat) : Prog isa :=
  .seq (.block [.mov .eax (.imm (BitVec.ofNat 32 b)), .mov .ecx (.imm (BitVec.ofNat 32 a)),
      .mov .edx (.imm (BitVec.ofNat 32 o))])
    (.frame (.push [.eax, .ecx, .edx, .edi]) (.call (mulAtName n) (mulAtBody n)) (.pop .eax 4))

end VG.Impl.Mont.X86.Dynamic
