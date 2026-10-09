import VerifiedGarbage.Impl.X25519.X86
import VerifiedGarbage.Spec.X25519.Field32

/-!
# Multiplication in curve25519's field on x86 (32-bit), as a function

`vg_gf25519_r32_mul(ws, o, a, b)` (`Spec/X25519/Field32.lean`), cdecl: the
arguments at `[esp + 4]` to `[esp + 16]`. It saves the callee-saved
registers it changes (`ebx`, `ebp`, `edi`) in its own working space
(`SAVE`), loads `ws` into `edi`, copies `[a]` (and `[b]`, if it is another
element) to the fixed offsets `opA` (and `opB`) of its own working space, and
runs X25519's product (`mul`, by `a²`'s columns for a square) with the
result over the copy of `[a]`. Then it restores the registers and copies the
result to `[ws + o]`. It uses no stack. Every address is `ws`, `ws` plus an
offset, or `esp`, plus a constant, and the only branch is on whether
`a = b`: only the arguments, which are public, may affect timing.

The function's own working space is bytes 768 to 1023: the copies at `opA`
and `opB`, the saved registers at `SAVE`, and X25519's 64-byte product at `T`
(864).
-/

namespace VG.Impl.X25519.X86.Field32

open VG.X86 VG.Impl.X25519.X86

/-- The copy of `[a]`, and the result. -/
def opA : Nat := 768

/-- The copy of `[b]`. -/
def opB : Nat := 800

/-- Where the function saves `ebx`, `ebp` and `edi`. -/
def SAVE : Nat := 832

/-- Argument `i`. -/
def argOp (i : Nat) : MemOp := at_ .esp (4 + 4 * i)

/-- `[edi + d + 4k] = [r + 4k]` for the eight words of an element, through `eax`. -/
def copyIn (r : Reg) (d : Nat) : List Instr :=
  (List.range 8).flatMap fun k => [.mov .eax (.mem (at_ r (4 * k))), .store (sc (d + 4 * k)) .eax]

/-- `[ecx + 4k] = [edx + opA + 4k]` for the eight words of the result, through `eax`. -/
def copyOut : List Instr :=
  (List.range 8).flatMap fun k => [.mov .eax (.mem (at_ .edx (opA + 4 * k))), .store (at_ .ecx (4 * k)) .eax]

/-- The registers saved at `SAVE` through `eax = ws`, `edi = ws`, `ecx = ws + a`,
`edx = ws + b`, and ZF set iff `a = b`. -/
def entry : List Instr :=
  [.mov .eax (.mem (argOp 0)), .store (at_ .eax SAVE) .ebx, .store (at_ .eax (SAVE + 4)) .ebp,
    .store (at_ .eax (SAVE + 8)) .edi, .mov .edi (.reg .eax), .mov .ecx (.mem (argOp 2)),
    .mov .edx (.mem (argOp 3)), .alu .add .ecx (.reg .edi), .alu .add .edx (.reg .edi),
    .alu .cmp .ecx (.reg .edx)]

/-- The square: `[a]` copied to `opA`, then `[opA]²` into `opA`. -/
def sqrBody : List Instr := copyIn .ecx opA ++ mul opA opA opA

/-- The product: `[a]` and `[b]` copied to `opA` and `opB`, then `[opA] [opB]` into `opA`. -/
def mulBody : List Instr := copyIn .ecx opA ++ copyIn .edx opB ++ mul opA opA opB

/-- `edx = ws`, `ecx = ws + o`, the registers restored, then the result
copied out. -/
def exit : List Instr :=
  [.mov .edx (.reg .edi), .mov .ecx (.mem (argOp 1)), .alu .add .ecx (.reg .edx),
    .mov .ebx (.mem (at_ .edx SAVE)), .mov .ebp (.mem (at_ .edx (SAVE + 4))),
    .mov .edi (.mem (at_ .edx (SAVE + 8)))] ++ copyOut

/-- `vg_gf25519_r32_mul`. -/
def mulFn : Prog isa :=
  .seq (.block entry) (.seq (.ite .e (.block sqrBody) (.block mulBody)) (.block exit))

/-- A call of `vg_gf25519_r32_mul`: the offsets in `eax`, `ecx` and `edx`, and
`ws = edi`, pushed as the arguments. The call changes `eax`, `ecx`, `edx`,
the flags, the result, the function's own working space and the 20 bytes
below `esp`. -/
def mulCall (o a b : Nat) : Prog isa :=
  .seq (.block [.mov .eax (.imm (BitVec.ofNat 32 o)), .mov .ecx (.imm (BitVec.ofNat 32 a)),
      .mov .edx (.imm (BitVec.ofNat 32 b))])
    (.frame (.push [.edx, .ecx, .eax, .edi]) (.call Spec.X25519.Field32.mulApi.name mulFn) (.pop .eax 4))

end VG.Impl.X25519.X86.Field32
