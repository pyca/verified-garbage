import VerifiedGarbage.Impl.Ed25519.X86.Field
import VerifiedGarbage.Spec.Ed25519.Point32

/-!
# Ed25519's point addition and doubling on x86 (32-bit), as functions

`vg_ed25519_r32_point_add(ws)`, `vg_ed25519_r32_add_affine(ws)` and
`vg_ed25519_r32_double(ws)` (`Spec/Ed25519/Point32.lean`), cdecl: `ws` at
`[esp + 4]`. Each (`fnOf`) saves the callee-saved registers it changes
(`ebx`, `ebp` and `edi`) in its own working space (`SAVE`), loads `ws` into
`edi`, runs its field program (`pointAddOps`: slots 0–3 become the sum of
slots 0–3 and 4–7, with `d` in slot 16; `pointAddAffineOps`: the sum of slots
0–3 and the affine cached point in slots 4–6; `pointDoubleRfcOps`: the double
of slots 0–3; the temporaries in slots 8–15), and restores the registers. It
uses no stack, every address is `edi` or `esp` plus a constant, and it has
no branch: only the pointer may affect timing.

The function's own working space is bytes 320 to 575 (slots 8–15) and 864
to 1023: X25519's 64-byte product (`T`) and `SAVE`.
-/

namespace VG.Impl.Ed25519.X86.Point32

open VG.X86 VG.Impl.Ed25519.X86
open VG.Impl.X25519.X86 (at_)

/-- Where the function saves `ebx`, `ebp` and `edi`. -/
def SAVE : Nat := 928

/-- The registers saved at `SAVE` through `eax = ws`, and `edi = ws`. -/
def entry : List Instr :=
  [.mov .eax (.mem (at_ .esp 4)), .store (at_ .eax SAVE) .ebx, .store (at_ .eax (SAVE + 4)) .ebp,
    .store (at_ .eax (SAVE + 8)) .edi, .mov .edi (.reg .eax)]

/-- The registers restored, through `edx = ws`. -/
def exit : List Instr :=
  [.mov .edx (.reg .edi), .mov .ebx (.mem (at_ .edx SAVE)), .mov .ebp (.mem (at_ .edx (SAVE + 4))),
    .mov .edi (.mem (at_ .edx (SAVE + 8)))]

/-- A function running the field program `ops` on the working space. -/
def fnOf (ops : List FieldOp) : Prog isa := .block (entry ++ fieldCode ops ++ exit)

/-- `vg_ed25519_r32_point_add`. -/
def addFn : Prog isa := fnOf pointAddOps

/-- `vg_ed25519_r32_add_affine`. -/
def affFn : Prog isa := fnOf pointAddAffineOps

/-- `vg_ed25519_r32_double`. -/
def doubleFn : Prog isa := fnOf pointDoubleRfcOps

/-- A call of the function `fn`, named `name`, `ws = edi` pushed as its argument. The call
changes `eax`, `ecx`, `edx`, the flags, slots 0–3 and 8–15, bytes 864 to 1023 of the working
space and the 8 bytes below `esp`. -/
def callOf (name : String) (fn : Prog isa) : Prog isa :=
  .frame (.push [.edi]) (.call name fn) (.pop .eax 1)

/-- A call of `vg_ed25519_r32_point_add`. -/
def addCall : Prog isa := callOf Spec.Ed25519.Point32.addApi.name addFn

/-- A call of `vg_ed25519_r32_add_affine`. -/
def affCall : Prog isa := callOf Spec.Ed25519.Point32.addAffineApi.name affFn

/-- A call of `vg_ed25519_r32_double`. -/
def doubleCall : Prog isa := callOf Spec.Ed25519.Point32.doubleApi.name doubleFn

end VG.Impl.Ed25519.X86.Point32
