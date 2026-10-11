module

public import VerifiedGarbage.Impl.Ed25519.X86.Field
public import VerifiedGarbage.Spec.Ed25519.Point32

/-!
# Ed25519's point addition on x86 (32-bit), as a function

`vg_ed25519_r32_point_add(ws)` (`Spec/Ed25519/Point32.lean`), cdecl: `ws` at
`[esp + 4]`. It saves the callee-saved registers it changes (`ebx`, `ebp`
and `edi`) in its own working space (`SAVE`), loads `ws` into `edi`, runs
the addition the x86 Ed25519 code inlined (`pointAddOps`: slots 0–3 become
the sum of slots 0–3 and 4–7, with `d` in slot 16 and the temporaries in
slots 8–15), and restores the registers. It uses no stack, every address is
`edi` or `esp` plus a constant, and it has no branch: only the pointer may
affect timing.

The function's own working space is bytes 320 to 575 (slots 8–15) and 864
to 1023: X25519's 64-byte product (`T`) and `SAVE`.
-/

@[expose] public section

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

/-- `vg_ed25519_r32_point_add`. -/
def addFn : Prog isa := .block (entry ++ fieldCode pointAddOps ++ exit)

/-- A call of `vg_ed25519_r32_point_add`, `ws = edi` pushed as its argument.
The call changes `eax`, `ecx`, `edx`, the flags, slots 0–3 and 8–15, bytes
864 to 1023 of the working space and the 8 bytes below `esp`. -/
def addCall : Prog isa :=
  .frame (.push [.edi]) (.call Spec.Ed25519.Point32.addApi.name addFn) (.pop .eax 1)

end VG.Impl.Ed25519.X86.Point32
