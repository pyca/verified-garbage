import VerifiedGarbage.Impl.X25519.X86
import VerifiedGarbage.Spec.X25519.Field32

/-!
# Powers in curve25519's field on x86 (32-bit), as a function

`vg_gf25519_r32_pow250(ws)` (`Spec/X25519/Field32.lean`), cdecl: `ws` at
`[esp + 4]`. It saves the callee-saved registers in its own working space
(`SAVE`), loads `ws` into `edi`, copies `a` (byte 128) to `AC`, and runs the
addition chain of ref10's `fe_invert` up to `a^(2^250 - 1)` with X25519's
product (`chain`): `a^11` is left at byte 512 (`E0`) and `a^(2^250 - 1)` at
byte 544 (`E1`), with the temporaries `E2` and `E3`, X25519's 64-byte
product (`T`, 864) and the counter `esi` of the runs of squarings. Then it
restores the registers. It uses no stack, every address is `edi` or `esp`
plus a constant, and the only branches are on the counter: only the pointer
may affect timing.

The function's own working space is bytes 576 to 1023: `E2`, `E3`, `AC`,
`T` and `SAVE`.
-/

namespace VG.Impl.X25519.X86.Field32

open VG.X86 VG.Impl.X25519.X86

/-- Where `a^11` is left. -/
def E0 : Nat := 512

/-- Where `a^(2^250 - 1)` is left. -/
def E1 : Nat := 544

/-- The chain's temporaries. -/
def E2 : Nat := 576
def E3 : Nat := 608

/-- The copy of `a`. -/
def AC : Nat := 640

/-- Where the function saves `ebx`, `esi`, `edi` and `ebp`. -/
def SAVE : Nat := 928

/-- `[o] = [a]^(2^n)`, for `n ≥ 2`: a squaring from `a`, then `n - 1` in
place, counted by `esi`. -/
def sqn (o a n : Nat) : Prog isa :=
  .seq (.block (mul o a a ++ [.mov .esi (.imm (BitVec.ofNat 32 (n - 1)))]))
    (.loop (.block (mul o o o ++ [.alu .sub .esi (.imm 1)])) .ne)

/-- From `a` at `AC`, `a^(2^250 - 1)` in `E1` and `a^11` in `E0`. -/
def chain : Prog isa :=
  .seq (.block (mul E0 AC AC)) <|                                             -- a^2
  .seq (.block (mul E1 E0 E0 ++ mul E1 E1 E1)) <|                           -- a^8
  .seq (.block (mul E1 AC E1 ++ mul E0 E0 E1 ++ mul E2 E0 E0 ++ mul E1 E1 E2)) <| -- a^(2^5 - 1)
  .seq (sqn E2 E1 5) <| .seq (.block (mul E1 E2 E1)) <|                    -- a^(2^10 - 1)
  .seq (sqn E2 E1 10) <| .seq (.block (mul E2 E2 E1)) <|                   -- a^(2^20 - 1)
  .seq (sqn E3 E2 20) <| .seq (.block (mul E2 E3 E2)) <|                   -- a^(2^40 - 1)
  .seq (sqn E2 E2 10) <| .seq (.block (mul E1 E2 E1)) <|                   -- a^(2^50 - 1)
  .seq (sqn E2 E1 50) <| .seq (.block (mul E2 E2 E1)) <|                   -- a^(2^100 - 1)
  .seq (sqn E3 E2 100) <| .seq (.block (mul E2 E3 E2)) <|                  -- a^(2^200 - 1)
  .seq (sqn E2 E2 50) (.block (mul E1 E2 E1))                              -- a^(2^250 - 1)

/-- The registers saved at `SAVE` through `eax = ws`, `edi = ws`, and `a`
copied to `AC`. -/
def entry : List Instr :=
  [.mov .eax (.mem (at_ .esp 4)), .store (at_ .eax SAVE) .ebx, .store (at_ .eax (SAVE + 4)) .esi,
    .store (at_ .eax (SAVE + 8)) .edi, .store (at_ .eax (SAVE + 12)) .ebp, .mov .edi (.reg .eax)] ++
  copy AC Spec.X25519.Field32.aAt

/-- The registers restored, through `edx = ws`. -/
def exit : List Instr :=
  [.mov .edx (.reg .edi), .mov .ebx (.mem (at_ .edx SAVE)), .mov .esi (.mem (at_ .edx (SAVE + 4))),
    .mov .ebp (.mem (at_ .edx (SAVE + 12))), .mov .edi (.mem (at_ .edx (SAVE + 8)))]

/-- `vg_gf25519_r32_pow250`. -/
def pow250Fn : Prog isa := .seq (.block entry) (.seq chain (.block exit))

/-- A call of `vg_gf25519_r32_pow250`, `ws = edi` pushed as its argument. The
call changes `eax`, `ecx`, `edx`, the flags, bytes 512 to 1023 of the
working space and the 8 bytes below `esp`. -/
def pow250Call : Prog isa :=
  .frame (.push [.edi]) (.call Spec.X25519.Field32.pow250Api.name pow250Fn) (.pop .eax 1)

end VG.Impl.X25519.X86.Field32
