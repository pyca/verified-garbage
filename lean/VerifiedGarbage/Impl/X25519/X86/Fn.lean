module

public import VerifiedGarbage.Impl.X25519.X86.Field32

/-!
# X25519: x86 (32-bit), the inversion and the function

`vg_x25519` (`Impl/X25519/X86.lean`): the setup, the ladder, the last swap,
the inversion and the result. The inversion `z2^(p-2)`, `p - 2 = 2²⁵⁵ - 21`,
is ref10's addition chain: `z2` is copied to byte 128 (`aAt`, among the
scalar's bits, which the ladder no longer needs), a call of
`vg_gf25519_r32_pow250` (`Field32.pow250Call`) leaves `z2^(2^250 - 1)` in
`E1` and `z2^11` in `E0`, and five squarings and a product finish the chain
in `E1`. The call uses the 8 bytes of stack below `esp`.
-/

@[expose] public section

namespace VG.Impl.X25519.X86

open VG.X86

/-- `[E1] = [Z2]^(p-2)`. -/
def invert : Prog isa :=
  .seq (.block (copy Field32.aAt Z2)) <| .seq Field32.pow250Call <|
    .seq (Field32.sqn Field32.E1 Field32.E1 5) (.block (mul Field32.E1 Field32.E1 Field32.E0))

/-- `x2 · z2^(p-2)`, reduced fully, to `out` (`[esp + 4]`), and the saved
registers restored. -/
def finish : List Instr :=
  mul X2 X2 Field32.E1 ++ freeze X2 ++
  .mov .esi (.mem (at_ .esp 4)) :: ((List.range 8).flatMap fun k =>
    [.mov .eax (.mem (sc (X2 + 4 * k))), .store (at_ .esi (4 * k)) .eax]) ++
  restore

def x25519 : Prog isa :=
  .seq setup <| .seq ladder <| .seq (.block lastSwap) <| .seq invert (.block finish)

end VG.Impl.X25519.X86
