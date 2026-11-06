module

public import VerifiedGarbage.Impl.Ed448.AArch64.VerifyEquation
public import VerifiedGarbage.Impl.Ed448.AArch64.CombBase
public import VerifiedGarbage.Impl.Ed448.AArch64.Point56

/-!
# Ed448 verification's equation on AArch64, by a comb and 4-bit windows

`vg_ed448_verify_equation(pk = x0, signature = x1, challenge = x2,
scratch = x3) -> w0`: the checks of `S` and of the encodings of `A` and `R`
are `VerifyEquation.lean`'s (with X448's memory-resident arithmetic), as is the
comparison of `[4]Q` with `[4]R`; but `Q = [S]B + [k](-A)` is computed with the
register-resident arithmetic (`Impl/Curve448/AArch64/Fast.lean`):

* `[S]B` by `vg_ed448_scalar_base`'s comb of 57 tables (`vg_ed448_r56_comb_base`, `CombBase.call 57`),
  from the bits of `S` at `BITS`.
* `[k](-A)` by 4-bit windows from the top (the challenge's nibbles, expanded into bytes at
  `BITS` once `[S]B` no longer needs it), each four doublings and the
  addition of `[n](-A)` for the window's digit `n`, selected in constant time
  with a mask for each of the 16 entries of a table of `[n](-A)` built at run
  time (`TAB`, entry `n` at `TAB + 192 n`: `X`, `Y` and `Z`, eight words each).
  Entry 0 is the neutral point, so every window adds one.

The additions and doublings of the table, the windows and the comparison are
calls of `vg_ed448_r56_point_add` and `vg_ed448_r56_point_double`
(`Point56.lean`), on slots 3–5 and 6–8. The challenge's bytes are copied to
the working space (`KB`) at the entry, since the field operations use every
register that could keep its pointer; `R`, once decoded, is kept at `RX` and
`RY`. The function saves `x19`–`x28`, its return address and `v8`–`v15` in
the working space and restores them. Every address and branch depends only on
the pointers and counters.
-/

@[expose] public section

namespace VG.Impl.Ed448.AArch64

open VG.AArch64
open VG.Impl.X448.AArch64 (ld st slot BITS)
open VG.Impl.X448.AArch64.Fast (codeOf opsK)
open VG.Impl.X448.AArch64.Base (constSlot)

/-! ## The working space -/

/-- The challenge's 57 bytes, copied at the entry: the windows read them from the working
space, at addresses from public registers. -/
def KB : Nat := 2944
/-- The table of `[n](-A)`, `n < 16`: 192 bytes each. -/
def TAB : Nat := 4992
/-- `R`'s `x` and `y`: after the table, and at `CAN`, which nothing uses between the decoding of
`R` and its comparison. -/
def RX : Nat := 8064
def RY : Nat := CAN

/-! ## Entry -/

/-- The challenge's bytes copied to `KB`, and `x21`–`x28` and `v8`–`v15` saved. -/
def wsave : List Instr :=
  (List.range 57).flatMap (fun i => [.ldrb .x4 .x2 i, .strb .x4 .x3 (KB + i)]) ++
    Impl.X448.AArch64.Fast.save ++ Impl.X448.AArch64.Fast.vsave

/-! ## The table of `[n](-A)` -/

/-- Slots 3–5 to entry `x19` of the table. -/
def tabStore : List Instr :=
  [.lsl .x .x8 .x19 7, .lsl .x .x9 .x19 6, .add .x .x8 .x8 .x9, .add .x .x8 .x8 .x3] ++
  (List.range 24).flatMap fun w =>
    [ld .x4 (slot (3 + w / 8) + 8 * (w % 8)), .str .x .x4 .x8 (TAB + 8 * w)]

/-! ## The comparison -/

/-- One comparison: slots 12 and 13 compared (`eqSlots`), then slots 14 and 15 copied into
them, for the second pass, and `x19` counted down. -/
def wcmp : Prog isa :=
  .seq (eqSlots 12 13) <| .block (Curve448.AArch64.copy (slot 12) (slot 14) ++
    Curve448.AArch64.copy (slot 13) (slot 15) ++ [.subImm .x .x19 .x19 1])

/-- The result `x0 = (x20 == 0)`, and the registers restored. -/
def wresult : List Instr :=
  [.addImm .x .x5 .x20 0] ++ isZero ++
  [.addImm .x .x0 .x5 0, ld .x19 0, ld .x20 8, ld .x30 LRS] ++ Impl.X448.AArch64.Fast.restore ++
  Impl.X448.AArch64.Fast.vrestore

/-- The comparisons of slots 12 and 13, then 14 and 15: two passes of `wcmp`, counted by
`x19`; then `wresult`. -/
def wfinish : Prog isa :=
  .seq (.seq (.block [.movz .x .x19 2 0]) (.loop wcmp (.nonzero .x .x19))) (.block wresult)

/-- The entry, the bits of `S`, its check, and the decodings of `A` (negated, into slots 6–7) and
`R` (into slots 8–9), by one copy of `decode` (`decodes`). -/
def wfront : Prog isa :=
  .seq (.seq ventry (.block wsave)) <| .seq (bitsAt .x1 57 0 BITS) <| .seq (.block sCheck) <|
  decodes

end VG.Impl.Ed448.AArch64
