module

public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# P-256's reduction row, on PPC64LE

For P-256's `p = 2²⁵⁶ - 2²²⁴ + 2¹⁹² + 2⁹⁶ - 1`, `m' = -p⁻¹ mod 2⁶⁴` is 1, so a
row of the Montgomery multiplication (`qrow` in `Impl/Mont/PPC64LE.lean`)
adds `q p` for `q = t₀`, the accumulator's low word, and moves the
accumulator one register down. `q p` is shifts of `q`, so the row needs no
multiplication (`qrowP`): with the accumulator `T` in `r15`–`r19` and its
top word in `r12`, and `(T + q p) / 2⁶⁴ = T / 2⁶⁴ + q 2³² + D 2¹²⁸` for
`D = q 2⁶⁴ + q - q 2³² < 2¹²⁸`,

1. `r11 = q << 32` and `r9 = q >> 32`, the words of `q 2³²`;
2. `D`'s words into `r8` and `r15` (`q` is not needed after);
3. `q 2³²` and `D 2¹²⁸` added to words 1 to 5, each sum into the register
   one below (word 1's into `r11`, then moved to `r15`).

It writes `r8`, `r9`, `r11`, `r12` and `r15`–`r19`: `r8`, the loop's
counter for other moduli, is free in P-256's loop, whose one iteration
does the four rows.
-/

@[expose] public section

namespace VG.Impl.Mont.PPC64LE

open VG.PPC64LE

/-- P-256's `p`. -/
def p256p : Nat := 2 ^ 256 - 2 ^ 224 + 2 ^ 192 + 2 ^ 96 - 1

/-- The row `T = (T + q p) / 2⁶⁴` for P-256's `p` and `q = t₀`. -/
def qrowP : List Instr :=
  [.lsl .r11 .r15 32, .lsr .d .r9 .r15 32,
    .subc .r8 .r15 .r11, .sube .r15 .r15 .r9,
    .addc .r11 .r16 .r11, .adde .r16 .r17 .r9, .adde .r17 .r18 .r8, .adde .r18 .r19 .r15,
    .addze .r19 .r12, .ori .r15 .r11 0]

end VG.Impl.Mont.PPC64LE
