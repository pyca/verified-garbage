module

public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# P-256's reduction row, on PPC64LE

For P-256's `p = 2²⁵⁶ - 2²²⁴ + 2¹⁹² + 2⁹⁶ - 1`, `m' = -p⁻¹ mod 2⁶⁴` is 1, so a
row of the Montgomery multiplication (`qrowM` in `Impl/Mont/PPC64LE.lean`)
adds `q p` for `q = t₀`, the accumulator's low word, and moves the
accumulator one register down. `q p` is shifts of `q`, so the row needs no
multiplication (`qrowP`): with the accumulator `T` in `r15`–`r19` and its
top word in `r12`,

1. `r11 = q << 32` and `r9 = q >> 32`, the words of `q 2³²`;
2. `q 2²²⁴` subtracted from words 3 to 5 (`r18`, `r19`, `r12`; the borrow
   out of `r12`, if any, is wrapped modulo `2⁶⁴`, as the sum below is
   below `2³⁸⁴`);
3. `q 2⁹⁶`, `q 2¹⁹²` and `q 2²⁵⁶` added to words 1 to 5;
4. the words 1 to 5 moved to `r15`–`r19` (word 0 is `q`, and `T + q p` is
   `T + q (2²⁵⁶ - 2²²⁴ + 2¹⁹² + 2⁹⁶) - q`).

It writes `r9`, `r11`, `r12` and `r15`–`r19`, as `qrowM` does.
-/

@[expose] public section

namespace VG.Impl.Mont.PPC64LE

open VG.PPC64LE

/-- P-256's `p`. -/
def p256p : Nat := 2 ^ 256 - 2 ^ 224 + 2 ^ 192 + 2 ^ 96 - 1

/-- The row `T = (T + q p) / 2⁶⁴` for P-256's `p` and `q = t₀`. -/
def qrowP : List Instr :=
  [.lsl .r11 .r15 32, .lsr .d .r9 .r15 32,
    .subc .r18 .r18 .r11, .sube .r19 .r19 .r9, .addze .r12 .r12, .subi .r12 .r12 1,
    .addc .r16 .r16 .r11, .adde .r17 .r17 .r9, .adde .r18 .r18 .r15, .adde .r19 .r19 .r15,
    .addze .r12 .r12,
    .ori .r15 .r16 0, .ori .r16 .r17 0, .ori .r17 .r18 0, .ori .r18 .r19 0, .ori .r19 .r12 0]

end VG.Impl.Mont.PPC64LE
