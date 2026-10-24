module

public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Arith

/-!
# ML-DSA on PPC64LE: rounding and hints

`vg_mldsa_power2round`, `vg_mldsa_high_bits`, `vg_mldsa_low_bits`,
`vg_mldsa_norm_lt`, `vg_mldsa_make_hint` and `vg_mldsa_use_hint`, as on x86
(`Impl/MlDsa/X86/Round/Round.lean`): each is one loop over the 256
coefficients, with a pointer register at coefficient `i` of each polynomial
and a count of the coefficients left. The arithmetic is on all 64 bits, where
the values never wrap around, and there is no branch on data: a value `u` in
`(-k, k)` is brought into `[0, k)` by `fixup` (`Impl/MlKem/PPC64LE/Poly.lean`),
which adds `k` (in a register) if `u` is negative.

`Decompose` divides by `2γ₂` with a multiplication and shifts (`hbRaw`):
`f = ⌊(⌊(a + 127)/2⁷⌋ · M + 2^(S-1)) / 2^S⌋` for `(M, S)` = `(1025, 22)` if
`γ₂ = (q - 1)/32` and `(11275, 24)` if `γ₂ = (q - 1)/88`, which is
`⌊(a + γ₂ - 1)/(2γ₂)⌋` for every `a < q` (`VG.Proof.MlDsa.Round.hbF_eq`);
then `r₁ = f mod m`, for `m = (q - 1)/(2γ₂)` (16 or 44), is one conditional
subtraction of `m`, as `f ≤ m` (`hb`). `M`, `2^(S-1)` and `m` are in `r10`,
`r11` and `r12` (`hbConsts`). `γ₂` is a public argument: the functions that
take it compare it with `(q - 1)/32` once (`gSel`), and branch to one loop
for each value.

* `power2Round(t = r3, t1 = r4, t0 = r5)`: `x = a + 4095`, `t1 = x >> 13`
  and `t0 = x - (t1 << 13) - 4095` (`(x mod 2¹³) - 4095`), plus `q` if
  negative.
* `highBits(r = r3, gamma2 = r4, out = r5)`: `r₁`.
* `lowBits(r = r3, gamma2 = r4, out = r5)`: `a - r₁ · 2γ₂`, plus `q` if
  negative (`a` kept in `r0`, `2γ₂` in `r4`).
* `normLt(f = r3, bound = r4)`: `r9` stays 1 while every coefficient `a` so
  far has `a < bound` or `q - a < bound` (the signs of `a - bound` and
  `q - a - bound`); it is the result.
* `makeHint(z = r3, r = r4, gamma2 = r5, h = r6)`: `r₁` of `r`, stored to
  `h[i]` and loaded back, and of `r + z mod q`, xored, is nonzero
  (`(x + 63) >> 6`, as `x < 64`) exactly when the hint is 1; `r0` counts
  the 1s.
* `useHint(h = r3, r = r4, gamma2 = r5, out = r6)`: `(f + m + δ) mod m`, for
  `δ` 0 if the hint is 0 (the sign of `h[i] - 1`) and else 1 if
  `f · 2γ₂ < a` (`r₀ > 0`), -1 otherwise: `f + δ` is in `[-1, m + 1]`, so
  `fixup` and then a conditional subtraction of `m` reduce it.
-/

@[expose] public section

namespace VG.Impl.MlDsa.PPC64LE.Round

open VG.PPC64LE
open VG.Impl.MlKem.PPC64LE (fixup)
open VG.Impl.MlDsa.PPC64LE.Arith (loadImm loadQ)

/-! ## `Decompose` -/

/-- The multiplier `M`. -/
def dMul (g : Nat) : Nat := if g = 261888 then 1025 else 11275

/-- The shift `S`. -/
def dShift (g : Nat) : Nat := if g = 261888 then 22 else 24

/-- `2^(S-1)`. -/
def dAdd (g : Nat) : Nat := if g = 261888 then 2 ^ 21 else 2 ^ 23

/-- `m = (q - 1)/(2γ₂)`. -/
def dMod (g : Nat) : Nat := if g = 261888 then 16 else 44

/-- The values of `γ₂`: `(q - 1)/32` and `(q - 1)/88`. -/
def g32 : Nat := 261888
def g88 : Nat := 95232

/-- `r10 = M`, `r11 = 2^(S-1)`, `r12 = m`. -/
def hbConsts (g : Nat) : List Instr := loadImm .r10 (dMul g) ++ loadImm .r11 (dAdd g) ++ [.li .r12 (dMod g)]

/-- `d ← f` for `a = d`. -/
def hbRaw (g : Nat) (d : Reg) : List Instr :=
  [.addi d d 127, .lsr .d d d 7, .mul d d .r10, .add d d .r11, .lsr .d d d (dShift g)]

/-- `d ← r₁ = f mod m` for `a = d`, with `t` a temporary. -/
def hb (g : Nat) (d t : Reg) : List Instr := hbRaw g d ++ [.subi d d (dMod g)] ++ fixup d t .r12

/-- `r0 ← γ₂ - (q - 1)/32` for `γ₂` in `r`, through `r7`. -/
def gSel (r : Reg) : List Instr := loadImm .r7 261888 ++ [.sub .r0 r .r7]

/-! ## `power2Round` -/

def p2rBody : List Instr :=
  [.load .w .r8 .r3 0, .addi .r8 .r8 4095, .lsr .d .r9 .r8 13, .store .w .r9 .r4 0, .lsl .r10 .r9 13,
    .sub .r8 .r8 .r10, .subi .r8 .r8 4095] ++ fixup .r8 .r9 .r7 ++
  [.store .w .r8 .r5 0, .addi .r3 .r3 4, .addi .r4 .r4 4, .addi .r5 .r5 4, .subi .r6 .r6 1]

def power2Round : Prog isa :=
  .seq (.block (.li .r6 256 :: loadQ .r7)) (.loop (.block p2rBody) (.nonzero .d .r6))

/-! ## `highBits` and `lowBits` -/

def hbBody (g : Nat) : List Instr :=
  [.load .w .r8 .r3 0] ++ hb g .r8 .r9 ++ [.store .w .r8 .r5 0, .addi .r3 .r3 4, .addi .r5 .r5 4, .subi .r6 .r6 1]

def hbLoop (g : Nat) : Prog isa :=
  .seq (.block (hbConsts g ++ [.li .r6 256])) (.loop (.block (hbBody g)) (.nonzero .d .r6))

def highBits : Prog isa := .seq (.block (gSel .r4)) (.ite (.zero .w .r0) (hbLoop g32) (hbLoop g88))

def lbBody (g : Nat) : List Instr :=
  [.load .w .r8 .r3 0, .load .w .r0 .r3 0] ++ hb g .r8 .r9 ++ [.mul .r8 .r8 .r4, .sub .r0 .r0 .r8] ++
    fixup .r0 .r9 .r7 ++ [.store .w .r0 .r5 0, .addi .r3 .r3 4, .addi .r5 .r5 4, .subi .r6 .r6 1]

def lbLoop (g : Nat) : Prog isa :=
  .seq (.block (hbConsts g ++ loadImm .r4 (2 * g) ++ loadQ .r7 ++ [.li .r6 256]))
    (.loop (.block (lbBody g)) (.nonzero .d .r6))

def lowBits : Prog isa := .seq (.block (gSel .r4)) (.ite (.zero .w .r0) (lbLoop g32) (lbLoop g88))

/-! ## `normLt` -/

def nlBody : List Instr :=
  [.load .w .r6 .r3 0, .sub .r7 .r6 .r4, .lsr .d .r7 .r7 63, .sub .r8 .r5 .r6, .sub .r8 .r8 .r4,
    .lsr .d .r8 .r8 63, .logic .or .r7 .r7 .r8, .logic .and .r9 .r9 .r7, .addi .r3 .r3 4, .subi .r10 .r10 1]

def normLt : Prog isa :=
  .seq (.block ([.lsr .w .r4 .r4 0, .li .r9 1, .li .r10 256] ++ loadQ .r5))
    (.seq (.loop (.block nlBody) (.nonzero .d .r10)) (.block [.logic .or .r3 .r9 .r9]))

/-! ## `makeHint` and `useHint` -/

/-- `MakeHint` of `[r3]` and `[r4]` stored to `[r6]`, and counted in `r0`. -/
def mhBody (g : Nat) : List Instr :=
  [.load .w .r8 .r4 0] ++ hb g .r8 .r9 ++
  [.store .w .r8 .r6 0, .load .w .r8 .r4 0, .load .w .r9 .r3 0, .add .r8 .r8 .r9, .sub .r8 .r8 .r5] ++
    fixup .r8 .r9 .r5 ++ hb g .r8 .r9 ++
  [.load .w .r9 .r6 0, .logic .xor .r8 .r8 .r9, .addi .r8 .r8 63, .lsr .d .r8 .r8 6, .store .w .r8 .r6 0,
    .add .r0 .r0 .r8, .addi .r3 .r3 4, .addi .r4 .r4 4, .addi .r6 .r6 4, .subi .r7 .r7 1]

def mhLoop (g : Nat) : Prog isa :=
  .seq (.block (hbConsts g ++ loadQ .r5 ++ [.li .r7 256, .li .r0 0]))
    (.seq (.loop (.block (mhBody g)) (.nonzero .d .r7)) (.block [.logic .or .r3 .r0 .r0]))

def makeHint : Prog isa := .seq (.block (gSel .r5)) (.ite (.zero .w .r0) (mhLoop g32) (mhLoop g88))

/-- `UseHint` of `[r3]` and `[r4]` stored to `[r6]`. -/
def uhBody (g : Nat) : List Instr :=
  [.load .w .r8 .r4 0, .load .w .r9 .r4 0] ++ hbRaw g .r9 ++
  [.mul .r0 .r9 .r5, .sub .r0 .r0 .r8, .lsr .d .r0 .r0 63, .lsl .r0 .r0 1, .subi .r0 .r0 1,
    .load .w .r8 .r3 0, .subi .r8 .r8 1, .lsr .d .r8 .r8 63, .mul .r8 .r8 .r0, .sub .r0 .r0 .r8,
    .add .r9 .r9 .r0] ++ fixup .r9 .r8 .r12 ++
  [.subi .r9 .r9 (dMod g)] ++ fixup .r9 .r8 .r12 ++
  [.store .w .r9 .r6 0, .addi .r3 .r3 4, .addi .r4 .r4 4, .addi .r6 .r6 4, .subi .r7 .r7 1]

def uhLoop (g : Nat) : Prog isa :=
  .seq (.block (hbConsts g ++ loadImm .r5 (2 * g) ++ [.li .r7 256])) (.loop (.block (uhBody g)) (.nonzero .d .r7))

def useHint : Prog isa := .seq (.block (gSel .r5)) (.ite (.zero .w .r0) (uhLoop g32) (uhLoop g88))

end VG.Impl.MlDsa.PPC64LE.Round
