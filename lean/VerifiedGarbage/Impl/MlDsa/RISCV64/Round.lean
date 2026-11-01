module

public import VerifiedGarbage.Impl.MlDsa.RISCV64.Arith

/-!
# ML-DSA on RISC-V: rounding and hints

`vg_mldsa_power2round`, `vg_mldsa_high_bits`, `vg_mldsa_low_bits`,
`vg_mldsa_norm_lt`, `vg_mldsa_make_hint` and `vg_mldsa_use_hint`, as on
PPC64LE (`Impl/MlDsa/PPC64LE/Round.lean`): each is one loop over the 256
coefficients, with a pointer register at coefficient `i` of each polynomial
and a count of the coefficients left. The arithmetic is on all 64 bits, where
the values never wrap around, and there is no branch on data: a value `u` in
`(-k, k)` is brought into `[0, k)` by `fixup` (`Impl/MlKem/RISCV64/Poly.lean`),
which adds `k` (in a register) if `u` is negative.

`Decompose` divides by `2γ₂` with a multiplication and shifts (`hbRaw`):
`f = ⌊(⌊(a + 127)/2⁷⌋ · M + 2^(S-1)) / 2^S⌋` for `(M, S)` = `(1025, 22)` if
`γ₂ = (q - 1)/32` and `(11275, 24)` if `γ₂ = (q - 1)/88`, which is
`⌊(a + γ₂ - 1)/(2γ₂)⌋` for every `a < q` (`VG.Proof.MlDsa.Round.hbF_eq`);
then `r₁ = f mod m`, for `m = (q - 1)/(2γ₂)` (16 or 44), is one conditional
subtraction of `m`, as `f ≤ m` (`hb`). `M`, `2^(S-1)` and `m` are in `a7`,
`t1` and `t2` (`hbConsts`). `γ₂` is a public argument, a `u32` whose upper
half the calling convention leaves unspecified: the functions that take it
compare its low half with `(q - 1)/32` once (`gSel`, a `subw`), and branch to
one loop for each value.

* `power2Round(t = a0, t1 = a1, t0 = a2)`: `x = a + 4095` (`4095` in `t2`),
  `t1 = x >> 13` and `t0 = x - (t1 << 13) - 4095` (`(x mod 2¹³) - 4095`),
  plus `q` if negative.
* `highBits(r = a0, gamma2 = a1, out = a2)`: `r₁`.
* `lowBits(r = a0, gamma2 = a1, out = a2)`: `a - r₁ · 2γ₂`, plus `q` if
  negative (`a` kept in `t0`, `2γ₂` in `a1`).
* `normLt(f = a0, bound = a1)`: `bound` zero-extended; `a6` stays 1 while
  every coefficient `a` so far has `a < bound` or `q - a < bound` (two
  `sltu`s); it is the result.
* `makeHint(z = a0, r = a1, gamma2 = a2, h = a3)`: `r₁` of `r`, stored to
  `h[i]` and loaded back, and of `r + z mod q`, xored, is nonzero
  (`(x + 63) >> 6`, as `x < 64`) exactly when the hint is 1; `t4` counts
  the 1s.
* `useHint(h = a0, r = a1, gamma2 = a2, out = a3)`: `(f + m + δ) mod m`, for
  `δ` 0 if the hint is 0 and else `2s - 1`, with `s` 1 if `f · 2γ₂ < a`
  (`r₀ > 0`) and 0 otherwise: with `z` 1 if the hint is 0 (the sign of
  `h[i] - 1`), `f + δ = f + 2s - 2sz + z - 1`. It is in `[-1, m + 1]`, so
  `fixup` and then a conditional subtraction of `m` reduce it.

Every address and branch depends only on the pointers and `γ₂`.
-/

@[expose] public section

namespace VG.Impl.MlDsa.RISCV64.Round

open VG.RISCV64
open VG.Impl.MlKem.RISCV64 (fixup)
open VG.Impl.MlDsa.RISCV64.Arith (loadImm)

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

/-- `r ← q`. -/
def loadQ (r : Reg) : List Instr := loadImm r 8380417

/-- `a7 = M`, `t1 = 2^(S-1)`, `t2 = m`. -/
def hbConsts (g : Nat) : List Instr := loadImm .a7 (dMul g) ++ loadImm .t1 (dAdd g) ++ [.li .t2 (dMod g)]

/-- `d ← f` for `a = d`. -/
def hbRaw (g : Nat) (d : Reg) : List Instr :=
  [.addi d d 127, .shift .srl .d d d 7, .mul d d .a7, .add d d .t1, .shift .srl .d d d (dShift g)]

/-- `d ← r₁ = f mod m` for `a = d`, with `t` a temporary. -/
def hb (g : Nat) (d t : Reg) : List Instr := hbRaw g d ++ [.sub d d .t2] ++ fixup d t .t2

/-- `t0 ← γ₂ - (q - 1)/32` on the low halves, sign-extended, for `γ₂` in `r`,
through `a4`: zero exactly when `γ₂ = (q - 1)/32`. -/
def gSel (r : Reg) : List Instr := loadImm .a4 261888 ++ [.subw .t0 r .a4]

/-! ## `power2Round` -/

def p2rBody : List Instr :=
  [.load .w .a5 .a0 0, .add .a5 .a5 .t2, .shift .srl .d .a6 .a5 13, .store .w .a6 .a1 0,
    .shift .sll .d .a7 .a6 13, .sub .a5 .a5 .a7, .sub .a5 .a5 .t2] ++ fixup .a5 .a6 .a4 ++
  [.store .w .a5 .a2 0, .addi .a0 .a0 4, .addi .a1 .a1 4, .addi .a2 .a2 4, .addi .a3 .a3 (-1)]

def power2Round : Prog isa :=
  .seq (.block (.li .a3 256 :: loadQ .a4 ++ loadImm .t2 4095)) (.loop (.block p2rBody) (.nonzero .a3))

/-! ## `highBits` and `lowBits` -/

def hbBody (g : Nat) : List Instr :=
  [.load .w .a5 .a0 0] ++ hb g .a5 .a6 ++ [.store .w .a5 .a2 0, .addi .a0 .a0 4, .addi .a2 .a2 4,
    .addi .a3 .a3 (-1)]

def hbLoop (g : Nat) : Prog isa :=
  .seq (.block (hbConsts g ++ [.li .a3 256])) (.loop (.block (hbBody g)) (.nonzero .a3))

def highBits : Prog isa := .seq (.block (gSel .a1)) (.ite (.zero .t0) (hbLoop g32) (hbLoop g88))

def lbBody (g : Nat) : List Instr :=
  [.load .w .a5 .a0 0, .load .w .t0 .a0 0] ++ hb g .a5 .a6 ++ [.mul .a5 .a5 .a1, .sub .t0 .t0 .a5] ++
    fixup .t0 .a6 .a4 ++ [.store .w .t0 .a2 0, .addi .a0 .a0 4, .addi .a2 .a2 4, .addi .a3 .a3 (-1)]

def lbLoop (g : Nat) : Prog isa :=
  .seq (.block (hbConsts g ++ loadImm .a1 (2 * g) ++ loadQ .a4 ++ [.li .a3 256]))
    (.loop (.block (lbBody g)) (.nonzero .a3))

def lowBits : Prog isa := .seq (.block (gSel .a1)) (.ite (.zero .t0) (lbLoop g32) (lbLoop g88))

/-! ## `normLt` -/

def nlBody : List Instr :=
  [.load .w .t0 .a0 0, .sltu .t2 .t0 .a1, .sub .t3 .a2 .t0, .sltu .t3 .t3 .a1, .logic .or .t2 .t2 .t3,
    .logic .and .a6 .a6 .t2, .addi .a0 .a0 4, .addi .t1 .t1 (-1)]

def normLt : Prog isa :=
  .seq (.block ([.shift .sll .d .a1 .a1 32, .shift .srl .d .a1 .a1 32, .li .a6 1, .li .t1 256] ++ loadQ .a2))
    (.seq (.loop (.block nlBody) (.nonzero .t1)) (.block [.addi .a0 .a6 0]))

/-! ## `makeHint` and `useHint` -/

/-- `MakeHint` of `[a0]` and `[a1]` stored to `[a3]`, and counted in `t4`. -/
def mhBody (g : Nat) : List Instr :=
  [.load .w .a5 .a1 0] ++ hb g .a5 .a6 ++
  [.store .w .a5 .a3 0, .load .w .a5 .a1 0, .load .w .a6 .a0 0, .add .a5 .a5 .a6, .sub .a5 .a5 .a2] ++
    fixup .a5 .a6 .a2 ++ hb g .a5 .a6 ++
  [.load .w .a6 .a3 0, .logic .xor .a5 .a5 .a6, .addi .a5 .a5 63, .shift .srl .d .a5 .a5 6, .store .w .a5 .a3 0,
    .add .t4 .t4 .a5, .addi .a0 .a0 4, .addi .a1 .a1 4, .addi .a3 .a3 4, .addi .t3 .t3 (-1)]

def mhLoop (g : Nat) : Prog isa :=
  .seq (.block (hbConsts g ++ loadQ .a2 ++ [.li .t3 256, .li .t4 0]))
    (.seq (.loop (.block (mhBody g)) (.nonzero .t3)) (.block [.addi .a0 .t4 0]))

def makeHint : Prog isa := .seq (.block (gSel .a2)) (.ite (.zero .t0) (mhLoop g32) (mhLoop g88))

/-- `UseHint` of `[a0]` and `[a1]` stored to `[a3]`. -/
def uhBody (g : Nat) : List Instr :=
  [.load .w .a5 .a1 0, .load .w .a6 .a1 0] ++ hbRaw g .a6 ++
  [.mul .t0 .a6 .a2, .sub .t0 .t0 .a5, .shift .srl .d .t0 .t0 63, .shift .sll .d .t0 .t0 1,
    .load .w .a5 .a0 0, .addi .a5 .a5 (-1), .shift .srl .d .a5 .a5 63,
    .add .a6 .a6 .t0, .mul .t0 .t0 .a5, .sub .a6 .a6 .t0, .add .a6 .a6 .a5, .addi .a6 .a6 (-1)] ++
    fixup .a6 .a5 .t2 ++
  [.sub .a6 .a6 .t2] ++ fixup .a6 .a5 .t2 ++
  [.store .w .a6 .a3 0, .addi .a0 .a0 4, .addi .a1 .a1 4, .addi .a3 .a3 4, .addi .t3 .t3 (-1)]

def uhLoop (g : Nat) : Prog isa :=
  .seq (.block (hbConsts g ++ loadImm .a2 (2 * g) ++ [.li .t3 256])) (.loop (.block (uhBody g)) (.nonzero .t3))

def useHint : Prog isa := .seq (.block (gSel .a2)) (.ite (.zero .t0) (uhLoop g32) (uhLoop g88))

end VG.Impl.MlDsa.RISCV64.Round
