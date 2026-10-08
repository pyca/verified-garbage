import VerifiedGarbage.Impl.Mont.X86_64
import VerifiedGarbage.Spec.Weierstrass.Mont

/-!
# Montgomery products modulo P-521's `p`, as functions, on x86-64

`vg_p521_mul_mod_p(ws, o, a, b)` and `vg_p521_mul_mod_p_adx`
(`Spec/Weierstrass/Mont.lean`; System V: `ws` in `rdi`, the offsets `o`,
`a` and `b` in `esi`, `edx` and `ecx`): the inline products of
`Impl/Mont/X86_64.lean` with their operands read through registers.
-/

namespace VG.Impl.Weierstrass.X86_64.Mont

open VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64

/-- The temporary area of the function's products: the last nine words
below byte 4096. -/
def fnTmp : Nat := 4096 - 72

/-- The callee-saved registers the function writes, which it keeps in
`xmm0`–`xmm5`, in that order. -/
def saved : List Reg := [.rbx, .rbp, .r12, .r13, .r14, .r15]

/-- P-521's `p` as the function takes it. -/
def fnMod (adx : Bool) : Mod where
  n := 9
  mo := 0
  tmp := fnTmp
  minv := BitVec.ofNat 64 1
  red := .friendly p521Ws
  adx := adx

/-- The offsets zero-extended. -/
def zext : List Instr := [.mov32 .rsi (.reg .rsi), .mov32 .rdx (.reg .rdx), .mov32 .rcx (.reg .rcx)]

/-- The callee-saved registers into `xmm0`–`xmm5`. -/
def saves : List Instr :=
  [.xop (.movq .xmm0 .rbx), .xop (.movq .xmm1 .rbp), .xop (.movq .xmm2 .r12),
    .xop (.movq .xmm3 .r13), .xop (.movq .xmm4 .r14), .xop (.movq .xmm5 .r15)]

/-- The callee-saved registers back from `xmm0`–`xmm5`. -/
def restores : List Instr :=
  [.movqR .rbx .xmm0, .movqR .rbp .xmm1, .movqR .r12 .xmm2, .movqR .r13 .xmm3, .movqR .r14 .xmm4,
    .movqR .r15 .xmm5]

/-- The registers saved, `rbx = ws + a`, `rcx = ws + b`, and ZF set iff
`a = b`; `o` stays in `rsi` throughout. -/
def setup : List Instr :=
  saves ++ [.mov .rbx (.reg .rdx), .alu .add .rbx (.reg .rdi), .alu .add .rcx (.reg .rdi),
    .alu .cmp .rbx (.reg .rcx)]

/-- Words `i … i + k - 1` of `[a]` (through `rbx`) into the temporary area,
through `rax`. -/
def copyW : Nat → Nat → List Instr
  | 0, _ => []
  | k + 1, i => [.mov .rax (.mem (rcR .rbx 0 (8 * i))), .store (sc (fnTmp + 8 * i)) .rax] ++ copyW k (i + 1)

/-- The product by rows: `[a]` copied into the temporary area, where row `i`
reads `a_i` before it stores its low word over it, `rbx = ws + b`, the rows
into the temporary area and `xWin 9`, then the reduction. -/
def mulX : List Instr :=
  copyW 9 0 ++ [.mov .rbx (.reg .rcx)] ++ (List.range 9).flatMap (xRowV (fnMod true) .rdi .rbx 0 fnTmp 0) ++
    xRed (fnMod true) 0

/-- The square and its reduction, `[a]` through `rbx`. -/
def sqrCore : List Instr :=
  (List.range 8).flatMap (sRowV (fnMod true) .rbx 0 0) ++ sDiag (fnMod true) .rbx 0 0 ++
    xRed (fnMod true) 0

/-- The square. -/
def sqrX : List Instr := sqrCore

/-- From `o` in `rsi`: `rdi = ws + o`, the result reduced and stored there,
`rdi = ws`, the registers restored from `xmm0`–`xmm5`. -/
def exit : List Instr :=
  [.alu .add .rdi (.reg .rsi)] ++ xCanon 0 0 ++ [.alu .sub .rdi (.reg .rsi)] ++ restores

/-- `vg_p521_mul_mod_p_adx`. -/
def mulFnX : Prog isa :=
  .seq (.block zext) (.seq (.block setup) (.seq (.ite .e (.block sqrX) (.block mulX)) (.block exit)))

/-! ## Without BMI2 and ADX: the product by columns

The columns of `mulP` and `sqrP` (`Impl/Mont/X86_64.lean`), their operands
read through `rbx = ws + a` and `rbp = ws + b`; the result plus one then into
`xWin 9`, for `exit`. -/

/-- `[a + 8 i]`, through `rbx`. -/
def opA (i : Nat) : MemOp := rcR .rbx 0 (8 * i)

/-- `[b + 8 j]`, through `rbp`. -/
def opB (j : Nat) : MemOp := rcR .rbp 0 (8 * j)

/-- `mx · sy` added to the accumulator of column `c`, `sy` into `rcx` and
`[mx]` into `rax` (`pTerm` with its operands given). -/
def termR (c : Nat) (mx : MemOp) (sy : Src) : List Instr :=
  [.mov .rcx sy, .mov .rax (.mem mx), .mul .rcx, .alu .add (pAcc c 0) (.reg .rax),
    .alu .adc (pAcc c 1) (.reg .rdx), .alu .adc (pAcc c 2) (.imm 0)]

/-- `termR`, the product added twice if `two` (`sTerm`). -/
def termR2 (c : Nat) (mx : MemOp) (sy : Src) (two : Bool) : List Instr :=
  termR c mx sy ++ if two then [.alu .add (pAcc c 0) (.reg .rax), .alu .adc (pAcc c 1) (.reg .rdx),
    .alu .adc (pAcc c 2) (.imm 0)] else []

/-- The reduction's term of column `c`: `512 u_{c-8}`, for `8 ≤ c ≤ 16`. -/
def redTerms (c : Nat) : List (MemOp × Src × Bool) :=
  if 8 ≤ c ∧ c ≤ 16 then [(sc (fnTmp + 8 * (c - 8)), .imm 512, false)] else []

/-- The terms of column `c` of the product (`pTerms`). -/
def mulTerms (c : Nat) : List (MemOp × Src × Bool) :=
  ((List.range 9).filter fun i => i ≤ c ∧ c - i < 9).map (fun i => (opA i, .mem (opB (c - i)), false)) ++
    redTerms c

/-- The terms of column `c` of the square (`sTerms`). -/
def sqrTerms (c : Nat) : List (MemOp × Src × Bool) :=
  ((List.range 9).filter fun i => 2 * i < c ∧ c - i < 9).map (fun i => (opA i, .mem (opA (c - i)), true)) ++
    (if c % 2 = 0 ∧ c / 2 < 9 then [(opA (c / 2), .mem (opA (c / 2)), false)] else []) ++ redTerms c

/-- Column `c`: its terms, then its low word stored at `[fnTmp + 8 (c mod 9)]`
and cleared. -/
def colR (ts : Nat → List (MemOp × Src × Bool)) (c : Nat) : List Instr :=
  (ts c).flatMap (fun t => termR2 c t.1 t.2.1 t.2.2) ++
    [.store (sc (fnTmp + 8 * (c % 9))) (pAcc c 0), .mov32 (pAcc c 0) (.imm 0)]

/-- The accumulator cleared, then the eighteen columns. -/
def colsR (ts : Nat → List (MemOp × Src × Bool)) : List Instr :=
  [.mov32 .r9 (.imm 0), .mov32 .r10 (.imm 0), .mov32 .r11 (.imm 0)] ++ (List.range 18).flatMap (colR ts)

/-- The result `S`, in the temporary area, plus one into `xWin 9`: what
`xCanon` takes. -/
def plusOne : List Instr :=
  loads (xWin 9) fnTmp ++ [.alu .add (xAcc 9) (.imm 1)] ++
    (List.range 8).map (fun k => .alu .adc (xAcc (10 + k)) (.imm 0))

/-- The columns, from `rbx = ws + a` and `rbp = ws + b`. -/
def colsO (ts : Nat → List (MemOp × Src × Bool)) : List Instr := [.mov .rbp (.reg .rcx)] ++ colsR ts

/-- `vg_p521_mul_mod_p`. -/
def mulFn : Prog isa :=
  .seq (.block zext) (.seq (.block setup)
    (.seq (.seq (.ite .e (.block (colsO sqrTerms)) (.block (colsO mulTerms))) (.block plusOne)) (.block exit)))

/-- A call of `f`, whose code is `body`: `rsi`, which the function changes,
kept in `r12`, which it does not, and the offsets into `esi`, `edx` and
`ecx`. -/
def mulCall (f : String) (body : Prog isa) (o a b : Nat) : Prog isa :=
  .seq (.block [.mov .r12 (.reg .rsi), .mov32 .rsi (.imm (BitVec.ofNat 32 o)),
      .mov32 .rdx (.imm (BitVec.ofNat 32 a)), .mov32 .rcx (.imm (BitVec.ofNat 32 b))])
    (.seq (.call f body) (.block [.mov .rsi (.reg .r12)]))

/-- The function the products modulo `M` call, and its code: P-521's `p`, with
the temporary area the functions' (`fnTmp`), with or without BMI2 and ADX;
none for any other modulus. -/
def callOf (M : Mod) : Option (String × Prog isa) :=
  if M.n = 9 ∧ M.red = .friendly p521Ws ∧ M.tmp = fnTmp then
    some (if M.adx then (Spec.Weierstrass.Mont.p521p.mulApi.name ++ "_adx", mulFnX)
      else (Spec.Weierstrass.Mont.p521p.mulApi.name, mulFn))
  else none

/-- Whether a product's offsets lie below the functions' own working space, as
their arguments must. -/
def lowArgs (o a b : Nat) : Bool := o + 72 ≤ 3520 && a + 72 ≤ 3520 && b + 72 ≤ 3520

end VG.Impl.Weierstrass.X86_64.Mont
