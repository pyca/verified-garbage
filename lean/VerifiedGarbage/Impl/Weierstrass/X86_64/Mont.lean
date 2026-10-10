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

/-! ## P-384's `p`: the inline product, relocated

`vg_p384_mul_mod_p(ws, o, a, b)` and `vg_p384_mul_mod_p_adx` run the inline
products of `Impl/Mont/X86_64.lean` for P-384's `p` (`mulRounds`, `sqrSA`),
which use every register but `rbx`, `rsi`, `rdi` and `rsp`, with their
operands read through registers: the inline code, made at the offsets `mA`,
`mB` and `mO` (markers, which no operand may be at), with each operand at a
marker moved to a register (`relocTo`), `[a]` through `rbx = ws + a`, `[b]`
through `rsi = ws + b` and `[o]` through `rsi = ws + o` (`o` kept in `xmm6`
meanwhile, for a product); the temporary area stays at `rdi = ws`. The
final reduction is `csubR`, which builds `p` in registers, as the function
has no modulus in memory. -/

/-- The temporary area of the function's products: the last six words below
byte 4096. -/
def fnTmp6 : Nat := 4096 - 48

/-- P-384's `p` as the function takes it. -/
def fnMod6 (adx : Bool) : Mod where
  n := 6
  mo := 0
  tmp := fnTmp6
  minv := BitVec.ofNat 64 0x100000001
  adx := adx
  sparse := true

/-- The memory operand with `f` applied to its memory operand, if any. -/
def _root_.VG.X86_64.Src.mapMem (f : MemOp → MemOp) : Src → Src
  | .mem m => .mem (f m)
  | s => s

/-- The instruction with `f` applied to its memory operand (those of the
integer instructions). -/
def _root_.VG.X86_64.Instr.mapMem (f : MemOp → MemOp) : Instr → Instr
  | .mov d s => .mov d (s.mapMem f)
  | .mov32 d s => .mov32 d (s.mapMem f)
  | .store m r => .store (f m) r
  | .store32 m r => .store32 (f m) r
  | .store8 m r => .store8 (f m) r
  | .alu op d s => .alu op d (s.mapMem f)
  | .alu32 op d s => .alu32 op d (s.mapMem f)
  | .movzx8 d m => .movzx8 d (f m)
  | .mulx hi lo s => .mulx hi lo (s.mapMem f)
  | .adcx d s => .adcx d (s.mapMem f)
  | .adox d s => .adox d (s.mapMem f)
  | .cmov c d s => .cmov c d (s.mapMem f)
  | i => i

/-- The markers: where the inline code the function runs has `[a]`, `[b]`
and `[o]`. -/
def mA : Nat := 1048576
def mB : Nat := 2097152
def mO : Nat := 4194304

/-- An operand `[rdi + d]` with `d` within 4096 bytes past a marker `V`
of `ps`, through that marker's register instead: `[r + d - V]`. -/
def relocTo (ps : List (Nat × Reg)) (m : MemOp) : MemOp :=
  match m.index, ps.find? (fun p => decide ((p.1 : Int) ≤ m.disp ∧ m.disp < p.1 + 4096)) with
  | none, some p => if m.base = .rdi then { m with base := p.2, disp := m.disp - p.1 } else m
  | _, _ => m

/-- Code with its operands at the markers `ps` relocated. -/
def reloc (ps : List (Nat × Reg)) (is : List Instr) : List Instr := is.map (Instr.mapMem (relocTo ps))

/-- The low words and the top word of the product's accumulator. -/
def low6 : List Reg := (List.range 6).map (win 6 6)
def top6 : Reg := win 6 6 6

/-- The square: `rsi = ws + o`, `sqrSA` with `[a]` through `rbx` and `[o]`
through `rsi`, `csubR`, and the result stored through `rsi`. -/
def sqr6 (adx : Bool) : List Instr :=
  [.alu .add .rsi (.reg .rdi)] ++ reloc [(mA, .rbx), (mO, .rsi)] (sqrSA (fnMod6 adx) mO mA) ++
    csubR sqWin6 .r8 ++ reloc [(mO, .rsi)] (stores sqWin6 mO)

/-- The product: `o` into `xmm6` and `rsi = ws + b`, `mulRounds` with `[a]`
through `rbx` and `[b]` through `rsi`, `csubR`, then `rsi = ws + o` and the
result stored through it. -/
def mul6 (adx : Bool) : List Instr :=
  [.xop (.movq .xmm6 .rsi), .mov .rsi (.reg .rcx)] ++ reloc [(mA, .rbx), (mB, .rsi)] (mulRounds (fnMod6 adx) mA mB) ++
    csubR low6 top6 ++ [.movqR .rsi .xmm6, .alu .add .rsi (.reg .rdi)] ++ reloc [(mO, .rsi)] (stores low6 mO)

/-- `vg_p384_mul_mod_p` (`adx` false) and `vg_p384_mul_mod_p_adx`. -/
def mulFn6 (adx : Bool) : Prog isa :=
  .seq (.block zext) (.seq (.block setup) (.seq (.ite .e (.block (sqr6 adx)) (.block (mul6 adx))) (.block restores)))

/-- The function the products modulo `M` call, and its code: P-521's `p`, with
the temporary area the functions' (`fnTmp`), or P-384's (`fnTmp6`) unless its
products are written out (`Mod.inl`), with or without BMI2 and ADX; none for
any other modulus. -/
def callOf (M : Mod) : Option (String × Prog isa) :=
  if M.n = 9 ∧ M.red = .friendly p521Ws ∧ M.tmp = fnTmp then
    some (if M.adx then (Spec.Weierstrass.Mont.p521p.mulApi.name ++ "_adx", mulFnX)
      else (Spec.Weierstrass.Mont.p521p.mulApi.name, mulFn))
  else if M.n = 6 ∧ M.sparse ∧ M.tmp = fnTmp6 ∧ M.inl = false then
    some (if M.adx then (Spec.Weierstrass.Mont.p384p.mulApi.name ++ "_adx", mulFn6 true)
      else (Spec.Weierstrass.Mont.p384p.mulApi.name, mulFn6 false))
  else none

/-- Whether a product's offsets suit the functions of `n` words: below their
own working space for nine words; for six, apart from their temporary area
and within an immediate's reach. -/
def lowArgs (n o a b : Nat) : Bool :=
  if n = 9 then o + 72 ≤ 3520 && a + 72 ≤ 3520 && b + 72 ≤ 3520
  else (o + 48 ≤ fnTmp6 || 4096 ≤ o && o < 2 ^ 31) && (a + 48 ≤ fnTmp6 || 4096 ≤ a && a < 2 ^ 31) &&
    (b + 48 ≤ fnTmp6 || 4096 ≤ b && b < 2 ^ 31)

end VG.Impl.Weierstrass.X86_64.Mont
