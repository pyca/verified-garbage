module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.Mont

/-!
# P-521's field on x86-64 with BMI2 and ADX: products by light calls, and fused linear steps

What the window method's doubling and mixed addition run (`WindowJF.lean`),
for P-521's `p = 2⁵²¹ - 1` in Montgomery's form (`R = 2⁵⁷⁶`):

* `vg_p521_sqr_adx`, `vg_p521_mul_adx` and `vg_p521_mulw_adx`: `[o] = [a] [b] R⁻¹`
  for `[a]`, `[b]` below `p`, called with `rbx = ws + a`, `rcx = ws + b`
  and `rsi = o` (`call`), keeping no register but `rdi`, `rsi` and `rsp`:
  the square by s2n-bignum's schedule (`sqrS`), the product by `mulPX`'s rows (`mulRows`), then
  `P R⁻¹ ≡ P_hi + (P_lo >> 55) + (P_lo mod 2⁵⁵) 2⁴⁶⁶` (`redS`, as
  `2⁵²¹ ≡ 1`), below `2p`, and `xCanon` (or, for `_mulw`, which only a
  `cms` reads, the number below `2p` as it is);
* `sAdd`, `sSub`: s2n-bignum's `add_p521` and `sub_p521`;
* `cmsF`: `C [a] - D [b] mod p` for the doubling's `4a - b`, `12a - 9b` and
  `3a - 8b`, `[a]` below `2⁵²²` and `[b]` below `p`: `C [a] + D (p - [b])`
  by shifts, `sbb` and `mulx`, then s2n-bignum's ending of `cmsub_p521`
  (`cmsTail`), which folds and reduces it in one carry chain.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.X86_64.P521F

open VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64
open VG.Impl.Weierstrass.X86_64.Mont (fnTmp fnMod)

/-- Word `k` of the functions' temporary area. -/
def T (k : Nat) : Nat := fnTmp + 8 * k

/-! ## The square's products

s2n-bignum's `bignum_sqr_p521`'s schedule, with the roles of the carries
swapped but in the top word's row: `[rbx]`'s words `0 … 7` squared, as the
products of two different words by rows, then doubled and the squares added,
then its top word's row. Word `w` of the products is in `q w` (eight
registers in turn, `r14` zero), words `0 … 7` stored once final. -/

/-- The registers of the square's words. -/
def QR : List Reg := [.rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r15]

/-- The register of word `w ≥ 1`. -/
def q (w : Nat) : Reg := QR.getD ((w + 7) % 8) .rbp

/-- The registers of words `w … w + n - 1`. -/
def qs (w n : Nat) : List Reg := (List.range n).map fun j => q (w + j)

/-- The word at `[rbx + d]`. -/
def asrc (d : Nat) : Src := .mem (rcR .rbx 0 d)

/-- `rdx · [d …]` along `ts`, each product's high half into the next register
(whatever it held) and its low half added through OF. -/
def mulAccsL : List Reg → Nat → List Instr
  | x :: y :: rest, d => [.mulx y .rax (asrc d), .adox x (.reg .rax)] ++ mulAccsL (y :: rest) (d + 8)
  | _, _ => []

/-- Row 0: `a_0 a_1 … a_0 a_7` at words `1 … 8` (one carry chain), words 1 and 2 stored. -/
def sqRow0 : List Instr :=
  [.alu32 .xor .r14 (.reg .r14), .mov .rdx (asrc 0), .mulx (q 2) (q 1) (asrc 8), .store (sc (T 1)) (q 1)] ++
  mulAccsL (qs 2 2) 16 ++ [.store (sc (T 2)) (q 2)] ++ mulAccsL (qs 3 6) 24 ++ [.adox (q 8) (.reg .r14)]

/-- `rdx · [d]` added at `x` (OF) and `y` (CF): `madd`, or, if `y` is
`fresh`, its high half into `y` (whatever it held) with CF. -/
def sqStep (fresh : Bool) (x y : Reg) (d : Nat) : List Instr :=
  if fresh then [.mulx y .rax (asrc d), .adox x (.reg .rax), .adcx y (.reg .r14)] else madd x y (asrc d)

/-- `n` products `rdx · [d …]` at words `w … w + n`, those from `w + f` fresh,
the first `st` words stored once final. -/
def sqChain : Nat → Nat → Nat → Nat → Nat → List Instr
  | 0, _, _, _, _ => []
  | n + 1, w, d, f, st => sqStep (f ≤ 1) (q w) (q (w + 1)) d ++
      (if 0 < st then [.store (sc (T w)) (q w)] else []) ++ sqChain n (w + 1) (d + 8) (f - 1) (st - 1)

/-- Row `r` of `1 … 3`: `a_r a_{r+1} … a_r a_7` at words `2r + 1 … r + 8`, then
`a_{r+4} a_4 … a_{r+4} a_{r+3}` at words `r + 8 … 2r + 8` (the products of
words `4 … 7`, s2n-bignum's), in one chain; words `2r + 1` and `2r + 2`
below 8 stored. -/
def sqRow (r : Nat) : List Instr :=
  [.alu32 .xor .r14 (.reg .r14), .mov .rdx (asrc (8 * r))] ++
  sqChain (7 - r) (2 * r + 1) (8 * (r + 1)) 6 (min 2 (7 - 2 * r)) ++
  [.mov .rdx (asrc (8 * (r + 4)))] ++ sqChain r (r + 8) 32 (r - 1) 0 ++ [.adox (q (2 * r + 8)) (.reg .r14)]

/-- Step `k` of `1 … 3` of the squares: words `2k` and `2k + 1` (in the
temporary area) doubled (OF) and `a_k²` added (CF). -/
def sqDiagM (k : Nat) : List Instr :=
  [.mov .rax (.mem (sc (T (2 * k)))), .mov .rdx (asrc (8 * k)), .mulx .rcx .rdx (.reg .rdx),
   .adox .rax (.reg .rax), .adcx .rax (.reg .rdx), .store (sc (T (2 * k))) .rax,
   .mov .rax (.mem (sc (T (2 * k + 1)))), .adox .rax (.reg .rax), .adcx .rax (.reg .rcx),
   .store (sc (T (2 * k + 1))) .rax]

/-- Step `k` of `4 … 6` of the squares: words `2k` and `2k + 1` (in their
registers) doubled (OF) and `a_k²` added (CF). -/
def sqDiagR (k : Nat) : List Instr :=
  [.mov .rdx (asrc (8 * k)), .mulx .rcx .rdx (.reg .rdx), .adox (q (2 * k)) (.reg (q (2 * k))),
   .adcx (q (2 * k)) (.reg .rdx), .adox (q (2 * k + 1)) (.reg (q (2 * k + 1))), .adcx (q (2 * k + 1)) (.reg .rcx)]

/-- Step 0 of the squares: word 0 is `a_0²`'s low half, word 1 doubled and its high half added. -/
def sqDiag0 : List Instr :=
  [.alu32 .xor .r14 (.reg .r14), .mov .rdx (asrc 0), .mulx .rcx .rax (.reg .rdx), .store (sc (T 0)) .rax,
   .mov .rax (.mem (sc (T 1))), .adox .rax (.reg .rax), .adcx .rax (.reg .rcx), .store (sc (T 1)) .rax]

/-- Step 7 of the squares: word 14 doubled and `a_7²`'s low half added, word 15
its high half and the carries. -/
def sqDiag7 : List Instr :=
  [.mov .rdx (asrc 56), .mulx (q 15) .rdx (.reg .rdx), .adox (q 14) (.reg (q 14)), .adcx (q 14) (.reg .rdx),
   .adcx (q 15) (.reg .r14), .adox (q 15) (.reg .r14)]

/-- The products doubled (OF) and the squares `a_k²` added (CF): words `0 … 7`
in the temporary area, `8 … 15` in their registers. -/
def sqDiag : List Instr :=
  sqDiag0 ++ sqDiagM 1 ++ sqDiagM 2 ++ sqDiagM 3 ++ sqDiagR 4 ++ sqDiagR 5 ++ sqDiagR 6 ++ sqDiag7

/-- `madd` with the carries' roles swapped: the low half through CF, the high through OF. -/
def maddM (x y : Reg) (src : Src) : List Instr := [.mulx .rcx .rax src, .adcx x (.reg .rax), .adox y (.reg .rcx)]

/-- `maddStepsC` (through `rbx`) by `maddM`. -/
def maddStepsM : Nat → List Reg → Nat → List Instr
  | k + 1, x :: y :: rest, d => maddM x y (asrc d) ++ maddStepsM k (y :: rest) (d + 8)
  | _, _, _ => []

/-- The top word's row: `a_8²` into word 16 (`imul`), `2 a_8 [a_0 … a_7]` at
words `8 … 16`. -/
def sqTop : List Instr :=
  [.mov .rdx (asrc 64), .mov .r14 (.reg .rdx), .imul .r14 .r14, .alu .add .rdx (.reg .rdx)] ++
  maddStepsM 8 [.r15, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14] 0 ++ [.alu .adc .r14 (.imm 0)]

/-- `[rbx]²`, its words `0 … 7` in the temporary area, `8` in `r15` and
`9 … 16` in `xAcc 9 … 16`. -/
def sqrS : List Instr := sqRow0 ++ sqRow 1 ++ sqRow 2 ++ sqRow 3 ++ sqDiag ++ sqTop

/-- `P R⁻¹` (plus one if `carry`) into `xWin 9`, for `P` with its words
`0 … 8` in the temporary area and `9 … 16` in `xAcc 9 … 16` (`17` zero):
`T = P_hi + (P₀ mod 2⁵⁵) 2⁴⁶⁶` (the two apart, `P` below `2¹⁰⁴²`), and
`q = P_lo >> 55` (by `shld`, word by word over the temporary area), added.
Each word is loaded again rather than copied between registers, which costs
an ALU port on cores without move elimination. -/
def redS (carry : Bool) : List Instr :=
  [.mov .rax (.mem (sc (T 0))), .mov .rcx (.mem (sc (T 0))), .shift .shl .rcx 18, .alu .or .r14 (.reg .rcx),
    .mov .r15 (.mem (sc (T 0))), .shift .shr .r15 46, .alu32 .and .r15 (.imm 511)] ++
  (List.range 8).flatMap (fun i => [.mov .rcx (.mem (sc (T (i + 1)))), .shld .rcx .rax 9,
    .store (sc (T i)) .rcx, .mov .rax (.mem (sc (T (i + 1))))]) ++
  [.shift .shr .rax 55] ++
  (if carry then [.alu32 .xor .rdx (.reg .rdx), .alu .cmp .rdx (.imm (-1))] else [.alu32 .xor .rdx (.reg .rdx)]) ++
  ((List.range 8).map fun i => .alu .adc (xAcc (9 + i)) (.mem (sc (T i)))) ++ [.alu .adc .r15 (.reg .rax)]

/-- The result, reduced below `p` (`xCanon`), at `[rdi + rsi]`. -/
def exitS : List Instr := [.alu .add .rdi (.reg .rsi)] ++ xCanon 0 0 ++ [.alu .sub .rdi (.reg .rsi)]

/-- The result, below `2p`, at `[rdi + rsi]`. -/
def exitW : List Instr := [.alu .add .rdi (.reg .rsi)] ++ storesC 0 (xWin 9) 0 ++ [.alu .sub .rdi (.reg .rsi)]

/-- The word at `[rsi + d]`: the second factor's, in the products. -/
def bsrc (d : Nat) : Src := .mem (rcR .rsi 0 d)

/-- `maddStepsM` through the register `r`. -/
def maddStepsMR (r : Reg) : Nat → List Reg → Nat → List Instr
  | k + 1, x :: y :: rest, d => maddM x y (.mem (rcR r 0 d)) ++ maddStepsMR r k (y :: rest) (d + 8)
  | _, _, _ => []

/-- Row 0 of the product, s2n-bignum's `bignum_mul_p521`'s: `b_0 [a_0 … a_7]`
at the words `0 … 8` (one carry chain), word 0 stored. -/
def prodRow0 : List Instr :=
  [.alu32 .xor .r14 (.reg .r14), .mov .rdx (bsrc 0), .mulx (q 1) .rax (asrc 0), .store (sc (T 0)) .rax] ++
  mulAccsL (qs 1 8) 8 ++ [.adox (q 8) (.reg .r14)]

/-- Row `i` of `1 … 7`: `b_i [a_0 … a_7]` added at the words `i … i + 8`, the
top one fresh in the register of word `i`, which is stored once final. -/
def prodRow (i : Nat) : List Instr :=
  [.alu32 .xor .r14 (.reg .r14), .mov .rdx (bsrc (8 * i))] ++ sqChain 7 i 0 8 1 ++ sqChain 1 (i + 7) 56 0 0 ++
  [.adox (q (i + 8)) (.reg .r14)]

/-- The top words' rows: `a_8 b_8` at word 16, `b_8 [a_0 … a_7]` and
`a_8 [b_0 … b_7]` at word 8, added to the words `8 … 15`. -/
def prodTop : List Instr :=
  [.mov .rdx (bsrc 64), .mov .r14 (asrc 64), .imul .r14 .rdx, .alu32 .xor .rax (.reg .rax)] ++
  maddStepsM 8 [.r15, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14] 0 ++ [.alu .adc .r14 (.imm 0)] ++
  [.mov .rdx (asrc 64), .alu32 .xor .rax (.reg .rax)] ++
  maddStepsMR .rsi 8 [.r15, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14] 0 ++ [.alu .adc .r14 (.imm 0)]

/-- `[rbx] [rcx]` as `sqrS` leaves a square: its words `0 … 7` in the
temporary area, `8` in `r15` and `9 … 16` in `xAcc 9 … 16`; `[rcx]` read
through `rsi`, the output's offset kept in `xmm13` meanwhile. -/
def mulS : List Instr :=
  [.xop (.movq .xmm13 .rsi), .mov .rsi (.reg .rcx)] ++ prodRow0 ++ (List.range 7).flatMap (fun i => prodRow (i + 1)) ++
    prodTop ++ [.movqR .rsi .xmm13]

/-- `vg_p521_sqr_adx`. -/
def sqrFn : Prog isa := .block (sqrS ++ [.store (sc (T 8)) .r15] ++ redS true ++ exitS)

/-- `vg_p521_mul_adx`. -/
def mulFn : Prog isa := .block (mulS ++ [.store (sc (T 8)) .r15] ++ redS true ++ exitS)

/-- `vg_p521_mulw_adx`. -/
def mulFnW : Prog isa := .block (mulS ++ [.store (sc (T 8)) .r15] ++ redS false ++ exitW)

/-- A call's arguments: `rbx = ws + a`, `rcx = ws + b`, `rsi = o`. -/
def args (o a b : Nat) : List Instr :=
  [.mov .rbx (.reg .rdi), .alu .add .rbx (.imm (BitVec.ofNat 32 a)), .mov .rcx (.reg .rdi),
    .alu .add .rcx (.imm (BitVec.ofNat 32 b)), .mov32 .rsi (.imm (BitVec.ofNat 32 o))]

/-- `[o] = [a] [b] R⁻¹` by a call: of the square if `a = b`, else of the
product, below `2p` only if `weak`. -/
def pmul (weak : Bool) (o a b : Nat) : Prog isa :=
  .seq (.block (args o a b)) (if a = b then .call "vg_p521_sqr_adx" sqrFn
    else if weak then .call "vg_p521_mulw_adx" mulFnW else .call "vg_p521_mul_adx" mulFn)

/-! ## Additions and subtractions -/

/-- The words of `sAdd`. -/
def AW : List Reg := [.rax, .rbx, .r8, .r9, .r10, .r11, .r12, .r13, .r14]

/-- The words of `sSub`. -/
def SW : List Reg := [.rax, .rdx, .r8, .r9, .r10, .r11, .r12, .r13, .r14]

/-- `t_k = [a + 8k] op [b + 8k]` along `ts`, `op` for the first word and `op'` after. -/
def ldOp (op op' : AluOp) : List Reg → Nat → Nat → List Instr
  | [], _, _ => []
  | t :: ts, a, b => [.mov t (.mem (sc a)), .alu op t (.mem (sc b))] ++ ldOp op' op' ts (a + 8) (b + 8)

/-- The borrow taken from `ts`, each word stored at `[o + 8k]` once final. -/
def sbbSt : List Reg → Nat → List Instr
  | [], _ => []
  | t :: ts, o => [.alu .sbb t (.imm 0), .store (sc o) t] ++ sbbSt ts (o + 8)

/-- s2n-bignum's `add_p521`, `[o] = [a] + [b] mod p` for `[a] + [b] < 2p`:
`[a] + [b] + 1`, then the one taken back unless its bit 521 is set, which is
cleared. -/
def sAdd (o a b : Nat) : List Instr :=
  [.alu32 .xor .rdx (.reg .rdx), .alu .cmp .rdx (.imm (-1))] ++ ldOp .adc .adc AW a b ++
  [.mov32 .rdx (.imm 512), .alu .and .rdx (.reg .r14), .alu .cmp .rdx (.imm 512)] ++
  sbbSt (AW.take 8) o ++ [.alu .sbb .r14 (.reg .rdx), .store (sc (o + 64)) .r14]

/-- s2n-bignum's `sub_p521`, `[o] = [a] - [b] mod p` for `[a]`, `[b]` below `p`:
`[a] - [b]`, and on a borrow one more taken and its bits from 521 cleared,
which adds `p`. -/
def sSub (o a b : Nat) : List Instr :=
  ldOp .sub .sbb SW a b ++ sbbSt (SW.take 8) o ++
  [.alu .sbb .r14 (.imm 0), .alu .and .r14 (.imm 511), .store (sc (o + 64)) .r14]

/-! ## `C [a] - D [b]` -/

/-- The words of `cmsF`'s accumulator `N`: `r8 … r15`, `rbx` (s2n-bignum's). -/
def CW : List Reg := [.r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15, .rbx]

/-- `N`'s words from the top down. -/
def CWr : List Reg := [.rbx, .r15, .r14, .r13, .r12, .r11, .r10, .r9, .r8]

/-- The words `ts` (from the top down) shifted left by `n`, each `shld` by
the word below. -/
def shlChain : List Reg → Nat → List Instr
  | [], _ => []
  | [t], n => [.shift .shl t n]
  | t :: u :: rest, n => .shld t u n :: shlChain (u :: rest) n

/-- `N = [a] 2^s`, by `shld` from the top word down. -/
def loadShl (a s : Nat) : List Instr := loads CW a ++ shlChain CWr s

/-- The words of `p - [b]`: `[b]`'s words complemented, the last one's nine bits. -/
def negLoads : List Reg → Nat → List Instr
  | [], _ => []
  | [t], b => [.mov t (.mem (sc b)), .alu .xor t (.imm 511)]
  | t :: u :: rest, b => [.mov t (.mem (sc b)), .alu .xor t (.imm (BitVec.ofInt 32 (-1)))] ++
      negLoads (u :: rest) (b + 8)

/-- `N = (p - [b]) 2^s`: `[b]`'s words complemented (its top word's nine bits),
then shifted. -/
def loadNegShl (b s : Nat) : List Instr := negLoads CW b ++ shlChain CWr s

/-- `N += p - [b]`: `[b] + 1` subtracted (`sbb`, CF set first), and `2⁵²¹` added. -/
def addNeg (b : Nat) : List Instr :=
  [.alu32 .xor .rax (.reg .rax), .alu .cmp .rax (.imm (-1))] ++ chain .sbb .sbb CW b ++
    [.alu .add .rbx (.imm 512)]

/-- `k` products `rdx · [d]`, `rdx · [d + 8]`, … added along the words `ts`
(`maddM`, the low halves through CF). -/
def maddStepsS : Nat → List Reg → Nat → List Instr
  | k + 1, x :: y :: rest, d => maddM x y (.mem (sc d)) ++ maddStepsS k (y :: rest) (d + 8)
  | _, _, _ => []

/-- `N += C [a]` by `mulx` (`rdx = C`), both carry chains. -/
def addMulC (C a : Nat) : List Instr :=
  [.alu32 .xor .rax (.reg .rax), .mov32 .rdx (.imm (BitVec.ofNat 32 C))] ++ maddStepsS 8 CW a ++
    [.mulx .rcx .rax (.mem (sc (a + 64))), .adcx .rbx (.reg .rax)]

/-- The carry `rcx` (zero) added along `ts`, each word stored at `[o + 8k]`. -/
def adcSt : List Reg → Nat → List Instr
  | [], _ => []
  | t :: ts, o => [.alu .adc t (.reg .rcx), .store (sc o) t] ++ adcSt ts (o + 8)

/-- `cmsTail`'s first part: whether `L + h + 1` reaches `2⁵²¹`, in CF, `h` in
`rdx`, `rcx = 0` and the top word's bits from 9 set. -/
def cmsCarry : List Instr :=
  [.mov .rax (.reg .r9)] ++ ([.r10, .r11, .r12, .r13, .r14, .r15].map fun r => .alu .and .rax (.reg r)) ++
  [.mov .rdx (.reg .rbx), .shift .shr .rdx 9, .alu .or .rbx (.imm (BitVec.ofInt 32 (-512))),
   .mov .rcx (.reg .rdx), .alu .add .rcx (.imm 1), .alu .add .rcx (.reg .r8), .mov32 .rcx (.imm 0),
   .alu .adc .rax (.reg .rcx), .mov .rax (.reg .rbx), .alu .adc .rax (.reg .rcx)]

/-- s2n-bignum's ending of `cmsub_p521`: `N` below `2⁵⁷⁶` as `L + 2⁵²¹ h`
(`L` its low 521 bits) to `[o] = (L + h) mod p`. Whether `L + h + 1` reaches
`2⁵²¹` (so `L + h ≥ p`) is found first, from word 0's carry, the `and` of
words `1 … 7` and the top word with its bits from 9 set, so that one chain
adds `h` and that carry and the bits from 521 are cleared. -/
def cmsTail (o : Nat) : List Instr :=
  cmsCarry ++ [.alu .adc .r8 (.reg .rdx), .store (sc o) .r8] ++ adcSt (CW.drop 1 |>.take 7) (o + 8) ++
  [.alu .adc .rbx (.reg .rcx), .alu .and .rbx (.imm 511), .store (sc (o + 64)) .rbx]

/-- `[o] = (C [a] - D [b]) mod p` for the doubling's three: `4a - b` (`D = 1`),
`12a - 9b` (`D = 9`) and `3a - 8b` (otherwise). -/
def cmsF (o C a D b : Nat) : List Instr :=
  if D = 1 then loadShl a 2 ++ addNeg b ++ cmsTail o
  else if D = 9 then loadNegShl b 3 ++ addNeg b ++ addMulC C a ++ cmsTail o
  else loadNegShl b 3 ++ addMulC C a ++ cmsTail o

end VG.Impl.Weierstrass.X86_64.P521F
