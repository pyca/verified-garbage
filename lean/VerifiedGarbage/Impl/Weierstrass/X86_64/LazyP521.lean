module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.Window

/-!
# P-521 on x86-64 with BMI2 and ADX: Jacobian doublings with lazy reduction

`p = 2⁵²¹ - 1` and nine words hold 576 bits, so a sum of a few numbers below
`p` fits nine words with no reduction, and the product 
is right for operands `A`, `B` with `A B < 2⁵⁷⁶ p`. So the linear operations
between products (`LOp`) reduce nothing, or only fold the bits above 521
(`fold`): a number here is at most `k p` for a small `k`, which `check` bounds
slot by slot, and `0` in a product's result stands for "below `p`".

* `p - b` is the complement of `b ≤ p` in 521 bits: each word is complemented,
  before the carry chain, and 512 added to the top word at the end.
* `fold`: for a number below `4p`, its bits above 521 (at most 3) added to the
  rest: at most `p + 3`; the bit 521 that this may set goes into word 0 without
  a chain, as the words are then below 3.

The doubling (`dblOps`) of `(X : Y : Z)` keeps `H = 2Y` in place of `Y`:
`G = H²`, `S = X G`, `M = 3 (X - Z²)(X + Z²)`, `X₃ = M² - 2S`, `Z₃ = H Z`,
`H₃ = 2 Y₃ = 2M (S - X₃) - G²`: four squares, four products. Its operations
are in the order measured fastest of a search over their orders. The products'
results are below `p`, so `Z` always is; `X` and `H` are at most `p`, until
`quadLazy`'s end, which makes `X` canonical and `Y = H/2` (`half`).
-/

@[expose] public section

namespace VG.Impl.Weierstrass.X86_64.LazyP521

open VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass

/-- The nine registers of a number, and its top and low words. -/
abbrev regs : List Reg := xWin 9
abbrev topR : Reg := xAcc 17
abbrev lowR : Reg := xAcc 9

/-- The registers complemented. -/
def nots : List Instr := regs.map fun t => .alu .xor t (.imm (-1))

/-- The carry added along registers. -/
def adcs (ts : List Reg) : List Instr := ts.map fun t => .alu .adc t (.imm 0)

/-- The bits above 521 of the top word into `rax`, taken off, and added to the
low word. -/
def foldHi : List Instr :=
  [.mov .rax (.reg topR), .shift .shr .rax 9, .alu .and topR (.imm 511), .alu .add lowR (.reg .rax)]

/-- A number below `4p` in the registers to one at most `p`. -/
def fold : List Instr := foldHi ++ adcs ((List.range 8).map fun k => xAcc (10 + k)) ++ foldHi

/-- A linear operation, or a product. -/
inductive LOp where
  /-- `[o] = [a] [b] 2⁻⁵⁷⁶ mod p`, below `p`. -/
  | mul (o a b : Nat)
  /-- `[o] = [a] + [b]`. -/
  | add (o a b : Nat)
  /-- `[o] = [a] + (p - [b])`. -/
  | sub (o a b : Nat)
  /-- `[o] = 3 [a]`. -/
  | tri (o a : Nat)
  /-- `[o] = [a] + 2 (p - [b])`, folded. -/
  | sub2 (o a b : Nat)
  /-- `[o] = [a] + (p - [b])`, folded. -/
  | subF (o a b : Nat)
  /-- `[o] = [a] / 2 mod p`. -/
  | half (o a : Nat)
  /-- `[o] = [a] + [b] mod p`, below `p`. -/
  | cadd (o a b : Nat)
  /-- `[o] = [a] - [b] mod p`, below `p`. -/
  | csub (o a b : Nat)

/-- `p - [b]` in the registers but for `512` in the top word, then `[a]` added. -/
def subs (a b : Nat) : List Instr := loadsC 0 regs b ++ nots ++ chainC 0 .add .adc regs a

/-- The registers of `half`'s result. -/
def halfRegs : List Reg := (List.range 8).map (fun k => xAcc (10 + k)) ++ [.rcx]

/-- The registers' 521 bits rotated right by one, into `halfRegs`. -/
def rot : List Instr :=
  [.mov .rax (.reg lowR), .alu .and .rax (.imm 1), .shift .shl .rax 8, .mov .rcx (.reg topR),
    .shift .shr .rcx 1, .alu .add .rcx (.reg .rax),
    .shld (xAcc 17) (xAcc 16) 63, .shld (xAcc 16) (xAcc 15) 63, .shld (xAcc 15) (xAcc 14) 63,
    .shld (xAcc 14) (xAcc 13) 63, .shld (xAcc 13) (xAcc 12) 63, .shld (xAcc 12) (xAcc 11) 63,
    .shld (xAcc 11) (xAcc 10) 63, .shld (xAcc 10) (xAcc 9) 63]

/-! ## The products

`vg_p521_win_sqr_adx` and `vg_p521_win_mul_adx` take pointers to the operands
(`rbx`; `rsi` and `rbx`), read in place, and leave the result plus one in the
registers, which the call site makes canonical and stores. They save nothing:
the call site keeps `rbx` in `xmm7` and `rsi` in `xmm6`. -/

/-- The square of the number `rbx` points to. -/
def sqrFn : Prog isa := .block Mont.sqrCore

/-- The product of the numbers `rsi` and `rbx` point to. -/
def mulFn : Prog isa :=
  .block ((List.range 9).flatMap (xRowV (Mont.fnMod true) .rsi .rbx 0 0 0) ++ xRed (Mont.fnMod true) 0)

/-- `r = rdi + a`. -/
def ptr (r : Reg) (a : Nat) : List Instr := [.mov r (.reg .rdi), .alu .add r (.imm (BitVec.ofNat 32 a))]

/-- `[o] = [a]² 2⁻⁵⁷⁶ mod p`. -/
def sqrCall (o a : Nat) : Prog isa :=
  .seq (.block (([.xop (.movq .xmm7 .rbx)] : List Instr) ++ ptr .rbx a)) <|
  .seq (.call "vg_p521_win_sqr_adx" sqrFn) (.block (xCanon 0 o ++ ([.movqR .rbx .xmm7] : List Instr)))

/-- `[o] = [a] [b] 2⁻⁵⁷⁶ mod p`. -/
def mulCall (o a b : Nat) : Prog isa :=
  .seq (.block (([.xop (.movq .xmm7 .rbx), .xop (.movq .xmm6 .rsi)] : List Instr) ++ ptr .rsi a ++ ptr .rbx b)) <|
  .seq (.call "vg_p521_win_mul_adx" mulFn)
    (.block (xCanon 0 o ++ ([.movqR .rbx .xmm7, .movqR .rsi .xmm6] : List Instr)))

/-- The code of an operation. -/
def code (M : Mod) : LOp → Prog isa
  | .mul o a b => if a = b then sqrCall o a else mulCall o a b
  | .add o a b => .block (loadsC 0 regs a ++ chainC 0 .add .adc regs b ++ storesC 0 regs o)
  | .sub o a b => .block (subs a b ++ ([.alu .add topR (.imm 512)] : List Instr) ++ storesC 0 regs o)
  | .tri o a => .block (loadsC 0 regs a ++ dblChain .add regs ++ chainC 0 .add .adc regs a ++ storesC 0 regs o)
  | .sub2 o a b => .block (loadsC 0 regs b ++ nots ++ dblChain .add regs ++ chainC 0 .add .adc regs a ++
      ([.alu .add topR (.imm 1024)] : List Instr) ++ fold ++ storesC 0 regs o)
  | .subF o a b => .block (subs a b ++ ([.alu .add topR (.imm 512)] : List Instr) ++ fold ++ storesC 0 regs o)
  | .half o a => .block (loadsC 0 regs a ++ rot ++ storesC 0 halfRegs o)
  | .cadd o a b => .block (Mont.X86_64.add M o a b)
  | .csub o a b => .block (Mont.X86_64.sub M o a b)

/-- The slot an operation writes. -/
def LOp.out : LOp → Nat
  | .mul o _ _ | .add o _ _ | .sub o _ _ | .tri o _ | .sub2 o _ _ | .subF o _ _ | .half o _ | .cadd o _ _
  | .csub o _ _ => o

/-- The bounds of slots: at most `k p`, or below `p` for `0`. -/
abbrev Bounds := List (Nat × Nat)

/-- The bounds after an operation, if it applies. -/
def step (L : Bounds) : LOp → Option Bounds
  | .mul o a b => do
    let ka ← L.lookup a
    let kb ← L.lookup b
    if ka ≤ 8 ∧ kb ≤ 8 ∧ Mont.lowArgs 9 o a b then some ((o, 0) :: L) else none
  | .add o a b => do
    let ka ← L.lookup a
    let kb ← L.lookup b
    if ka ≤ 4 ∧ kb ≤ 4 then some ((o, max ka 1 + max kb 1) :: L) else none
  | .sub o a b => do
    let ka ← L.lookup a
    let kb ← L.lookup b
    if ka ≤ 4 ∧ kb ≤ 1 then some ((o, max ka 1 + 1) :: L) else none
  | .tri o a => do
    let ka ← L.lookup a
    if ka ≤ 1 then some ((o, 3) :: L) else none
  | .sub2 o a b | .subF o a b => do
    let ka ← L.lookup a
    let kb ← L.lookup b
    if ka ≤ 1 ∧ kb ≤ 1 then some ((o, 1) :: L) else none
  | .half o a => do
    let ka ← L.lookup a
    if ka ≤ 1 then some ((o, 1) :: L) else none
  | .cadd o a b => do
    let ka ← L.lookup a
    let kb ← L.lookup b
    if ka ≤ 1 ∧ kb = 0 then some ((o, 0) :: L) else none
  | .csub o a b => do
    let ka ← L.lookup a
    let kb ← L.lookup b
    if ka = 0 ∧ kb = 0 then some ((o, 0) :: L) else none

/-- The bounds after operations, if they apply. -/
def check : Bounds → List LOp → Option Bounds
  | L, [] => some L
  | L, op :: ops => (step L op).bind fun L => check L ops

/-- The operations' code, one after the other. -/
def prog (M : Mod) : List LOp → Prog isa
  | [] => .block []
  | op :: ops => .seq (code M op) (prog M ops)

/-- `(X : H/2 : Z)` doubled in place, `H` in `p.y`. -/
def dblOps (S : RcbSlots) (p : Pt) : List LOp :=
  [.mul S.t0 p.z p.z, .sub S.t1 p.x S.t0, .add S.t0 p.x S.t0, .mul S.t2 p.y p.y,
   .mul S.t1 S.t1 S.t0, .mul S.t0 S.t2 S.t2, .tri S.t1 S.t1, .mul S.t2 p.x S.t2,
   .mul S.t3 S.t1 S.t1, .sub2 p.x S.t3 S.t2, .mul p.z p.y p.z, .sub S.t2 S.t2 p.x,
   .add S.t1 S.t1 S.t1, .mul S.t2 S.t1 S.t2, .subF p.y S.t2 S.t0]

/-- `maddJ`, its differences before products lazy. -/
def maddOps (S : RcbSlots) (p q o : Pt) : List LOp :=
  [.mul S.t0 p.z p.z, .mul S.t1 q.x S.t0, .mul S.t2 p.z S.t0, .mul S.t2 q.y S.t2,
   .sub S.t1 S.t1 p.x, .sub S.t2 S.t2 p.y, .mul S.t3 S.t1 S.t1, .mul S.t4 S.t1 S.t3,
   .mul S.t3 p.x S.t3, .mul o.x S.t2 S.t2, .csub o.x o.x S.t4, .cadd S.t5 S.t3 S.t3,
   .csub o.x o.x S.t5, .sub S.t3 S.t3 o.x, .mul S.t3 S.t2 S.t3, .mul S.t4 p.y S.t4,
   .csub o.y S.t3 S.t4, .mul o.z p.z S.t1]

end LazyP521

open VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass

namespace WinCfg

variable (K : WinCfg)

/-- The bounds of `R`'s slots between the doublings, and of the constant zero. -/
def lazyBounds : LazyP521.Bounds := [(K.R.x, 1), (K.R.y, 2), (K.R.z, 0), (K.zero, 0)]

/-- The bounds of the points of an addition. -/
def lazyAddBounds : LazyP521.Bounds :=
  [(K.R.x, 0), (K.R.y, 0), (K.R.z, 0), (K.E.x, 0), (K.E.y, 0)]

/-- Whether the doublings of `quadLazy` and the addition of `sumJ` are P-521's
with BMI2 and ADX, on slots that suit them. -/
def lazyOk : Bool :=
  K.M.adx && decide (K.M.n = 9) && decide (K.M.red = .friendly p521Ws) && decide (K.M.tmp = Mont.fnTmp) &&
  (match LazyP521.check (lazyBounds K) (LazyP521.dblOps K.S K.R) with
  | none => false
  | some L => (L.lookup K.R.x == some 1) && (L.lookup K.R.y == some 1) && (L.lookup K.R.z == some 0) &&
      (L.lookup K.zero == some 0)) &&
  (match LazyP521.check (lazyAddBounds K) (LazyP521.maddOps K.S K.R K.E K.D) with
  | none => false
  | some L => (L.lookup K.D.x == some 0) && (L.lookup K.D.y == some 0) && (L.lookup K.D.z == some 0))

/-- A pair of lazy doublings, with the public count in `rbx` (`jacPairOn`). -/
def lazyPair : Prog isa :=
  .seq (LazyP521.prog K.M (LazyP521.dblOps K.S K.R)) <|
  .seq (LazyP521.prog K.M (LazyP521.dblOps K.S K.R)) <|
  .block [.alu .sub .rbx (.imm 4096), .alu .cmp .rbx (.imm 4096)]

/-- `R = 16 R` in Jacobian coordinates: `Y` doubled, two pairs of lazy
doublings, `Y` halved, and `X` and `Y` made canonical (zero added). -/
def quadLazy : Prog isa :=
  .seq (LazyP521.prog K.M [.add K.R.y K.R.y K.R.y]) <|
  .seq (.block [.alu .add .rbx (.imm 8192)]) <|
  .seq (.loop (lazyPair K) .ae) <|
  LazyP521.prog K.M [.half K.R.y K.R.y, .cadd K.R.y K.R.y K.zero, .cadd K.R.x K.R.x K.zero]

/-- `D = R + E` by the mixed addition: `maddOps` where `lazyOk`, else `maddJ`. -/
def maddP : Prog isa :=
  if lazyOk K then LazyP521.prog K.M (LazyP521.maddOps K.S K.R K.E K.D) else fprogB K.M (maddJ K.S K.R K.E K.D)

end WinCfg

end VG.Impl.Weierstrass.X86_64
