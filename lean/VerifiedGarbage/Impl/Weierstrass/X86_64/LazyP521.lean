module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.Window

/-!
# P-521 on x86-64 with BMI2 and ADX: Jacobian doublings with lazy reduction

`p = 2⁵²¹ - 1` and nine words hold 576 bits, so a sum of a few numbers below
`p` fits nine words with no reduction, and the product by `vg_p521_mul_mod_p_adx`
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
abbrev top : Reg := xAcc 17
abbrev low : Reg := xAcc 9

/-- The registers complemented. -/
def nots : List Instr := regs.map fun t => .alu .xor t (.imm (-1))

/-- The carry added along registers. -/
def adcs (ts : List Reg) : List Instr := ts.map fun t => .alu .adc t (.imm 0)

/-- The bits above 521 of the top word into `rax`, taken off, and added to the
low word. -/
def foldHi : List Instr :=
  [.mov .rax (.reg top), .shift .shr .rax 9, .alu .and top (.imm 511), .alu .add low (.reg .rax)]

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

/-- `p - [b]` in the registers but for `512` in the top word, then `[a]` added. -/
def subs (a b : Nat) : List Instr := loadsC 0 regs b ++ nots ++ chainC 0 .add .adc regs a

/-- The code of an operation. -/
def code : LOp → Prog isa
  | .mul o a b => Mont.mulCall ("vg_p521_mul_mod_p" ++ "_adx") Mont.mulFnX o a b
  | .add o a b => .block (loadsC 0 regs a ++ chainC 0 .add .adc regs b ++ storesC 0 regs o)
  | .sub o a b => .block (subs a b ++ ([.alu .add top (.imm 512)] : List Instr) ++ storesC 0 regs o)
  | .tri o a => .block (loadsC 0 regs a ++ dblChain .add regs ++ chainC 0 .add .adc regs a ++ storesC 0 regs o)
  | .sub2 o a b => .block (loadsC 0 regs b ++ nots ++ dblChain .add regs ++ chainC 0 .add .adc regs a ++
      ([.alu .add top (.imm 1024)] : List Instr) ++ fold ++ storesC 0 regs o)
  | .subF o a b => .block (subs a b ++ ([.alu .add top (.imm 512)] : List Instr) ++ fold ++ storesC 0 regs o)

/-- The slot an operation writes, and those it reads. -/
def LOp.out : LOp → Nat
  | .mul o _ _ | .add o _ _ | .sub o _ _ | .tri o _ | .sub2 o _ _ | .subF o _ _ => o

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

/-- The bounds after operations, if they apply. -/
def check : Bounds → List LOp → Option Bounds
  | L, [] => some L
  | L, op :: ops => (step L op).bind fun L => check L ops

/-- The operations' code, one after the other. -/
def prog : List LOp → Prog isa
  | [] => .block []
  | op :: ops => .seq (code op) (prog ops)

/-- `(X : H/2 : Z)` doubled in place, `H` in `p.y`. -/
def dblOps (S : RcbSlots) (p : Pt) : List LOp :=
  [.mul S.t0 p.z p.z, .sub S.t1 p.x S.t0, .add S.t0 p.x S.t0, .mul S.t2 p.y p.y,
   .mul S.t1 S.t1 S.t0, .mul S.t0 S.t2 S.t2, .tri S.t1 S.t1, .mul S.t2 p.x S.t2,
   .mul S.t3 S.t1 S.t1, .sub2 p.x S.t3 S.t2, .mul p.z p.y p.z, .sub S.t2 S.t2 p.x,
   .add S.t1 S.t1 S.t1, .mul S.t2 S.t1 S.t2, .subF p.y S.t2 S.t0]

/-- The registers of `half`'s result. -/
def halfRegs : List Reg := (List.range 8).map (fun k => xAcc (10 + k)) ++ [.rcx]

/-- `[o]` halved modulo `p`: its 521 bits rotated right by one. -/
def half (o : Nat) : List Instr :=
  loadsC 0 regs o ++
  ([.mov .rax (.reg low), .alu .and .rax (.imm 1), .shift .shl .rax 8, .mov .rcx (.reg top),
    .shift .shr .rcx 1, .alu .add .rcx (.reg .rax)] : List Instr) ++
  ([.shld (xAcc 17) (xAcc 16) 63, .shld (xAcc 16) (xAcc 15) 63, .shld (xAcc 15) (xAcc 14) 63,
    .shld (xAcc 14) (xAcc 13) 63, .shld (xAcc 13) (xAcc 12) 63, .shld (xAcc 12) (xAcc 11) 63,
    .shld (xAcc 11) (xAcc 10) 63, .shld (xAcc 10) (xAcc 9) 63] : List Instr) ++
  storesC 0 halfRegs o

end LazyP521

open VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass

namespace WinCfg

variable (K : WinCfg)

/-- The bounds of `R`'s slots before, between and after the doublings. -/
def lazyBounds : LazyP521.Bounds := [(K.R.x, 1), (K.R.y, 2), (K.R.z, 0)]

/-- Whether the doublings of `quadLazy` are P-521's with BMI2 and ADX, on slots
that suit them. -/
def lazyOk : Bool :=
  K.M.adx && decide (K.M.n = 9) && decide (K.M.red = .friendly p521Ws) && decide (K.M.tmp = Mont.fnTmp) &&
  match LazyP521.check (lazyBounds K) (LazyP521.dblOps K.S K.R) with
  | none => false
  | some L => L.lookup K.R.x == some 1 && L.lookup K.R.y == some 1 && L.lookup K.R.z == some 0

/-- A pair of lazy doublings, with the public count in `rbx` (`jacPairOn`). -/
def lazyPair : Prog isa :=
  .seq (LazyP521.prog (LazyP521.dblOps K.S K.R)) <|
  .seq (LazyP521.prog (LazyP521.dblOps K.S K.R)) <|
  .block [.alu .sub .rbx (.imm 4096), .alu .cmp .rbx (.imm 4096)]

/-- `R = 16 R` in Jacobian coordinates: `Y` doubled, two pairs of lazy
doublings, `Y` halved, and `X` and `Y` made canonical (zero added). -/
def quadLazy : Prog isa :=
  .seq (LazyP521.code (.add K.R.y K.R.y K.R.y)) <|
  .seq (.block [.alu .add .rbx (.imm 8192)]) <|
  .seq (.loop (lazyPair K) .ae) <|
  .seq (.block (LazyP521.half K.R.y)) <|
  .seq (.block (Mont.X86_64.add K.M K.R.y K.R.y K.zero)) <|
  .block (Mont.X86_64.add K.M K.R.x K.R.x K.zero)

end WinCfg

end VG.Impl.Weierstrass.X86_64
