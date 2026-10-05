import VerifiedGarbage.Proof.Framework.AArch64.TaintEraseOff
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.Ed448.AArch64.VerifyEquation

/-!
# Ed448's base-point multiplication and verification on AArch64: the code without its offsets

Untrusted: everything here is checked by Lean. The constant-time analysis,
`keepsV` and `noFrames` do not read the offsets of loads and stores or the
other immediates (`Code.eraseOff`), and without them every field operation
of X448's arithmetic (`Weak.code`) is one of six pieces of code, whatever
its slots (`code_eraseOff`, proven without evaluating them): the product,
the square, the sum, the difference, the product by a small constant and
the copy. `scalarBase0` and `verifyEquation0` are the functions with each
field operation written as that piece (`code0`), and their other blocks as
constants too; the kernel, evaluating their analysis or their `keepsV`
check, checks each piece once from each taint rather than once for every
operation, since it caches the check of the same code from the same state.
The pieces and blocks have literals (`materialize_code`), which both checks
read; the functions have none, which would cost more to check (evaluating
every operation) than it saves.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448 VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64 (slot X2 T0 T1 T2 T3 T4 T5 T6 T7 Op)

/-! ## Field operations without their slots -/

section Field

open VG.Impl.Curve448.AArch64
open VG.Impl.X448.AArch64 (Wide.column Wide.pass Wide.fold Tail.pass Cached.loadCached)

/-- `collect` without its offsets. -/
def collectE : List Instr := (collect 0).map Instr.eraseOff

theorem collect_eraseOff (o : Nat) : (collect o).map Instr.eraseOff = collectE := by
  simp only [collectE, collect, List.map_flatMap, List.map_cons, List.map_nil,
    VG.Impl.X448.AArch64.ld, VG.Impl.X448.AArch64.st, Instr.eraseOff]

theorem normalize_eraseOff (o : Nat) :
    (normalize o).map Instr.eraseOff = (normalize 0).map Instr.eraseOff := by
  simp only [normalize, List.map_append, collect_eraseOff]

theorem pointFinish_eraseOff (o : Nat) :
    (pointFinish o).map Instr.eraseOff = (pointFinish 0).map Instr.eraseOff := by
  simp only [pointFinish, List.map_append, collect_eraseOff]

/-- `Wide.column` without its offsets. -/
def columnE (k : Nat) : List Instr := (Wide.column 0 0 k).map Instr.eraseOff

theorem column_eraseOff (a b k : Nat) : (Wide.column a b k).map Instr.eraseOff = columnE k := by
  simp only [columnE, Wide.column, List.map_append, List.map_flatMap,
    apply_ite (List.map Instr.eraseOff), List.map_cons, List.map_nil,
    VG.Impl.X448.AArch64.ld, VG.Impl.X448.AArch64.st, Instr.eraseOff]

/-- `Cached.loadCached` without its offsets. -/
def loadCachedE : List Instr := (Cached.loadCached 0).map Instr.eraseOff

theorem loadCached_eraseOff (a : Nat) : (Cached.loadCached a).map Instr.eraseOff = loadCachedE := by
  simp only [loadCachedE, Cached.loadCached, List.map_flatMap, List.map_cons, List.map_nil,
    VG.Impl.X448.AArch64.ld, Instr.eraseOff]

/-- The product of X448's arithmetic, on slots chosen once. -/
def productC : Prog isa := product 0 0 1

theorem product_eraseOff (o a b : Nat) : Code.eraseOff (product o a b) = Code.eraseOff productC := by
  simp only [productC, product, Code.eraseOff, List.map_append, List.map_flatMap,
    column_eraseOff, normalize_eraseOff]

/-- The square, on a slot chosen once. -/
def sqrC : Prog isa := sqr 0 0

theorem sqr_eraseOff (o a : Nat) : Code.eraseOff (sqr o a) = Code.eraseOff sqrC := by
  simp only [sqrC, sqr, Code.eraseOff, List.map_append, loadCached_eraseOff, normalize_eraseOff]

/-- The sum, on slots chosen once. -/
def addC : Prog isa := .block (add 0 0 0)

theorem add_eraseOff (o a b : Nat) : Code.eraseOff (.block (add o a b)) = Code.eraseOff addC := by
  simp only [addC, Code.eraseOff, add, addStep, addEval, storeCoeff, List.map_append,
    List.map_flatMap, List.map_cons, List.map_nil, pointFinish_eraseOff, VG.Impl.X448.AArch64.ld,
    Instr.eraseOff]

/-- The difference, on slots chosen once. -/
def subC : Prog isa := .block (sub 0 0 0)

theorem sub_eraseOff (o a b : Nat) : Code.eraseOff (.block (sub o a b)) = Code.eraseOff subC := by
  simp only [subC, Code.eraseOff, sub, subStep, subEval, storeCoeff, List.map_append,
    List.map_flatMap, List.map_cons, List.map_nil, pointFinish_eraseOff, VG.Impl.X448.AArch64.ld,
    Instr.eraseOff]

/-- The product by a small constant, on slots chosen once. -/
def smallC : Prog isa := .block (small 0 0)

theorem small_eraseOff (o a : Nat) : Code.eraseOff (.block (small o a)) = Code.eraseOff smallC := by
  simp only [smallC, Code.eraseOff, small, smallStep, smallEval, storeCoeff, List.map_append,
    List.map_flatMap, List.map_cons, List.map_nil, normalize_eraseOff, VG.Impl.X448.AArch64.ld,
    Instr.eraseOff]

/-- The copy, on slots chosen once. -/
def copyC : Prog isa := .block (copy 0 0)

theorem copy_eraseOff (o a : Nat) : Code.eraseOff (.block (copy o a)) = Code.eraseOff copyC := by
  simp only [copyC, Code.eraseOff, copy, List.map_flatMap, List.map_cons, List.map_nil,
    VG.Impl.X448.AArch64.ld, VG.Impl.X448.AArch64.st, Instr.eraseOff]

/-- A multiplication on slots chosen once: a square or a product. -/
def mul0 (a b : Nat) : Prog isa := if a = b then sqrC else productC

theorem mul_eraseOff (o a b : Nat) : Code.eraseOff (mul o a b) = Code.eraseOff (mul0 a b) := by
  by_cases h : a = b
  · simp only [mul, mul0, h, ite_true, sqr_eraseOff]
  · simp only [mul, mul0, h, ite_false, product_eraseOff]

end Field

/-! The kernel reads these pieces from literals, rather than building each from the functions
that make it (once for every taint it is analysed from). -/

materialize_code productC
materialize_code sqrC
materialize_code addC
materialize_code subC
materialize_code smallC
materialize_code copyC

/-- A field operation (`Weak.code`) on slots chosen once. -/
def code0 : Op → Prog isa
  | .mul _ a b => mul0 a b
  | .mulSmall _ _ => smallC
  | .add _ _ _ => addC
  | .sub _ _ _ => subC
  | .copy _ _ => copyC

theorem code_eraseOff (op : Op) :
    Code.eraseOff (VG.Impl.X448.AArch64.Weak.code op) = Code.eraseOff (code0 op) := by
  cases op with
  | mul o a b => exact mul_eraseOff o a b
  | mulSmall o a => exact small_eraseOff o a
  | add o a b => exact add_eraseOff o a b
  | sub o a b => exact sub_eraseOff o a b
  | copy o a => exact copy_eraseOff o a

/-- `Weak.ops`, each operation without its slots. -/
def ops0 : List Op → Prog isa
  | [] => .block []
  | o :: os => .seq (code0 o) (ops0 os)

theorem ops_eraseOff (os : List Op) :
    Code.eraseOff (VG.Impl.X448.AArch64.Weak.ops os) = Code.eraseOff (ops0 os) := by
  induction os with
  | nil => rfl
  | cons o os ih =>
    simp only [VG.Impl.X448.AArch64.Weak.ops, ops0, Code.eraseOff, code_eraseOff, ih]

/-- `field`, each operation without its slots. -/
def field0 (ops : List VG.Impl.Ed448.FOp) : Prog isa := ops0 (ops.map toOp)

theorem field_eraseOff (ops : List VG.Impl.Ed448.FOp) :
    Code.eraseOff (field ops) = Code.eraseOff (field0 ops) :=
  ops_eraseOff _

/-- `Weak.sqn`, its square on a slot chosen once. -/
def sqn0 : Prog isa :=
  .seq (.block [.movz .x .x19 1 0])
    (.loop (.seq sqrC (.block [.subImm .x .x19 .x19 1])) (.nonzero .x .x19))

theorem sqn_eraseOff (o n : Nat) :
    Code.eraseOff (VG.Impl.X448.AArch64.Weak.sqn o n) = Code.eraseOff sqn0 := by
  simp only [sqn0, VG.Impl.X448.AArch64.Weak.sqn, Code.eraseOff, mul_eraseOff, mul0, ite_true,
    List.map_cons, List.map_nil, Instr.eraseOff]

/-! ## X448's chains without their slots -/

/-- `Weak.invert`, each field operation without its slots. -/
def invert0 : Prog isa :=
  .seq (ops0 [.copy T0 VG.Impl.X448.AArch64.Z2]) <| .seq sqn0 <|
  .seq (ops0 [.mul T0 T0 VG.Impl.X448.AArch64.Z2, .copy T1 T0]) <|
  .seq sqn0 <| .seq (ops0 [.mul T1 T1 T0, .copy T2 T1]) <|
  .seq sqn0 <| .seq (ops0 [.mul T2 T2 T1, .copy T3 T2]) <|
  .seq sqn0 <| .seq (ops0 [.mul T3 T3 T2, .copy T4 T3]) <|
  .seq sqn0 <| .seq (ops0 [.mul T4 T4 T3, .copy T5 T4]) <|
  .seq sqn0 <| .seq (ops0 [.mul T5 T5 T4, .copy T6 T5]) <|
  .seq sqn0 <| .seq (ops0 [.mul T6 T6 T5]) <|
  .seq sqn0 <| .seq (ops0 [.mul T6 T6 T5]) <|
  .seq sqn0 <| .seq (ops0 [.mul T6 T6 T3]) <|
  .seq sqn0 <| .seq (ops0 [.mul T6 T6 T2]) <|
  .seq sqn0 <| .seq (ops0 [.mul T6 T6 T1]) <|
  .seq sqn0 <| .seq (ops0 [.mul T6 T6 T0, .copy T7 T6]) <|
  .seq sqn0 <| .seq (ops0 [.mul T7 T7 VG.Impl.X448.AArch64.Z2]) <|
  .seq sqn0 <| .seq sqn0 <| ops0 [.mul T6 T6 VG.Impl.X448.AArch64.Z2, .mul T7 T7 T6]

theorem invert_eraseOff : Code.eraseOff VG.Impl.X448.AArch64.Weak.invert = Code.eraseOff invert0 := by
  simp only [VG.Impl.X448.AArch64.Weak.invert, invert0, Code.eraseOff, ops_eraseOff, sqn_eraseOff]

/-- `root z`, each field operation without its slots. -/
def root0 (z : Nat) : Prog isa :=
  .seq (ops0 [.copy T0 (slot z)]) <| .seq sqn0 <|
  .seq (ops0 [.mul T0 T0 (slot z), .copy T1 T0]) <|
  .seq sqn0 <| .seq (ops0 [.mul T1 T1 T0, .copy T2 T1]) <|
  .seq sqn0 <| .seq (ops0 [.mul T2 T2 T1, .copy T3 T2]) <|
  .seq sqn0 <| .seq (ops0 [.mul T3 T3 T2, .copy T4 T3]) <|
  .seq sqn0 <| .seq (ops0 [.mul T4 T4 T3, .copy T5 T4]) <|
  .seq sqn0 <| .seq (ops0 [.mul T5 T5 T4, .copy T6 T5]) <|
  .seq sqn0 <| .seq (ops0 [.mul T6 T6 T5]) <|
  .seq sqn0 <| .seq (ops0 [.mul T6 T6 T5]) <|
  .seq sqn0 <| .seq (ops0 [.mul T6 T6 T3]) <|
  .seq sqn0 <| .seq (ops0 [.mul T6 T6 T2]) <|
  .seq sqn0 <| .seq (ops0 [.mul T6 T6 T1]) <|
  .seq sqn0 <| .seq (ops0 [.mul T6 T6 T0, .copy T7 T6]) <|
  .seq sqn0 <| .seq (ops0 [.mul T7 T7 (slot z)]) <|
  .seq sqn0 (ops0 [.mul T7 T7 T6])

theorem root_eraseOff (z : Nat) : Code.eraseOff (root z) = Code.eraseOff (root0 z) := by
  simp only [root, root0, Code.eraseOff, ops_eraseOff, sqn_eraseOff]

/-! ## `verifyEquation`

Its other blocks, as constants with literals, those of both decodings without their
slots. -/

theorem copy_map_eraseOff (o a : Nat) :
    (VG.Impl.Curve448.AArch64.copy o a).map Instr.eraseOff =
      (VG.Impl.Curve448.AArch64.copy 0 0).map Instr.eraseOff := by
  simp only [VG.Impl.Curve448.AArch64.copy, List.map_flatMap, List.map_cons, List.map_nil,
    VG.Impl.X448.AArch64.ld, VG.Impl.X448.AArch64.st, Instr.eraseOff]

theorem cswap_map_eraseOff (x y : Nat) :
    (VG.Impl.Curve448.AArch64.cswap x y).map Instr.eraseOff =
      (VG.Impl.Curve448.AArch64.cswap 0 0).map Instr.eraseOff := by
  simp only [VG.Impl.Curve448.AArch64.cswap, List.map_flatMap, List.map_cons, List.map_nil,
    VG.Impl.X448.AArch64.ld, VG.Impl.X448.AArch64.st, Instr.eraseOff]

/-- The entry. -/
def ventryC : Prog isa := .block ventry

/-- The check of `S`. -/
def sCheckC : Prog isa := .block sCheck

/-- `y` of the encoding at `rp`, into slot `yo`, and its checks. -/
def decodeYC (rp : Reg) (yo : Nat) : Prog isa := .block (decodeY rp yo)

/-- The checks of the root `x` in slot `xo`. -/
def checkXC (xo : Nat) : Prog isa := .block (eqSlots 12 13 ++ zeroSign xo ++ negMask)

/-- `checkXC` without its offsets. -/
def checkXE : List Instr := (eqSlots 12 13 ++ zeroSign 6 ++ negMask).map Instr.eraseOff

theorem checkX_eraseOff (xo : Nat) :
    (eqSlots 12 13 ++ zeroSign xo ++ negMask).map Instr.eraseOff = checkXE := by
  simp only [checkXE, zeroSign, canon, List.map_append, copy_map_eraseOff]

/-- `x` swapped with `-x`. -/
def negSwapC (xo : Nat) : Prog isa := .block (negSwap xo)

/-- `negSwapC` without its offsets. -/
def negSwapE : List Instr := (negSwap 6).map Instr.eraseOff

theorem negSwap_eraseOff (xo : Nat) : (negSwap xo).map Instr.eraseOff = negSwapE := by
  simp only [negSwapE, negSwap, List.map_append, cswap_map_eraseOff]

/-- A mask from a bit, and the swap of `T` into `Q`. -/
def maskSwapC : Prog isa := .block (maskAt 0 0 ++ swapT)

/-- `maskSwapC` without its offsets. -/
def maskSwapE : List Instr := (maskAt 0 0 ++ swapT).map Instr.eraseOff

theorem maskSwap_eraseOff (d₁ d₂ : Nat) : (maskAt d₁ d₂ ++ swapT).map Instr.eraseOff = maskSwapE := by
  simp only [maskSwapE, maskAt, List.map_append, List.map_cons, List.map_nil, Instr.eraseOff]

/-- `Q` the neutral point. -/
def qInitC : Prog isa := .block qInit

/-- The first comparison. -/
def eqC : Prog isa := .block (eqSlots 12 13)

/-- The second comparison, the result and the registers restored. -/
def resultC : Prog isa :=
  .block (eqSlots 12 13 ++ [.addImm .x .x5 .x20 0] ++ isZero ++
    [.addImm .x .x0 .x5 0, VG.Impl.X448.AArch64.ld .x19 0, VG.Impl.X448.AArch64.ld .x20 8])

materialize_code ventryC
materialize_code sCheckC
materialize_code decodeYA := decodeYC .x0 7
materialize_code decodeYR := decodeYC .x1 9
materialize_code checkXC6 := checkXC 6
materialize_code negSwapC6 := negSwapC 6
materialize_code maskSwapC
materialize_code qInitC
materialize_code eqC
materialize_code resultC
materialize_code VG.Impl.Ed448.AArch64.vbits

/-- `decode`, each field operation on slots chosen once. -/
def decode0 (rp : Reg) (xo yo : Nat) : Prog isa :=
  .seq (decodeYC rp yo) <| .seq (field0 (decodeUV yo xo)) <| .seq (root0 12) <|
  .seq (field0 [.mul xo xo 21, .sqr 12 xo, .mul 12 3 12]) <|
  .seq (checkXC 6) <| .seq (field0 [.sub 12 xo xo, .sub 12 12 xo]) (negSwapC 6)

/-- `vstep`, each field operation on slots chosen once. -/
def vstep0 : Prog isa :=
  .seq (.block [.subImm .x .x19 .x19 1]) <| .seq (field0 (doubleAt 0 1 2)) <|
  .seq (field0 (addAt 8 9)) <| .seq maskSwapC <| .seq (field0 (addAt 6 7)) maskSwapC

/-- `verifyEquation`, each field operation on slots chosen once. -/
def verifyEquation0 : Prog isa :=
  .seq ventryC <| .seq vbits <| .seq sCheckC <|
  .seq (.seq (decode0 .x0 6 7) <| .seq (field0 [.sub 6 0 6]) qInitC) <|
  .seq (.seq (.block [.movz .x .x19 456 0]) (.loop vstep0 (.nonzero .x .x19))) <|
  .seq (.seq (ops0 [.copy (slot 6) (slot 1)]) (decode0 .x1 8 9)) <|
  .seq (field0 (doubleAt 0 6 2 ++ doubleAt 0 6 2 ++ doubleAt 8 9 10 ++ doubleAt 8 9 10 ++
    [.mul 12 0 10, .mul 13 8 2])) <|
  .seq eqC <| .seq (field0 [.mul 12 6 10, .mul 13 9 2]) resultC

theorem verifyEquation_eraseOff : Code.eraseOff verifyEquation = Code.eraseOff verifyEquation0 := by
  simp only [verifyEquation, verifyEquation0, vdecodeA, vdecodeR, decode, decode0, vloop, vstep,
    vstep0, vfinish, Code.eraseOff, field_eraseOff, ops_eraseOff, root_eraseOff, ventryC, sCheckC,
    decodeYC, qInitC, eqC, resultC, checkXC, negSwapC, maskSwapC, checkX_eraseOff, negSwap_eraseOff,
    maskSwap_eraseOff]

end VG.Proof.Ed448.AArch64
