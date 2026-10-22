module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
public import VerifiedGarbage.Impl.Weierstrass.X86_64.SelWeave
public import VerifiedGarbage.Impl.X86_64Scal

/-!
# 5-bit windows with an affine table on x86-64, each selection woven into the addition before it

`windowA`'s loop, with the entry of digit `j - 1` selected while digit `j`'s
mixed addition runs (`stepAP`), as `windowOP` does for odd windows
(`WinJacOddP.lean`): its loads, of the entry's `X` and `Y` (its first `n`
16-byte pieces), are spread among the addition's field operations
(`selChunkA`, `fprogBI`, the products written out: `Mod.inl`) and kept in
vector registers until the addition and the masks after it
(`masksA`: `D = T` where `R = O`, `R = D` unless the digit is zero) have read
`T`; then they are stored to `T` (whose `Z` stays one) and its `Y` negated
for a negative digit (`finA`). Digit `J - 2`'s entry is selected before the
loop (`firstAP`), and the last addition, digit `0`'s, selects none
(`lastA`). The weaving applies to at least three digits, at most ten pieces,
and an addition and masks of scalar code (`weaveAOk`); `windowAW` falls back to
`windowA` elsewhere.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.X86_64

open VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass

namespace JacWinCfg

variable (K : JacWinCfg)

/-- The modulus with its products written out. -/
def MI : Mod := { K.M with inl := true }

/-- The mixed addition's field operations. -/
def nMadd : Nat := (maddJ K.S K.R K.E K.D).length

/-- After field operation `i` of the mixed addition: entries
`chunkW nMadd i + 1 … chunkW nMadd (i + 1)` kept in the accumulators. -/
def selChunkA (i : Nat) : List Instr := selChunkW K.avx2 K.tbl K.st K.M.n K.nMadd i

/-- What the iteration does after the mixed addition: `D = T` where `R = O`,
and `R = D` unless the digit is zero. -/
def masksA : List Instr :=
  nzMask K.M.n K.R.z ++ selPt K.M.n K.D K.E K.D ++ K.tc.digit ++ eqMask 0 ++ selPt K.M.n K.R K.D K.R

/-- Before digit `j = rbx`'s addition: digit `j - 1`'s magnitude into `r8`,
and the selection of its entry's `X` and `Y` set up. -/
def prepA : List Instr :=
  [.alu .sub .rbx (.imm 1)] ++ K.tc.digit ++ [.alu .add .rbx (.imm 1)] ++ selSetW K.avx2 K.M.n

/-- After digit `j = rbx`'s masks: digit `j - 1`'s `X` and `Y` stored to `T`,
its `Y` negated for a negative digit, and `ZF` for `j = 1`. -/
def finA : List Instr :=
  storeW K.avx2 K.T K.M.n ++ [.alu .sub .rbx (.imm 1)] ++ K.tc.negY ++
    [.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm 1)]

/-- Iteration `j = rbx - 1` (with `rbx` counting down from `J - 1` to `2`):
`R = 32 R + [d_j]P`, digit `j`'s entry in `T`, with digit `j - 1`'s
selected meanwhile into `T`. -/
def stepAP (dbl : Pt → Prog isa) : Prog isa :=
  .seq (.block [.alu .sub .rbx (.imm 1)]) <|
  .seq (K.dbls dbl) <|
  .seq (.block K.prepA) <|
  .seq (fprogBI K.MI (maddJ K.S K.R K.E K.D) K.selChunkA 0) <|
  .block (K.masksA ++ K.finA)

/-- The last iteration, `rbx = 1`: `R = 32 R + [d_0]P`, digit `0`'s entry in
`T`. -/
def lastA (dbl : Pt → Prog isa) : Prog isa :=
  .seq (.block [.alu .sub .rbx (.imm 1)]) <|
  .seq (K.dbls dbl) (.block (fprog K.M (maddJ K.S K.R K.E K.D) ++ K.masksA))

/-- `rbx = J - 1`, `R` the top digit's point, and digit `J - 2`'s entry in
`T`. -/
def firstAP : List Instr :=
  K.first ++ [.alu .sub .rbx (.imm 1)] ++ K.tc.digit ++ K.selectA ++ K.tc.negY ++ [.alu .add .rbx (.imm 1)]

/-- `windowA`, its selections woven into the additions. -/
def windowAP (inv : Prog isa) (dbl : Pt → Prog isa) : Prog isa :=
  .seq K.build <| .seq (K.normA inv) <| .seq (.block K.firstAP) <| .seq (.loop (K.stepAP dbl) .ne) <|
  .seq (K.lastA dbl) <| .seq (.block K.tc.outFix) (ForwardField.programB K.M K.tc.outOps)

/-- Whether the woven selection applies: at least three digits, an entry's
`X` and `Y` of two to ten 16-byte pieces, and a mixed addition whose
operations, written out, and masks are of scalar code. -/
def weaveAOk : Bool :=
  decide (3 ≤ K.J) && decide (2 ≤ K.M.n ∧ K.M.n ≤ 10) &&
    ((maddJ K.S K.R K.E K.D).all fun op => scalCode (opProg K.MI op)) && K.masksA.all scalarI

/-- `windowAP` where it applies (`weaveAOk`), else `windowA`. -/
def windowAW (inv : Prog isa) (dbl : Pt → Prog isa) : Prog isa :=
  if K.weaveAOk then K.windowAP inv dbl else K.windowA inv dbl

end JacWinCfg

end VG.Impl.Weierstrass.X86_64
