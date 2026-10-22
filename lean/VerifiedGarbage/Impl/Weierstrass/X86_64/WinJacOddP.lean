module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacOdd
public import VerifiedGarbage.Impl.Weierstrass.X86_64.ForwardFieldI
public import VerifiedGarbage.Impl.X86_64Scal
public import VerifiedGarbage.Impl.Weierstrass.X86_64.SelWeave

/-!
# The odd window method on x86-64, its selections woven into the additions

`windowO`'s loop, with the entry of digit `j - 1` selected while digit `j`'s
addition runs (`stepOP`): the selection loads every entry of the table, which
takes about as long as the addition but needs none of its results, while the
addition's field operations mostly wait on each other's. Its loads are spread
among the addition's operations (`selChunkO`, `ForwardField.programBI`) and
kept in vector accumulators, which the operations, of scalar code, do not
touch, until the addition is done; then they are stored to `T`, which the
addition has finished reading, and its `Y` negated for a negative digit
(`finO`). Each part of the selection computes the table's address in `rdx`
again, the only register it writes.

With AVX2 the entries are selected 32 bytes at a time (`selEntryY`); without,
16 bytes at a time with SSE2 (`selEntryX`): the mask of an entry from the
counter `xmm11` and the broadcast magnitude `xmm13` (`pcmpeqd`), as with
AVX2, so that no part of the selection needs a general-purpose register but
`rdx`. Digit `J - 2`'s entry is selected before the loop (`firstOP`), and the
last addition, digit `0`'s, selects none (`lastO`). The weaving applies to
four words (an entry of ten 16-byte pieces, five 32-byte ones), at least
three digits, and an addition of scalar code (`weaveOk`); `windowOW` falls
back to `windowO` elsewhere.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.X86_64

open VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass

namespace JacWinCfg

variable (K : JacWinCfg)

/-- The addition's field operations. -/
def nAddO : Nat := K.addOpsO.length

/-- The entries selected before field operation `i` of the addition is done
(`chunkW`). -/
def chunkO (i : Nat) : Nat := chunkW K.nAddO i

/-- Entry `m` of the table at `rdx`, its five coordinates kept in the
accumulators. -/
def selEntryP (m : Nat) : List Instr := selEntryW K.avx2 K.st K.np16 m

/-- After field operation `i`: entries `chunkO i + 1 … chunkO (i + 1)` kept in
the accumulators (`selChunkW`). -/
def selChunkO (i : Nat) : List Instr := selChunkW K.avx2 K.tbl K.st K.np16 K.nAddO i

/-- The selection of an entry's five coordinates set up (`selSetW`). -/
def selSetP : List Instr := selSetW K.avx2 K.np16

/-- The accumulators stored to `T` (`storeW`). -/
def storeP : List Instr := storeW K.avx2 K.T K.np16

/-- Before digit `j = rbx`'s addition: digit `j - 1`'s entry into `r8`, and
the selection set up for it. -/
def prepO : List Instr := [.alu .sub .rbx (.imm 1)] ++ K.digitO ++ [.alu .add .rbx (.imm 1)] ++ K.selSetP

/-- After digit `j = rbx`'s addition: digit `j - 1`'s entry stored to `T`, its
`Y` negated for a negative digit, and `ZF` for `j = 1`. -/
def finO : List Instr :=
  K.storeP ++ [.alu .sub .rbx (.imm 1)] ++ K.tc.negY ++ [.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm 1)]

/-- Iteration `j = rbx - 1` (with `rbx` counting down from `J - 1` to `2`):
`R = 32 R + [d_j]P`, digit `j`'s entry in `T`, with digit `j - 1`'s
selected meanwhile into `T`. -/
def stepOP (dbl : Pt → Prog isa) : Prog isa :=
  .seq (.block [.alu .sub .rbx (.imm 1)]) <|
  .seq (K.dbls dbl) <|
  .seq (.block K.prepO) <|
  .seq (ForwardField.programBI K.M K.addOpsO K.selChunkO) <|
  .block K.finO

/-- The last iteration, `rbx = 1`: `R = 32 R + [d_0]P`, digit `0`'s entry in
`T`. -/
def lastO (dbl : Pt → Prog isa) : Prog isa :=
  .seq (.block [.alu .sub .rbx (.imm 1)]) <|
  .seq (K.dbls dbl) (ForwardField.programB K.M K.addOpsO)

/-- `rbx = J - 1`, `R = P`, and digit `J - 2`'s entry in `T`. -/
def firstOP : List Instr :=
  K.firstO ++ [.alu .sub .rbx (.imm 1)] ++ K.digitO ++ K.select ++ K.tc.negY ++ [.alu .add .rbx (.imm 1)]

/-- `windowO`, its selections woven into the additions. -/
def windowOP (dbl : Pt → Prog isa) : Prog isa :=
  .seq K.buildO <| .seq (.block K.firstOP) <| .seq (.loop (K.stepOP dbl) .ne) <| .seq (K.lastO dbl) <|
  .seq (.block K.tc.outFix) (ForwardField.programB K.M K.tc.outOps)

/-- Whether the woven selection applies: four words, at least three digits,
and an addition whose operations, forwarded or not, are of scalar code. -/
def weaveOk : Bool :=
  decide (K.M.n = 4) && decide (3 ≤ K.J) && K.addOpsO.all fun op =>
    (ForwardField.code K.M op).all scalarI && scalCode ((opCall? K.M op).getD (.block (ForwardField.code K.M op)))

/-- `windowOP` where it applies (`weaveOk`), else `windowO`. -/
def windowOW (dbl : Pt → Prog isa) : Prog isa := if K.weaveOk then K.windowOP dbl else K.windowO dbl

end JacWinCfg

end VG.Impl.Weierstrass.X86_64
