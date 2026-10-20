module

public import VerifiedGarbage.Impl.Weierstrass.AArch64.Naf
public import VerifiedGarbage.Impl.Weierstrass.CoZ
public import VerifiedGarbage.Impl.Weierstrass.CachedJac

/-!
# Public width-five NAF multiplication of any word count

`[k]P` for a public scalar `k` of `n` words, in Jacobian coordinates, for
fields whose products may be calls (`Mont.callOf`): the signed digits of `k`
(width five, `64 n + 1` bytes, `prep`), a table of the eight odd multiples
`[1]P, [3]P, …, [15]P` (`table`), and one doubling per digit, adding the
table's entry for each nonzero digit (`window`). The table holds no operand
of a product: `2P` is kept in `E` while the table is built, and an entry is
copied to `E` before it is added, so the table may lie above the products'
offsets. The table is built by co-Z arithmetic, for a `P` whose `z` is one,
and each entry's `Z²` and `Z³` are kept after it (`cache`), so that an
addition of an entry does not compute them (`addC`).
The loop alternates between `R` and `D` rather than copying the
result of each doubling and addition back. Every branch and address depends
on the digits of `k` and on the points, so only on public values.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.AArch64.PubNaf
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass
open Jacobian

/-! ## The recoding -/

/-- The registers of the scalar's `n` words (`low`) and its top word (`top`),
then of the constants `2^5 - 1`, `2^4`, `0` and `1` (`cst`), for `n ≤ 9`. -/
def regs : List Reg := [.x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x21, .x22, .x23]

def low (n : Nat) : List Reg := regs.take n
def top (n : Nat) : Reg := regs.getD n .x15
def limbs (n : Nat) : List Reg := low n ++ [top n]
def cst (n i : Nat) : Reg := regs.getD (n + 1 + i) .x15

/-- The scalar's words from `[x0 + src]`, a top word of zero, the constants,
`x19 = 64 n + 1` digits and `x20` at the digits. -/
def prepInit (K : WinCfg) (src : Nat) : List Instr :=
  loads (low K.M.n) src ++
  [.movz .x (top K.M.n) 0 0, .movz .x (cst K.M.n 0) 31 0, .movz .x (cst K.M.n 1) 16 0,
   .movz .x (cst K.M.n 2) 0 0, .movz .x (cst K.M.n 3) 1 0,
   .movz .x .x19 (BitVec.ofNat 16 (64 * K.M.n + 1)) 0, .addImm .x .x20 .x0 K.bits]

/-- `x2` = the digit: for an odd scalar its five low bits as a signed residue
(`-15 … 15`), else zero. -/
def chooseDigit (n : Nat) : Prog isa :=
  .seq (.block [.logic .and .x .x1 .x5 (cst n 3)]) <|
    .ite (.nonzero .x .x1)
      (.block [.logic .and .x .x2 .x5 (cst n 0), .logic .and .x .x3 .x2 (cst n 1),
        .lsl .x .x3 .x3 1, .sub .x .x2 .x2 .x3])
      (.block [.movz .x .x2 0 0])

/-- A right shift of `rs` by one bit. -/
def shrChain : List Reg → List Instr
  | [] => []
  | [r] => [.lsr .x r r 1]
  | r :: r' :: rs => .extr .x r r' r 1 :: shrChain (r' :: rs)

/-- The scalar less the digit (`x2`, sign-extended by `x3`), shifted right
by one bit. -/
def subtractShift (n : Nat) : List Instr :=
  [.lsr .x .x3 .x2 63, .sub .x .x3 (cst n 2) .x3, .subs .x .x5 .x5 .x2] ++
    ((limbs n).drop 1).map (fun r => .sbcs .x r r .x3) ++ shrChain (limbs n)

def prepStep (n : Nat) : Prog isa :=
  .seq (chooseDigit n) (.block (([.strb .x2 .x20 0, .addImm .x .x20 .x20 1] : List Instr) ++
    subtractShift n ++ [decCounter]))

/-- The `64 n + 1` signed digits of the scalar at `src`, as bytes from `K.bits`. -/
def prep (K : WinCfg) (src : Nat) : Prog isa :=
  .seq (.block (prepInit K src)) (.loop (prepStep K.M.n) (.nonzero .x .x19))

/-! ## The table -/

/-- The bytes of an entry. -/
def stride (K : WinCfg) : Nat := 24 * K.M.n

/-- `R` into the entry at `x0 + x20 + K.tbl`. -/
def store (K : WinCfg) : List Instr :=
  (List.range (3 * K.M.n)).flatMap fun i => [ld .x4 (K.R.x + 8 * i), .str .x .x4 .x20 (K.tbl + 8 * i)]

/-- ZADDU's slots (`CoZ`): the addend in `E`, the temporaries, the sum in
`R`, two unused slots and `P`, whose `z` is one. -/
def coZσ (K : WinCfg) (i : Nat) : Nat :=
  [K.E.x, K.E.y, K.S.t0, K.S.t1, K.S.t2, K.S.t3, K.S.t4, K.S.t5, K.R.x, K.R.y, K.R.z,
    K.D.x, K.D.y, K.P.x, K.P.y, K.P.z].getD i K.P.x

/-- DBLU's slots: `2P` into `E` (`x`, `y`), `P` at the same `Z` into `R`, as
ZADDU takes them. -/
def dbluσ (K : WinCfg) (i : Nat) : Nat :=
  [K.S.t4, K.S.t5, K.S.t0, K.S.t1, K.R.y, K.R.x, K.S.t2, K.S.t3, K.E.x, K.E.y, K.R.z,
    K.D.x, K.D.y, K.P.x, K.P.y, K.P.z].getD i K.P.x

def dbluOps (K : WinCfg) : List FOp := CoZ.dblu.map (CoZ.rename (dbluσ K))
def zadduOps (K : WinCfg) : List FOp := CoZ.zaddu.map (CoZ.rename (coZσ K))

/-- `R = R + 2P` by ZADDU, `E = 2P` at the new `Z`, stored in the next entry. -/
def tableStep (K : WinCfg) : Prog isa :=
  .seq (fprogB K.M (zadduOps K)) <|
    .block (store K ++ [.addImm .x .x20 .x20 (stride K), decCounter])

/-- `R = P` (affine) into the first entry, then by co-Z arithmetic `2P` and
`P` at one `Z`, and the seven other entries, each adding `2P`. -/
def table (K : WinCfg) : Prog isa :=
  .seq (.block (copyPt K.M.n K.R K.P ++ [.addImm .x .x20 .x0 0] ++ store K ++
    [.addImm .x .x20 .x20 (stride K), .movz .x .x19 7 0])) <|
  .seq (fprogB K.M (dbluOps K)) <|
  .loop (tableStep K) (.nonzero .x .x19)

/-! ## The multiplication -/

/-- Entry `a`'s `Z²` and `Z³`, after the table. -/
def cacheAt (K : WinCfg) (a : Nat) : Nat := K.tbl + 8 * stride K + 16 * K.M.n * (a - 1)

/-- Entry `a`'s `Z²` and `Z³` into the cache, from its `z` copied to `t2`
(products read no slot of the table) and through `t0` and `t1`. -/
def cacheOne (K : WinCfg) (a : Nat) : Prog isa :=
  .seq (.block (copy K.M.n K.S.t2 (K.tblPt a).z)) <|
  .seq (fprogB K.M [.mul K.S.t0 K.S.t2 K.S.t2, .mul K.S.t1 K.S.t2 K.S.t0]) <|
    .block (copy K.M.n (cacheAt K a) K.S.t0 ++ copy K.M.n (cacheAt K a + 8 * K.M.n) K.S.t1)

/-- The cache of entries `1 … a`. -/
def cacheTo (K : WinCfg) : Nat → Prog isa
  | 0 => .block []
  | a + 1 => .seq (cacheTo K a) (cacheOne K (a + 1))

/-- The cache of the eight entries. -/
def cache (K : WinCfg) : Prog isa := cacheTo K 8

/-- Entry `x2` (`1 … 8`, of `[2 x2 - 1]P`), into `E`, and first its `Z²` and
`Z³` into `R.y` and `R.z`, which the addition writes only after reading them. -/
def entry (K : WinCfg) : List Instr :=
  [.subImm .x .x2 .x2 1, .movz .x .x17 (BitVec.ofNat 16 (16 * K.M.n)) 0, .mul .x .x17 .x2 .x17,
   .add .x .x16 .x0 .x17] ++
  ((List.range (2 * K.M.n)).flatMap fun i => [.ldr .x .x4 .x16 (cacheAt K 1 + 8 * i), st .x4 (K.R.y + 8 * i)]) ++
  [.movz .x .x17 (BitVec.ofNat 16 (stride K)) 0, .mul .x .x2 .x2 .x17, .add .x .x16 .x0 .x2] ++
  ((List.range (3 * K.M.n)).flatMap fun i => [.ldr .x .x4 .x16 (K.tbl + 8 * i), st .x4 (K.E.x + 8 * i)])

/-- The entry of the digit `x2`'s magnitude, negated for a negative digit. -/
def signedEntry (K : WinCfg) : Prog isa :=
  .seq (.block (Naf.digitIndex ++ entry K)) <|
    .seq (.block (Naf.signRead K)) <|
      .ite (.nonzero .x .x3) (.block (Mont.AArch64.sub K.M K.E.y K.zero K.E.y)) (.block [])

/-- `o = p + q`, as `jacAdd`, with `q`'s `Z²` and `Z³` in `o.y` and `o.z`. -/
def addC (K : WinCfg) (p q o : Pt) : Prog isa :=
  .seq (.block (zeroMask K.M.n p.z)) <|
  .ite (.nonzero .x .x2) (.block (copyPt K.M.n o q)) <|
  .seq (.block (zeroMask K.M.n q.z)) <|
  .ite (.nonzero .x .x2) (.block (copyPt K.M.n o p)) <|
  .seq (fprogB K.M (CachedJac.headAt K.S p q o.y o.z)) <|
  .seq (.block (zeroMask K.M.n K.S.t3)) <|
  .ite (.nonzero .x .x2)
    (.seq (.block (zeroMask K.M.n K.S.t5)) <|
      .ite (.nonzero .x .x2) (VG.Impl.P256.VerifyDouble.double K.M K.S p o) (.block (infinity K o)))
    (fprogB K.M (jacTail K.S p q o))

/-- `R = D + [d]P` for the digit `d` at `x19`. -/
def digit (K : WinCfg) : Prog isa :=
  .seq (.block (Naf.digitRead K)) <|
    .ite (.nonzero .x .x2) (.seq (signedEntry K) (addC K K.D K.E K.R)) (.block (copyPt K.M.n K.R K.D))

/-- `D = 2R`, then `R = D + [d]P` for the next digit. -/
def step (K : WinCfg) : Prog isa :=
  .seq (.block [decCounter]) <| .seq (fprogB K.M (dblJ K.S K.R K.D)) (digit K)

/-- `step`, with the doubling `d` in place of the field program's. -/
def stepD (K : WinCfg) (d : Prog isa) : Prog isa :=
  .seq (.block [decCounter]) <| .seq d (digit K)

/-- An iteration, with the given doubling (`dd`) if any. -/
def stepOf (K : WinCfg) : Option (Prog isa) → Prog isa
  | none => step K
  | some d => stepD K d

/-- `R` to projective coordinates, through `E`: `(XZ : Y : Z³)`, and
`(0 : 1 : 0)` for the point at infinity. -/
def finish (K : WinCfg) : Prog isa :=
  .seq (.block (copyPt K.M.n K.E K.R)) <|
    .seq (fprogB K.M (fromJ K.S K.E (WinCfg.zeroPt K) K.R)) (.block (WinCfg.ySel K))

/-- `[k]P` into `R`, projective, from the digits at `K.bits`, with the
doubling `dd` if given (an allocated one, which does what `dblJ` does). -/
def window (K : WinCfg) (dd : Option (Prog isa) := none) : Prog isa :=
  .seq (table K) <|
  .seq (cache K) <|
  .seq (.block (infinity K K.D ++ [.movz .x .x19 (BitVec.ofNat 16 (64 * K.M.n)) 0])) <|
  .seq (digit K) <|
  .seq (.loop (stepOf K dd) (.nonzero .x .x19)) (finish K)

end VG.Impl.Weierstrass.AArch64.PubNaf
