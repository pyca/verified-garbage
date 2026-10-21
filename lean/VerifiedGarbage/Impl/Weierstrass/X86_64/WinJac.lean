module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.CachedJac
public import VerifiedGarbage.Impl.Weierstrass.X86_64.TCombJ
public import VerifiedGarbage.Impl.X86_64Scal

/-!
# Short Weierstrass curves on x86-64: scalar multiplication by 5-bit windows in Jacobian coordinates

`[k]P` for a point `P` known only at run time, of a curve whose group has
prime order `n` (every point but `O` has order `n`), for `1 ≤ k < n`: the
window method of `Impl/Weierstrass/X86_64/Window.lean` with windows of 5 bits
and every point in Jacobian coordinates, so that no addition is complete.

The scalar is recoded as `k' = k + 16 Σ_{j<J} 32^j` (`offset`), whose 5-bit
windows `k'_j` give the digits `d_j = k'_j - 16 ∈ [-16, 15]` with
`k = Σ_j d_j 32^j`, read as the comb reads its digits (`TCombCfg.digit`,
`Impl/Weierstrass/X86_64/TComb.lean`, with `w = 5`).

The table holds `[m]P` for `m = 1 … 16`, entry `m` at `tbl + 40 n (m - 1)`:
`X`, `Y`, `Z` in Jacobian coordinates and the powers `Z²` and `Z³` the
additions use (`build`). `[1]P` is `P` (`Z = 1`); `[2]P` is its co-Z doubling
(DBLU, Meloni–Goundar, `dbluOps`), which also leaves `D = P` with the same
`Z`; and `[m + 1]P = P + [m]P` by the co-Z addition (ZADDU, `zadduOps`) of
`D` and `T`, which leaves `D = P` with the sum's `Z` for the next one. It is
right since `[m]P ≠ ±P` for `2 ≤ m ≤ 15 < n - 1`. The entry is stored at an
address computed from the public counter `rbx` (`entryAddr`).

The top digit's entry, selected as below, is `R` (`first`: zeros, i.e. `O`,
for the digit zero); then, for `j = J - 2` down to `0`, `R = 32 R + [d_j]P`
(`step`): five doublings in place (`dbl`, a loop whose
count is in the bits of `rbx` above the window index); the entry of `|d_j|`
selected in constant time into `T` (all five coordinates: every entry is
loaded, 16 bytes at a time, or 32 with AVX2, and kept under the mask of its
index, `selPassAt`, `selPassY`), and its `Y` negated for a negative digit
(`TCombCfg.negY`); `D = R + T` by Jacobian addition with `T`'s cached powers
(`CachedJac.head`, `jacTail`); `D = T` where `R` is `O` (`nzMask`); and
`R = D` unless the digit is zero (`eqMask 0`). The addition is right unless
`R = ±T`: with `R = [32 m]P` for the scalar `m` of the digits above `j`, that
would need `32 m ≡ ±d_j (mod n)`, which the recoding's bounds rule out for a
nonzero `R` and digit (the proof's exception argument, for each curve).

At the end `R = (XZ : Y : Z³)` in projective coordinates, with `Y = 1` where
`Z = 0` (`TCombCfg.outFix`, `outOps`). Every address and branch depends only
on `rdi` and the public counter `rbx`.

Where the selection loads 32 bytes at a time and the addition's field
operations and the masks are scalar code (`pipeOk`), the iterations select
the next digit's entry while they add (`windowP`): the entry of digit
`j - 1` is kept in the accumulators, under the mask of its magnitude, in
parts spread between the field operations of digit `j`'s addition
(`selChunk`, by `fprogBI` without forwarding), then stored to `T` and its
`Y` negated after the masks (`finNext`), for the next iteration's addition
after its doublings, which do not write `T`. The addition's
multiplications wait on each other; the selection's loads fill their gaps.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.X86_64

open VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass

/-- What the window method needs: the field, the slots of the additions, the
point `P` (affine: `P.z` holds Montgomery's one), the accumulator `R`, the
sum `D` (while the table is built, `P` sharing `T`'s `Z`), the selected
entry's five coordinates at `T`, `T + 8 n`, … (`X`, `Y`, `Z`, `Z²`, `Z³`), a
slot for `-y` and one holding zero, the table of the scalar's bits, the table
of points, the number of digits `J` (at least 2), Montgomery's one, and
whether the selection loads 32 bytes at a time with AVX2. -/
structure JacWinCfg where
  M : Mod
  S : RcbSlots
  P : Pt
  R : Pt
  D : Pt
  T : Nat
  neg : Nat
  zero : Nat
  bits : Nat
  tbl : Nat
  J : Nat
  one : Nat
  avx2 : Bool
  /-- Whether the iterations select the next digit's entry while they add,
  where `pipeOk` allows it. -/
  pipe : Bool := false

namespace JacWinCfg

variable (K : JacWinCfg)

/-- `16 Σ_{j<J} 32^j`, the recoding's offset. -/
def offset (J : Nat) : Nat := 16 * ((32 ^ J - 1) / 31)

/-- The bytes between entries of the table: five coordinates of `n` words. -/
def st : Nat := 40 * K.M.n

/-- The selected entry, as a Jacobian point. -/
def E : Pt := ⟨K.T, K.T + 8 * K.M.n, K.T + 16 * K.M.n⟩

/-- The selected entry's `Z²`, followed by its `Z³`. -/
def z2 : Nat := K.T + 24 * K.M.n

/-- The window method as the comb sees it, for the digits and the negation. -/
def tc : TCombCfg where
  M := K.M
  S := K.S
  A := K.R
  E := K.E
  D := K.D
  neg := K.neg
  zero := K.zero
  bits := K.bits
  kbytes := 5 * K.J
  tsym := ""
  w := 5
  J := K.J
  start := (0, 0)
  one := K.one

/-- The 16-byte pieces of an entry, the last its last 16 bytes. -/
def np16 : Nat := (5 * K.M.n + 1) / 2

/-- Where piece `c` of an entry is. -/
def po (c : Nat) : Nat := if c + 1 < K.np16 then 16 * c else K.st - 16

/-- The 32-byte pieces of an entry, piece `c` at `16 qY np16 c` bytes. -/
def np32 : Nat := (K.np16 + 1) / 2

/-- The entry of the magnitude in `r8` (from 1; none for 0) into `T`, from the
table at `rdx = rdi + tbl`: without AVX2, in one pass if its pieces fit the 14
accumulators, else in two, its first 8 pieces then the others (for six
words, 15 pieces). -/
def select : List Instr :=
  [.mov .rdx (.reg .rdi), .alu .add .rdx (.imm (BitVec.ofNat 32 K.tbl))] ++
  if K.avx2 then selPassY K.T 16 K.st K.np32 (qY K.np16)
  else if K.np16 ≤ 14 then selPassAt K.T 16 K.st K.np16 K.po
  else selPassAt K.T 16 K.st 8 (16 * ·) ++ selPassAt K.T 16 K.st (K.np16 - 8) (fun c => 16 * (8 + c))

/-- `rdx = rdi + tbl + st (rbx - 1)`: entry `rbx`'s address, through `rax` and `rcx`. -/
def entryAddr : List Instr :=
  [.mov .rax (.reg .rbx), .alu .sub .rax (.imm 1), .mov32 .rcx (.imm (BitVec.ofNat 32 K.st)), .mul .rcx,
    .mov .rdx (.reg .rdi), .alu .add .rdx (.imm (BitVec.ofNat 32 K.tbl)), .alu .add .rdx (.reg .rax)]

/-- `T`'s five coordinates into entry `rbx`, through `rax`, `rcx` and `rdx`. -/
def storeEntry : List Instr :=
  K.entryAddr ++ (List.range (5 * K.M.n)).flatMap fun i =>
    [.mov .rax (.mem (sc (K.T + 8 * i))), .store (tblAt (8 * i)) .rax]

/-- `T`'s `Z³`, after its `Z²`. -/
def zz : Nat := K.z2 + 8 * K.M.n

/-- Co-Z doubling (DBLU) of the affine `P` (`Z = 1`) for `a = -3`: `B = x²`,
`E = y²`, `L = E²`, `S = 4 x E` (in `t3`), `M = 3 (B - 1)`, then
`T = (M² - 2 S, M (S - X) - 8 L, 2 y) = 2 P` and its `Z²`, `Z³`, with `8 L` in
`t2`: `(S, 8 L)` is `P` with `T`'s `Z`. -/
def dbluOps : List FOp :=
  [.mul K.S.t0 K.P.x K.P.x, .mul K.S.t1 K.P.y K.P.y, .mul K.S.t2 K.S.t1 K.S.t1,
   .mul K.S.t3 K.P.x K.S.t1, .add K.S.t3 K.S.t3 K.S.t3, .add K.S.t3 K.S.t3 K.S.t3,
   .sub K.S.t4 K.S.t0 K.P.z, .add K.S.t5 K.S.t4 K.S.t4, .add K.S.t4 K.S.t5 K.S.t4,
   .mul K.E.x K.S.t4 K.S.t4, .sub K.E.x K.E.x K.S.t3, .sub K.E.x K.E.x K.S.t3,
   .sub K.S.t5 K.S.t3 K.E.x, .mul K.E.y K.S.t4 K.S.t5,
   .add K.S.t2 K.S.t2 K.S.t2, .add K.S.t2 K.S.t2 K.S.t2, .add K.S.t2 K.S.t2 K.S.t2,
   .sub K.E.y K.E.y K.S.t2, .add K.E.z K.P.y K.P.y,
   .mul K.z2 K.E.z K.E.z, .mul K.zz K.z2 K.E.z]

/-- Co-Z addition (ZADDU) of `D = (X1, Y1)` and `T = (X2, Y2)`, sharing `Z`:
`C = (X1 - X2)²`, `W1 = X1 C`, `W2 = X2 C`, `A1 = Y1 (W1 - W2)`; `T` becomes
`((Y1 - Y2)² - W1 - W2, (Y1 - Y2) (W1 - X3) - A1, Z (X1 - X2)) = D + T`, with
its `Z² = Z² C` and `Z³`, and `D` becomes `(W1, A1)`, the same point with
`T`'s new `Z`. -/
def zadduOps : List FOp :=
  [.sub K.S.t0 K.D.x K.E.x, .mul K.S.t1 K.S.t0 K.S.t0, .mul K.E.z K.E.z K.S.t0,
   .mul K.D.x K.D.x K.S.t1, .mul K.S.t3 K.E.x K.S.t1, .sub K.S.t4 K.D.y K.E.y,
   .mul K.S.t5 K.S.t4 K.S.t4, .sub K.S.t2 K.D.x K.S.t3, .mul K.D.y K.D.y K.S.t2,
   .sub K.E.x K.S.t5 K.D.x, .sub K.E.x K.E.x K.S.t3, .sub K.E.y K.D.x K.E.x,
   .mul K.E.y K.S.t4 K.E.y, .sub K.E.y K.E.y K.D.y,
   .mul K.z2 K.z2 K.S.t1, .mul K.zz K.z2 K.E.z]

/-- Entry `rbx` from entry `rbx - 1` in `T`, `D = P` sharing its `Z`:
`T = T + D` by ZADDU, stored; then `rbx + 1`, compared with 16. -/
def buildStep : Prog isa :=
  .seq (.block [.alu .add .rbx (.imm 1)]) <|
  .seq (ForwardField.programB K.M K.zadduOps) <|
  .block (K.storeEntry ++ [.alu .cmp .rbx (.imm 16)])

/-- The table: `T = P` (`Z = 1`) into entry 1; `T = 2 P` and `D = P` sharing
its `Z` by DBLU, into entry 2; then `T = T + D` by ZADDU into entries 3 to 16. -/
def build : Prog isa :=
  .seq (.block (copyPt K.M.n K.E K.P ++ copy K.M.n K.z2 K.P.z ++ copy K.M.n (K.z2 + 8 * K.M.n) K.P.z ++
    [.mov32 .rbx (.imm 1)] ++ K.storeEntry)) <|
  .seq (ForwardField.programB K.M K.dbluOps) <|
  .seq (.block (copy K.M.n K.D.x K.S.t3 ++ copy K.M.n K.D.y K.S.t2 ++ [.mov32 .rbx (.imm 2)] ++
    K.storeEntry)) <|
  .loop K.buildStep .ne

/-- One doubling of `R`, counted in the bits of `rbx` above the window index
(below 4096). -/
def dblStep (dbl : Pt → Prog isa) : Prog isa :=
  .seq (dbl K.R) (.block [.alu .sub .rbx (.imm 4096), .alu .cmp .rbx (.imm 4096)])

/-- `R = 32 R`: five doublings, `rbx` restored. -/
def dbls (dbl : Pt → Prog isa) : Prog isa :=
  .seq (.block [.alu .add .rbx (.imm (BitVec.ofNat 32 (5 * 4096)))]) (.loop (K.dblStep dbl) .ae)

/-- `D = R + T`, with `T`'s cached powers. -/
def addOps : List FOp := CachedJac.head K.M.n K.S K.R K.E K.z2 ++ jacTail K.S K.R K.E K.D

/-- Iteration `j = rbx - 1` (with `rbx` counting down from `J - 1`):
`R = 32 R + [d_j]P`. -/
def step (dbl : Pt → Prog isa) : Prog isa :=
  .seq (.block [.alu .sub .rbx (.imm 1)]) <|
  .seq (K.dbls dbl) <|
  .seq (.block (K.tc.digit ++ K.select)) <|
  .seq (.block K.tc.negY) <|
  .seq (ForwardField.programB K.M K.addOps) <|
  .block (nzMask K.M.n K.R.z ++ selPt K.M.n K.D K.E K.D ++
    K.tc.digit ++ eqMask 0 ++ selPt K.M.n K.R K.D K.R ++ [.alu .test .rbx (.reg .rbx)])

/-- `rbx = J - 1` and the top digit's entry into `R` (zeros, `O`, for the
digit zero). -/
def first : List Instr :=
  [.mov32 .rbx (.imm (BitVec.ofNat 32 (K.J - 1)))] ++ K.tc.digit ++ K.select ++ K.tc.negY ++
    copyPt K.M.n K.R K.E

/-- `[k]P` into `R`, in projective coordinates, for the table of the bits of
`k + offset J` at `K.bits`, each iteration selecting its own entry. -/
def window0 (dbl : Pt → Prog isa) : Prog isa :=
  .seq K.build <| .seq (.block K.first) <| .seq (.loop (K.step dbl) .ne) <|
  .seq (.block K.tc.outFix) (ForwardField.programB K.M K.tc.outOps)

/-! ## Selecting the next digit's entry during the addition -/

/-- The addition's field operations. -/
def nOps : Nat := K.addOps.length

/-- The entries selected after the addition's operations before `i`. -/
def chunkLo (i : Nat) : Nat := 16 * i / K.nOps

/-- `rdx = rdi + tbl`, the table's address. -/
def tblAddr : List Instr := [.mov .rdx (.reg .rdi), .alu .add .rdx (.imm (BitVec.ofNat 32 K.tbl))]

/-- Entries `lo + 1 … hi` kept in the accumulators under the mask of the
magnitude (`selEntryY`). -/
def selRange (lo hi : Nat) : List Instr :=
  (List.range (hi - lo)).flatMap fun e => selEntryY K.st K.np32 (qY K.np16) (lo + e + 1)

/-- After the addition's operation `i`: the table's address in `rdx` (the
operations keep nothing in registers, so each part computes it again), and
entries `chunkLo i + 1 … chunkLo (i + 1)` into the accumulators. -/
def selChunk (i : Nat) : List Instr :=
  if K.chunkLo (i + 1) = K.chunkLo i then [] else K.tblAddr ++ K.selRange (K.chunkLo i) (K.chunkLo (i + 1))

/-- Before digit `j = rbx`'s addition: the magnitude of digit `j - 1`
(`rbx` decremented around it) broadcast to `ymm13`, one to `ymm12` and the
counter `ymm14`, and the accumulators cleared (`selPassY`'s start). -/
def prepNext : List Instr :=
  [.alu .sub .rbx (.imm 1)] ++ K.tc.digit ++ [.alu .add .rbx (.imm 1)] ++
  [.vop (.vmovq .xmm13 .r8), .vop (.vpbroadcastd .l256 .xmm13 .xmm13), .mov32 .rcx (.imm 1),
    .vop (.vmovq .xmm12 .rcx), .vop (.vpbroadcastd .l256 .xmm12 .xmm12), .vop (.vmovdqa .l256 .xmm14 .xmm12)] ++
  ((List.range K.np32).map (fun c => .vop (.vbin .vpxor .l256 (selAcc c) (selAcc c) (selAcc c))) : List Instr)

/-- The accumulators stored to `T` (`selPassY`'s end). -/
def storeT : List Instr :=
  ((List.range K.np32).map (fun c => .vmovdquStore .l256 (sc (K.T + 16 * qY K.np16 c)) (selAcc c)) :
    List Instr) ++ [.vop .vzeroupper]

/-- After digit `j = rbx`'s masks: digit `j - 1`'s entry, selected into the
accumulators, stored to `T` and its `Y` negated for a negative digit (`rbx`
decremented around them); `ZF` for `j = 1`. -/
def finNext : List Instr :=
  [.alu .sub .rbx (.imm 1)] ++ (K.storeT ++ K.tc.digit) ++ K.tc.negY ++
    [.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm 1)]

/-- `D = T` where `R` is `O`, and `R = D` unless digit `rbx` is zero. -/
def masks : List Instr :=
  nzMask K.M.n K.R.z ++ selPt K.M.n K.D K.E K.D ++ K.tc.digit ++ eqMask 0 ++ selPt K.M.n K.R K.D K.R

/-- Iteration `j = rbx - 1` (`1 ≤ j ≤ J - 2`), digit `j`'s entry in `T`:
`R = 32 R + [d_j]P`, selecting digit `j - 1`'s entry during the addition
into `T`; `ZF` for `j = 1`. -/
def stepP (dbl : Pt → Prog isa) : Prog isa :=
  .seq (.block [.alu .sub .rbx (.imm 1)]) <|
  .seq (K.dbls dbl) <|
  .seq (.block K.prepNext) <|
  .seq (fprogBI K.M K.addOps K.selChunk 0) <|
  .block (K.masks ++ K.finNext)

/-- The last iteration, `j = 0`, its entry in `T`. -/
def stepLast (dbl : Pt → Prog isa) : Prog isa :=
  .seq (.block [.alu .sub .rbx (.imm 1)]) <|
  .seq (K.dbls dbl) <|
  .seq (ForwardField.programB K.M K.addOps) <|
  .block K.masks

/-- `first`, then digit `J - 2`'s entry into `T`, `rbx = J - 1`. -/
def firstP : List Instr :=
  K.first ++ [.alu .sub .rbx (.imm 1)] ++ K.tc.digit ++ K.select ++ K.tc.negY ++ [.alu .add .rbx (.imm 1)]

/-- `window0`, selecting each entry during the iteration before. -/
def windowP (dbl : Pt → Prog isa) : Prog isa :=
  .seq K.build <| .seq (.block K.firstP) <| .seq (.loop (K.stepP dbl) .ne) <| .seq (K.stepLast dbl) <|
  .seq (.block K.tc.outFix) (ForwardField.programB K.M K.tc.outOps)

/-- Where the iterations may select the next entry while they add: with
AVX2, three digits or more, and the addition's field operations and the
masks scalar code. -/
def pipeOk : Bool :=
  K.pipe && K.avx2 && decide (3 ≤ K.J) && K.masks.all scalarI && K.addOps.all fun op => scalCode (opProg K.M op)

/-- `[k]P` into `R`, in projective coordinates, for the table of the bits of
`k + offset J` at `K.bits`. -/
def window (dbl : Pt → Prog isa) : Prog isa :=
  if K.pipeOk then K.windowP dbl else K.window0 dbl

end JacWinCfg

end VG.Impl.Weierstrass.X86_64
