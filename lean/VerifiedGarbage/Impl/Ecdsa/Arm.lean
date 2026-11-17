module

public import VerifiedGarbage.Impl.Weierstrass.Arm.LadderP
public import VerifiedGarbage.Impl.Weierstrass.Arm.Window
public import VerifiedGarbage.Impl.Weierstrass.JacMul
public import VerifiedGarbage.Impl.Weierstrass.JacDblA
public import VerifiedGarbage.Impl.Weierstrass.Rcb0
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.Spec.Ecdsa
public import VerifiedGarbage.Impl.Weierstrass.Layout.Mul

/-!
# ECDSA signing on 32-bit ARM

`vg_ecdsa_<curve>_sign(out, d, digest, k, scratch) -> r0` (AAPCS: `out`,
`d`, `digest` and `k` in `r0`–`r3`, `scratch` on the stack at `[sp]`), for
a curve whose field elements and scalars are `n` 64-bit words (`2n` 32-bit
words; `n = 4` for the 256-bit curves), from the code of
`Impl/Weierstrass/Arm.lean`, as on x86 (`Impl/Ecdsa/X86.lean`):

1. the working space's base goes to `r12`, the callee-saved registers
   `r4`–`r11` and `lr` are saved in its first 36 bytes, and `out` goes to
   `lr`, which nothing else uses (so `out` stays known to be public through
   the computation's stores of secrets); `k`, `d`
   and the hash are read big-endian into slots, and the constants (the
   moduli, `a`, `3b`, `G` and Montgomery's ones in Montgomery form,
   `R² mod n`, and the exponents `p - 2` and `n - 2`) are stored as
   immediates;
2. the bits of `k`, `p - 2` and `n - 2` are expanded into tables;
3. `R = [k]G` (`gen`: by `vg_<curve>_mul`'s windows for a curve that has the
   function, else by the ladder from `R = O = (0 : 1 : 0)`, `ladderP`: by calls
   of the point functions for coordinates of at most 6 words), then
   `x = X Z^(p-2)` (Montgomery's form left by a multiplication by 1) and
   `r = x mod n` (a conditional subtraction, as `x < p < 2n`);
4. `s = k^(n-2) (e + r d) mod n`, in Montgomery form modulo `n`, then left;
5. the flag: `d` and `k` in `[1, n-1]`, `r ≠ 0` and `s ≠ 0`, as a mask, which
   selects `r ‖ s` or zeros for `out` (big-endian), and is returned as 0 or 1.

The field arithmetic is calls of the functions of `p` and `n`
(`Proof/Weierstrass/MontContract.lean`), which use the `64 n` bytes below byte 4096
for themselves (`wk`); every offset of a slot is below them, which `ldr`
and `str` reach from `r12`, and the tables of bits are past byte 4096.
`R = O` (impossible for `k` in `[1, n-1]`) gives `Z = 0`, so `x = 0` and
`r = 0`, as the specification says. Everything is computed whatever the
flag, and only the pointers may affect timing.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.Arm

open VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass

/-- `-m⁻¹ mod 2⁶⁴`, for odd `m`, by Newton's iteration. -/
def minv (m : Nat) : Nat :=
  let inv := (List.range 6).foldl (fun x _ => x * ((2 + 2 ^ 64 - m * x % 2 ^ 64) % 2 ^ 64) % 2 ^ 64) 1
  (2 ^ 64 - inv) % 2 ^ 64

/-- The working space: the saved registers in bytes `[0, 36)`, then
slots of `n` words (`slot n i`) from byte 64, then the field arithmetic's
own working space (`wkAt`, its `64 n` bytes below byte 4096), then the tables
of bits (`bitsAt`). Everything but the tables is within the 4096 bytes a
`ldr` or `str` reaches from `r12`; a table is reached from a register
(`bitMask`, `bits`). -/
def slot (n i : Nat) : Nat := 64 + 8 * n * i

/-! Slot numbers. -/
def MP := 0
def MN := 1
def TMP := 2
def ZERO := 3
def ONE := 4
def ONEP := 5
def AP := 6
def B3P := 7
def GX := 8
def GY := 9
def R2N := 10
def ONEN := 11
def EXPP := 12
def EXPN := 13
def RX := 14
def RY := 15
def RZ := 16
def DX := 17
def DY := 18
def DZ := 19
def TX := 20
def TY := 21
def TZ := 22
def T0 := 23
def T1 := 24
def T2 := 25
def T3 := 26
def T4 := 27
def T5 := 28
def ACC := 29
def PT := 30
def K := 31
def D := 32
def E := 33
def XM := 34
def X := 35
def RR := 36
def KM := 37
def RM := 38
def DM := 39
def EM := 40
def TT := 41
def SM := 42
def SS := 43
def FLAG := 44
/-- The number of slots. -/
def nslots := 45

/-- The field arithmetic's own working space (`Impl.Weierstrass.Mont.ownAt`):
the `64 n` bytes below byte 4096, after the slots. -/
def wkAt (n : Nat) : Nat := Mont.own n

/-- The table of the bits of `k` (`j = 0`), `p - 2` (1) and `n - 2` (2), of
`64 n` bytes each: after the field arithmetic's own working space. -/
def bitsAt (n j : Nat) : Nat := 4096 + 64 * n * j

/-- The registers holding the arguments the setup reads: `k`, `d` and the
hash (the functions built on the signature's code read some of them from the
same argument), and the working space's (`sc`), or `none` for the argument on
the stack; and the slot, if any, holding a hash to shift. -/
structure Args where
  k : Reg
  d : Reg
  e : Reg
  sc : Option Reg := none
  hs : Option Nat := none

/-- The signature's: `(out, d, digest, k, scratch)`, `scratch` on the stack,
shifting the hash in `E`. -/
abbrev Args.sign : Args := ⟨.r3, .r1, .r2, none, some E⟩

/-- A curve as the code has it: `n` words, its parameters, and the
functions of its arithmetic modulo `p` and `n` (`SP`, `SN`). -/
structure Cfg where
  n : Nat
  C : Spec.Weierstrass.Curve
  SP : Impl.Weierstrass.Mont.Modulus
  SN : Impl.Weierstrass.Mont.Modulus
  /-- The curve whose `vg_<curve>_mul` (`Proof/Weierstrass/MulContract.lean`) computes
  `[k]Q` (`mulFn`), which the signature, the public key, ECDH and
  verification call (`gen`, `qMul`), if any; else they run the ladder inline. -/
  mul : Option Impl.Weierstrass.Mul.Curve
  /-- Whether the field operations are calls of the `_umaal` variants
  of `vg_<curve>_{mul,add,sub}_mod_<p|n>` (`Impl/Weierstrass/Arm/Mont.lean`),
  and so the point functions and `vg_<curve>_mul` called too. -/
  umaal : Bool := false

namespace Cfg

variable (c : Cfg)

/-- `R = 2^(64 n)`. -/
def R : Nat := 2 ^ (64 * c.n)

/-- The bits of the hash's `len` bytes that are not `e`'s: `8 len - N`, for
`N` the bits of `n` (0 but for P-521's 7). -/
def sh : Nat := 8 * c.C.len - Spec.Ecdsa.nBits c.C

/-- `x R mod p`. -/
def mont (x : Nat) : Nat := x * c.R % c.C.p

def sl (i : Nat) : Nat := slot c.n i

def wk : Nat := wkAt c.n

def MP' : Mod := { n := c.n, mo := c.sl MP, tmp := c.sl TMP, minv := BitVec.ofNat 64 (minv c.C.p) }
def MN' : Mod := { n := c.n, mo := c.sl MN, tmp := c.sl TMP, minv := BitVec.ofNat 64 (minv c.C.n) }

def pt (x y z : Nat) : Pt := ⟨c.sl x, c.sl y, c.sl z⟩

def rcbSlots : RcbSlots := ⟨c.sl AP, c.sl B3P, c.sl T0, c.sl T1, c.sl T2, c.sl T3, c.sl T4, c.sl T5⟩

/-- Process every encoded scalar bit, including invalid encodings, but no word padding. -/
def ladderCfg : LadderCfg where
  M := c.MP'
  S := c.rcbSlots
  G := c.pt GX GY ONEP
  R := c.pt RX RY RZ
  D := c.pt DX DY DZ
  T := c.pt TX TY TZ
  bits := bitsAt c.n 0
  nbits := 8 * c.C.len

def powP : PowCfg := ⟨c.MP', c.sl ACC, c.sl PT, c.sl RZ, c.sl ONEP, bitsAt c.n 1, 64 * c.n⟩
def powN : PowCfg := ⟨c.MN', c.sl ACC, c.sl PT, c.sl KM, c.sl ONEN, bitsAt c.n 2, 64 * c.n⟩

/-- The callee-saved registers, and where they are saved. -/
def saved : List (Reg × Nat) :=
  [(.r4, 0), (.r5, 4), (.r6, 8), (.r7, 12), (.r8, 16), (.r9, 20), (.r10, 24), (.r11, 28), (.lr, 32)]

/-- The constants, and `R = (0 : 1 : 0)`: slots and values. -/
def consts : List (Nat × Nat) :=
  [(MP, c.C.p), (MN, c.C.n), (ZERO, 0), (ONE, 1), (ONEP, c.mont 1), (AP, c.mont c.C.a),
    (B3P, c.mont (3 * c.C.b)), (GX, c.mont c.C.gx), (GY, c.mont c.C.gy), (R2N, c.R * c.R % c.C.n),
    (ONEN, c.R % c.C.n), (EXPP, c.C.p - 2), (EXPN, c.C.n - 2), (RX, 0), (RY, c.mont 1), (RZ, 0)]

/-- Saves them at `[r12]`. -/
def saveCode : List Instr := saved.map fun (r, d) => .str r wb d

/-- The working space's base to `r12`: from the stack argument, or from a
register. -/
def scStart (A : Args) : Instr :=
  match A.sc with
  | none => .ldrSp wb 0
  | some r => .mov wb (.reg r)

/-- The slot `hs` (if any) shifted right by the bits of a hash's `len`
bytes that are not `e`'s (`sh`: none but for P-521's 7). -/
def shiftCode : Option Nat → List Instr
  | none => []
  | some i => if c.sh = 0 then [] else shrWords c.n (c.sl i) c.sh

/-- The working space from its argument to `r12`; saves the callee-saved
registers there and moves `out` to `lr`; reads `k`, `d` and the hash (`len`
bytes each) from the registers `A` names, and shifts the slot `A.hs` holding
a hash; stores the constants; and sets `R = (0 : 1 : 0)` and the flag (a
word) to all ones. -/
def setupWith (A : Args) : List Instr :=
  [scStart A] ++ saveCode ++ ([.mov .lr (.reg .r0)] : List Instr) ++
  loadBytes c.C.len c.n (c.sl K) A.k ++ loadBytes c.C.len c.n (c.sl D) A.d ++
  loadBytes c.C.len c.n (c.sl E) A.e ++ c.shiftCode A.hs ++
  c.consts.flatMap (fun (i, x) => setConst c.n (c.sl i) x) ++
  ([.mov .r4 (.imm 0), .dp .sub .r4 .r4 (.imm 1), .str .r4 wb (c.sl FLAG)] : List Instr)

/-- The setup of `sign`. -/
def setup : List Instr := c.setupWith .sign

/-- The mask `r5` of `[a] ≠ 0` (all ones if it is not zero), through `r4`:
the words or'ed, then the top bit of `x | -x`, negated. -/
def nonzero (a : Nat) : List Instr :=
  ([.ldr .r5 wb a] : List Instr) ++
  ((List.range (2 * c.n - 1)).flatMap fun j => [.ldr .r4 wb (a + 4 * (j + 1)), .dp .orr .r5 .r5 (.reg .r4)]) ++
  ([.mov .r4 (.imm 0), .dp .sub .r4 .r4 (.reg .r5), .dp .orr .r4 .r4 (.reg .r5), .mov .r4 (.shifted .r4 .lsr 31),
    .mov .r5 (.imm 0), .dp .sub .r5 .r5 (.reg .r4)] : List Instr)

/-- Digit `j` of `[a] - n`, from the carry `r3` (1 for the first), its carry
to `r3`; `r7` and `r8` hold the words `j / 2` of `[a]` and of `n`. -/
def ltDigit (j : Nat) : List Instr :=
  [half .r4 .r7 (j % 2), half .r5 .r8 (j % 2), .dp .add .r4 .r4 (.reg .r6), .dp .sub .r4 .r4 (.reg .r5),
    .dp .add .r4 .r4 (.reg .r3), .mov .r3 (.shifted .r4 .lsr 16)]

/-- The mask `r5` of `[a] < [m]` (all ones if it is): the carry out of
`[a] - [m]` digit by digit is 0 if it borrowed. -/
def ltM (m a : Nat) : List Instr :=
  [mask16, .mov .r3 (.imm 1)] ++
  ((List.range (2 * c.n)).flatMap fun k =>
    ([.ldr .r7 wb (a + 4 * k), .ldr .r8 wb (m + 4 * k)] : List Instr) ++ ltDigit (2 * k) ++ ltDigit (2 * k + 1)) ++
  ([.dp .sub .r5 .r3 (.imm 1)] : List Instr)

/-- The mask `r5` of `[a] < n`. -/
def ltN (a : Nat) : List Instr := c.ltM (c.sl MN) a

/-- The flag `&=` the mask `r5`, through `r4`. -/
def andFlag : List Instr :=
  [.ldr .r4 wb (c.sl FLAG), .dp .and .r4 .r4 (.reg .r5), .str .r4 wb (c.sl FLAG)]

/-- `[a]` is in `[1, n-1]`: the flag `&=` both masks (the first kept in `r9`). -/
def checkRange (a : Nat) : List Instr :=
  c.ltN a ++ ([.mov .r9 (.reg .r5)] : List Instr) ++ c.nonzero a ++ ([.dp .and .r5 .r5 (.reg .r9)] : List Instr) ++ c.andFlag

/-- `[a] ≠ 0`: the flag `&=` its mask. -/
def checkNonzero (a : Nat) : List Instr := c.nonzero a ++ c.andFlag

/-- `x = X Z⁻¹`, `r = x mod n`, `k R mod n`, and the checks of `d`, `k`, `r`. -/
def middle : Prog isa :=
  progs [Mont.mulCall c.SP (c.sl XM) (c.sl RX) (c.sl ACC) c.umaal,
    Mont.mulCall c.SP (c.sl X) (c.sl XM) (c.sl ONE) c.umaal,
    Mont.addCall c.SN (c.sl RR) (c.sl X) (c.sl ZERO) c.umaal,
    Mont.mulCall c.SN (c.sl KM) (c.sl K) (c.sl R2N) c.umaal,
    .block (c.checkRange (c.sl D) ++ c.checkRange (c.sl K) ++ c.checkNonzero (c.sl RR))]

/-- The callee-saved registers restored. -/
def restore : List Instr := saved.map fun (r, d) => .ldr r wb d

/-- `r ‖ s` (or zeros) to `out` (in `lr`), the flag's low bit to `r0`, and
the callee-saved registers restored. -/
def finish : List Instr :=
  ([.ldr .r10 wb (c.sl FLAG)] : List Instr) ++
  storeBytes c.C.len c.n .lr 0 (c.sl RR) ++ storeBytes c.C.len c.n .lr c.C.len (c.sl SS) ++
  ([.dp .and .r0 .r10 (.imm 1)] : List Instr) ++ restore

/-- `s = k⁻¹ (e + r d) mod n`, with `k⁻¹ R` in `ACC`, and its check. -/
def scalar : Prog isa :=
  progs [Mont.mulCall c.SN (c.sl RM) (c.sl RR) (c.sl R2N) c.umaal,
    Mont.mulCall c.SN (c.sl DM) (c.sl D) (c.sl R2N) c.umaal,
    Mont.mulCall c.SN (c.sl EM) (c.sl E) (c.sl R2N) c.umaal,
    Mont.mulCall c.SN (c.sl TT) (c.sl RM) (c.sl DM) c.umaal,
    Mont.addCall c.SN (c.sl TT) (c.sl TT) (c.sl EM) c.umaal,
    Mont.mulCall c.SN (c.sl SM) (c.sl ACC) (c.sl TT) c.umaal,
    Mont.mulCall c.SN (c.sl SS) (c.sl SM) (c.sl ONE) c.umaal,
    .block (c.checkNonzero (c.sl SS) ++ c.finish)]

/-- `vg_ecdsa_<curve>_sign`. -/
def signWith (generator : Prog isa) : Prog isa :=
  .seq (.block c.setup) <|
  .seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n)) <|
  .seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n)) <|
  .seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n)) <|
  .seq generator <|
  .seq (pow c.powP c.SP c.umaal) <|
  .seq c.middle <|
  .seq (pow c.powN c.SN c.umaal) c.scalar


/-! ## `vg_<curve>_mul`

`[k]Q` (`Proof/Weierstrass/MulContract.lean`) as a function, which the signature,
the public key, ECDH and verification call, for the affine point `Q` in `R`'s
first two slots and the number `k` at `K`'s slot, in windows of `winW` bits:

1. the table of `k`'s bits (table 0);
2. the table of `[e]Q` for `e < 2^winW`, `24 n` bytes each in projective
   coordinates, past the three tables of bits (`winTbl`): `O = (0 : 1 : 0)`
   and `Q = (x : y : 1)`, then `[e + 1]Q = [e]Q + Q` by the complete addition
   of the curve for an affine point (`winAddM`), in the slots `D` and `T`;
3. from `R = O`, for the windows `j` from `winJ - 1` down to `0`,
   `R = 2^winW R + [k_j]Q`:
   * `R = 2^winW R` (`winQuad`): `R` in Jacobian coordinates, `winW`
     doublings by the Jacobian formulas for the curve's `a` (`winDbl`)
     between `D` and `T`, back in projective coordinates, and `Y = 1` where
     `Z = 0`;
   * the window `k_j` from the table of bits (`winDigit`, the comb's code),
     and its entry by a scan of the whole table into `T` (`scan`);
   * `D = R + T` by the complete addition of the curve (`winAdd`), copied
     to `R`.

The counters are `r11` (which the field arithmetic keeps) and, in the scan,
`r7`; every address is `r12` plus a constant or a multiple of a counter.
The function keeps the callee-saved registers `r4`–`r9`, `r11` and `lr`
past the numbered slots (slot 45's place, the start of the contract's tail,
below the field arithmetic's own working space), and `r10` in `lr`, which
the calls of the field arithmetic keep in registers alone (so a public
`r10`, such as a caller's `out`, stays known to be public through the stores
of secrets in memory); it returns with `r12` the working space. -/

/-- Where `vg_<curve>_mul` keeps the callee-saved registers but `r10`: past
the numbered slots. -/
def mulSaved : List (Reg × Nat) := (saved.filter (·.1 != .r10)).map fun (r, d) => (r, c.sl nslots + d)

/-- The bits of a window: four, or three for coordinates of more than six
words, whose sixteen multiples would not fit the working space past the
tables of bits. -/
def winW : Nat := if c.n ≤ 6 then 4 else 3

/-- The windows of an encoded scalar's `8 len` bits. -/
def winJ : Nat := (8 * c.C.len + c.winW - 1) / c.winW

/-- Where the table of the point's multiples is: past the three tables of
bits. -/
def winTbl : Nat := bitsAt c.n 3

/-- The Jacobian doubling of the curve: for `a = -3`, for `a = 0`, or for
any `a`. -/
def winDbl : RcbSlots → Pt → Pt → List FOp :=
  if c.C.a + 3 = c.C.p then dblJMul else if c.C.a = 0 then dblJ0 else dblJa

/-- The windows' complete addition: Algorithm 7 for `a = 0`, else
Algorithm 1. -/
def winAdd : RcbSlots → Pt → Pt → Pt → List FOp := if c.C.a = 0 then rcb0 else rcb

/-- The table's complete addition of the point, which is affine: Algorithm 8
for `a = 0`, else Algorithm 1. -/
def winAddM : RcbSlots → Pt → Pt → Pt → List FOp := if c.C.a = 0 then rcb0m else rcb

/-- Zero, as a point (`toJ` and `fromJ` add zero to copy). -/
def zeroPt : Pt := c.pt ZERO ZERO ZERO

/-- The comb whose code of a window's index and bits (`TCombCfg.windowIndex`,
`lastTest`, `horner`) reads the windows of `winW` bits of table 0: only its
`w`, `J` and table of bits are read. -/
def winK : TCombCfg :=
  { L := c.ladderCfg, F := c.SP, w := c.winW, J := c.winJ, tsym := "", start := (0, 0), one := c.sl ONEP,
    zero := c.sl ZERO, neg := c.sl TMP, u := c.umaal }

/-- The window `r11` of the scalar, into `r9`: of the bits it has, for the
last one. -/
def winDigit : Prog isa :=
  .seq (.block c.winK.windowIndex) <| .seq (.block c.winK.lastTest) <|
    .ite .eq (.block (c.winK.horner c.winK.topBits)) (.block (c.winK.horner c.winW))

/-- `k` doublings from the Jacobian `p` (alternately into `q` and back), then
`R` = the result in projective coordinates. -/
def winDbls : Nat → Pt → Pt → Prog isa
  | 0, p, _ => fprog c.SP (fromJ c.rcbSlots p c.zeroPt (c.pt RX RY RZ)) c.umaal
  | k + 1, p, q => .seq (fprog c.SP (c.winDbl c.rcbSlots p q) c.umaal) (winDbls k q p)

/-- `R = 2^winW R`: to Jacobian coordinates in `D`, the doublings between `D`
and `T`, back to `R`, then `Y = 1` where `Z` is zero. -/
def winQuad : Prog isa :=
  .seq (fprog c.SP (toJ c.rcbSlots (c.pt RX RY RZ) c.zeroPt (c.pt DX DY DZ)) c.umaal) <|
  .seq (c.winDbls c.winW (c.pt DX DY DZ) (c.pt TX TY TZ))
    (.block (c.nonzero (c.sl RZ) ++ ([.mov .r10 (.reg .r5)] : List Instr) ++
      sel (2 * c.n) (c.sl RY) (c.sl ONEP) (c.sl RY)))

/-- One window: `r11 -= 1`, `R = 2^winW R`, the entry `T` of the window, and
`R = R + T`. -/
def winStep : Prog isa :=
  .seq (.block [decCounter]) <| .seq c.winQuad <| .seq c.winDigit <|
  .seq (scan (c.sl TX) (6 * c.n) (2 ^ c.winW) c.winTbl) <|
  .seq (fprog c.SP (c.winAdd c.rcbSlots (c.pt RX RY RZ) (c.pt TX TY TZ) (c.pt DX DY DZ)) c.umaal)
    (.block (Point.copyPt c.n (c.pt RX RY RZ) (c.pt DX DY DZ) ++ [testCounter]))

/-- Entry `r11 + 1` of the table: `T = D + Q`, stored, and `D = T`; then
`r11 += 1`, and `Z` set once every entry is there. -/
def winBuildStep : Prog isa :=
  .seq (fprog c.SP (c.winAddM c.rcbSlots (c.pt DX DY DZ) (c.pt RX RY ONEP) (c.pt TX TY TZ)) c.umaal) <|
  .block (entryPtr (c.winTbl + 24 * c.n) (24 * c.n) ++ storePt c.n 0 (c.pt TX TY TZ) ++
    Point.copyPt c.n (c.pt DX DY DZ) (c.pt TX TY TZ) ++
    ([.dp .add .r11 .r11 (.imm 1), .cmp .r11 (.imm (BitVec.ofNat 32 (2 ^ c.winW - 1)))] : List Instr))

/-- The table: `O`, `Q`, then `[e]Q` for `e` from 2. -/
def winBuild : Prog isa :=
  .seq (.block (farPtr .r5 c.winTbl ++ storePt c.n 0 (c.pt ZERO ONEP ZERO) ++
    storePt c.n (24 * c.n) (c.pt RX RY ONEP) ++ Point.copyPt c.n (c.pt DX DY DZ) (c.pt RX RY ONEP) ++
    ([.mov .r11 (.imm 1)] : List Instr)))
    (.loop c.winBuildStep .ne)

/-- `vg_<curve>_mul`'s body: the table of `k`'s bits, the table of the
multiples of `Q` (in `R`'s first two slots), `R = O`, then `R = [k]Q` by the
windows. -/
def mulBody : Prog isa :=
  .seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n)) <|
  .seq c.winBuild <|
  .seq (.block (Point.copyPt c.n (c.pt RX RY RZ) (c.pt ZERO ONEP ZERO) ++
    ([.mov .r11 (.imm (BitVec.ofNat 32 c.winJ))] : List Instr)))
    (.loop c.winStep .ne)

/-- `vg_<curve>_mul`: the working space from `r0` to `r12`, the callee-saved
registers kept around the body (`mulSaved`, and `r10` in `lr`). -/
def mulFn : Prog isa :=
  .seq (.block (.mov wb (.reg .r0) :: c.mulSaved.map fun (r, d) => .str r wb d)) <|
  .seq (.block [.mov .lr (.reg .r10)]) <|
  .seq c.mulBody <|
  .seq (.block [.mov .r10 (.reg .lr)]) (.block (c.mulSaved.map fun (r, d) => .ldr r wb d))

/-- A call of `vg_<curve>_mul` (`C`'s) on the point at `px`, `py`: the point
copied to `R`'s first two slots, `lr` kept in `r10` across the call, as the
calls of the point and Montgomery functions do. -/
def mulAt (C : Impl.Weierstrass.Mul.Curve) (px py : Nat) : Prog isa :=
  .seq (.block (copy (2 * c.n) (c.sl RX) (c.sl px) ++ copy (2 * c.n) (c.sl RY) (c.sl py) ++
    [.mov .r10 (.reg .lr), .mov .r0 (.reg wb)])) <|
  .seq (.call (s!"vg_{C.curve}_mul" ++ if c.umaal then "_umaal" else "") c.mulFn) (.block [.mov .lr (.reg .r10)])

/-- Whether `qMul`'s inline ladder doubles and adds by the point functions
for `a = 0` (`vg_<curve>_point_a0_double`, `vg_<curve>_point_a0_add_affine`):
for a curve without `vg_<curve>_mul` whose `a` is zero and whose
coordinates fit the point functions' slots. -/
def qA0 : Bool := c.mul.isNone && (c.C.a == 0 && decide (c.n ≤ 6))

/-- `R = [k]P` for the point `P` at `px`, `py`, `ONEP` and the number `k` at
`K`'s slot: a call of `vg_<curve>_mul` if the curve has it (`Cfg.mul`), else
the ladder inline, from the table of `k`'s bits (by the point functions for
`a = 0` if `qA0`: `P` is affine). -/
def qMul (px py : Nat) : Prog isa :=
  match c.mul with
  | some C => c.mulAt C px py
  | none => Point.ladderP { c.ladderCfg with G := c.pt px py ONEP } c.SP c.qA0 c.umaal

/-- `R = [k]G`: `qMul` from `G`. -/
def gen : Prog isa := c.qMul GX GY

/-- Signing with `gen`. -/
def sign : Prog isa := c.signWith c.gen

end Cfg

end VG.Impl.Ecdsa.Arm
