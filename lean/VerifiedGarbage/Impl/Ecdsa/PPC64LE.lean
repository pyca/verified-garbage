module

public import VerifiedGarbage.Impl.Weierstrass.PPC64LE.LadderP
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.Spec.Ecdsa
public import VerifiedGarbage.Impl.Weierstrass.Layout.Mul

/-!
# ECDSA signing on PPC64LE

`vg_ecdsa_<curve>_sign(out, d, digest, k, scratch) -> r3` (ELFv2: the
arguments in `r3`–`r7`), for a curve whose field elements and scalars are `n`
64-bit words, from the code of `Impl/Weierstrass/PPC64LE.lean`, as on 32-bit
ARM (`Impl/Ecdsa/Arm.lean`):

1. the callee-saved registers the function uses (`r14`, which keeps `out`,
   and `r31`, the loops' counter) and the link register are saved in the
   working space's first 24 bytes, whose base then goes to `r3`, where the
   field arithmetic's functions take it and leave it; `k`, `d` and the hash
   are read big-endian into slots, and the constants (the moduli, `a`, `3b`,
   `G` and Montgomery's ones in Montgomery form, `R² mod n`, and the
   exponents `p - 2` and `n - 2`) are stored as immediates;
2. the bits of `k`, `p - 2` and `n - 2` are expanded into tables;
3. `R = [k]G` by the ladder from `R = O = (0 : 1 : 0)` (`ladderP`: by calls of
   the point functions for coordinates of at most 6 words), then
   `x = X Z^(p-2)` (Montgomery's form left by a multiplication by 1) and
   `r = x mod n` (a conditional subtraction, as `x < p < 2n`);
4. `s = k^(n-2) (e + r d) mod n`, in Montgomery form modulo `n`, then left;
5. the flag: `d` and `k` in `[1, n-1]`, `r ≠ 0` and `s ≠ 0`, as a mask, which
   selects `r ‖ s` or zeros for `out` (big-endian), and is returned as 0 or 1.

The field arithmetic is calls of the functions of `p` and `n`
(`Proof/Weierstrass/MontContract.lean`), which use the `64 n` bytes below byte 4096
for themselves; every slot is below them, and the tables of bits are past
byte 4096. `R = O` (impossible for `k` in `[1, n-1]`) gives `Z = 0`, so
`x = 0` and `r = 0`, as the specification says. Everything is computed
whatever the flag, and only the pointers may affect timing.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.PPC64LE

open VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass.PPC64LE VG.Impl.Weierstrass

/-- `-m⁻¹ mod 2⁶⁴`, for odd `m`, by Newton's iteration. -/
def minv (m : Nat) : Nat :=
  let inv := (List.range 6).foldl (fun x _ => x * ((2 + 2 ^ 64 - m * x % 2 ^ 64) % 2 ^ 64) % 2 ^ 64) 1
  (2 ^ 64 - inv) % 2 ^ 64

/-- The working space: the saved registers in bytes `[0, 24)`, then slots of
`n` words (`slot n i`) from byte 64, then the field arithmetic's own working
space (its `64 n` bytes below byte 4096), then the tables of bits
(`bitsAt`). -/
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

/-- The table of the bits of `k` (`j = 0`), `p - 2` (1) and `n - 2` (2), of
`64 n` bytes each: after the field arithmetic's own working space. -/
def bitsAt (n j : Nat) : Nat := 4096 + 64 * n * j

/-- The registers holding the arguments the setup reads: `k`, `d` and the
hash (the functions built on the signature's code read some of them from the
same argument), the working space's (`sc`), and the slot, if any, holding a
hash to shift. -/
structure Args where
  k : Reg
  d : Reg
  e : Reg
  sc : Reg
  hs : Option Nat := none

/-- The signature's: `(out, d, digest, k, scratch)`, shifting the hash in
`E`. -/
abbrev Args.sign : Args := ⟨.r6, .r4, .r5, .r7, some E⟩

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

/-- The callee-saved registers the function writes, and where they are saved
(`lr` is saved after them, at byte 16). -/
def saved : List (Reg × Nat) := [(.r14, 0), (.r31, 8)]

/-- Where `lr` is saved. -/
def lrAt : Nat := 16

/-- The constants, and `R = (0 : 1 : 0)`: slots and values. -/
def consts : List (Nat × Nat) :=
  [(MP, c.C.p), (MN, c.C.n), (ZERO, 0), (ONE, 1), (ONEP, c.mont 1), (AP, c.mont c.C.a),
    (B3P, c.mont (3 * c.C.b)), (GX, c.mont c.C.gx), (GY, c.mont c.C.gy), (R2N, c.R * c.R % c.C.n),
    (ONEN, c.R % c.C.n), (EXPP, c.C.p - 2), (EXPN, c.C.n - 2), (RX, 0), (RY, c.mont 1), (RZ, 0)]

/-- The saves, at `[sc]`, and `out` (`r3`) to `r14`, the working space to `r3`. -/
def saveCode (sc : Reg) : List Instr :=
  saved.map (fun (r, d) => .store .d r sc d) ++ [.mflr .r0, .store .d .r0 sc lrAt, mov .r14 .r3, mov .r3 sc]

/-- The slot `hs` (if any) shifted right by the bits of a hash's `len`
bytes that are not `e`'s (`sh`: none but for P-521's 7). -/
def shiftCode : Option Nat → List Instr
  | none => []
  | some i => if c.sh = 0 then [] else shrWords c.n (c.sl i) c.sh

/-- The saves; `k`, `d` and the hash (`len` bytes each) read from the
registers `A` names, and the slot `A.hs` holding a hash shifted; the
constants stored; and `R = (0 : 1 : 0)` and the flag (a word) set to all
ones. -/
def setupWith (A : Args) : List Instr :=
  saveCode A.sc ++
  loadBytes c.C.len c.n (c.sl K) A.k ++ loadBytes c.C.len c.n (c.sl D) A.d ++
  loadBytes c.C.len c.n (c.sl E) A.e ++ c.shiftCode A.hs ++
  c.consts.flatMap (fun (i, x) => VG.Impl.Mont.PPC64LE.setConst c.n (c.sl i) x) ++
  ([.li .r4 0, .subi .r4 .r4 1, .store .d .r4 wb (c.sl FLAG)] : List Instr)

/-- The setup of `sign`. -/
def setup : List Instr := c.setupWith .sign

/-- The mask `r5` of `[a] ≠ 0` (all ones if it is not zero), through `r4`:
the words or'ed, then the top bit of `x | -x`, negated. -/
def nonzero (a : Nat) : List Instr :=
  ([.load .d .r5 wb a] : List Instr) ++
  ((List.range (c.n - 1)).flatMap fun j => [.load .d .r4 wb (a + 8 * (j + 1)), .logic .or .r5 .r5 .r4]) ++
  ([.li .r4 0, .sub .r4 .r4 .r5, .logic .or .r4 .r4 .r5, .lsr .d .r4 .r4 63, .li .r5 0,
    .sub .r5 .r5 .r4] : List Instr)

/-- Digit `j` of `[a] - [m]` (32-bit digits), from the carry `r6` (1 for
the first), its carry to `r6`; `r0 = 2³² - 1`. -/
def ltDigit (m a j : Nat) : List Instr :=
  [.load .w .r7 wb (a + 4 * j), .load .w .r8 wb (m + 4 * j), .add .r7 .r7 .r0, .sub .r7 .r7 .r8,
    .add .r7 .r7 .r6, .lsr .d .r6 .r7 32]

/-- The mask `r5` of `[a] < [m]` (all ones if it is): the carry out of
`[a] - [m]` digit by digit is 0 if it borrowed. -/
def ltM (m a : Nat) : List Instr :=
  VG.Impl.Mont.PPC64LE.mask32 ++ [.li .r6 1] ++ (List.range (2 * c.n)).flatMap (ltDigit m a) ++ [.subi .r5 .r6 1]

/-- The mask `r5` of `[a] < n`. -/
def ltN (a : Nat) : List Instr := c.ltM (c.sl MN) a

/-- The flag `&=` the mask `r5`, through `r4`. -/
def andFlag : List Instr :=
  [.load .d .r4 wb (c.sl FLAG), .logic .and .r4 .r4 .r5, .store .d .r4 wb (c.sl FLAG)]

/-- `[a]` is in `[1, n-1]`: the flag `&=` both masks (the first kept in `r9`). -/
def checkRange (a : Nat) : List Instr :=
  c.ltN a ++ ([mov .r9 .r5] : List Instr) ++ c.nonzero a ++ ([.logic .and .r5 .r5 .r9] : List Instr) ++ c.andFlag

/-- `[a] ≠ 0`: the flag `&=` its mask. -/
def checkNonzero (a : Nat) : List Instr := c.nonzero a ++ c.andFlag

/-- `x = X Z⁻¹`, `r = x mod n`, `k R mod n`, and the checks of `d`, `k`, `r`. -/
def middle : Prog isa :=
  progs [mulCall c.SP (c.sl XM) (c.sl RX) (c.sl ACC),
    mulCall c.SP (c.sl X) (c.sl XM) (c.sl ONE),
    addCall c.SN (c.sl RR) (c.sl X) (c.sl ZERO),
    mulCall c.SN (c.sl KM) (c.sl K) (c.sl R2N),
    .block (c.checkRange (c.sl D) ++ c.checkRange (c.sl K) ++ c.checkNonzero (c.sl RR))]

/-- The callee-saved registers and `lr` restored, through `r0`. -/
def restore : List Instr :=
  [.load .d .r0 wb lrAt, .mtlr .r0] ++ saved.map fun (r, d) => .load .d r wb d

/-- `r ‖ s` (or zeros) to `out` (in `r14`), the flag's low bit to `r3`, and
the callee-saved registers restored. -/
def finish : List Instr :=
  ([.load .d .r10 wb (c.sl FLAG)] : List Instr) ++
  storeBytes c.C.len c.n .r14 0 (c.sl RR) ++ storeBytes c.C.len c.n .r14 c.C.len (c.sl SS) ++
  ([.li .r4 1, .logic .and .r4 .r10 .r4] : List Instr) ++ restore ++ [mov .r3 .r4]

/-- `s = k⁻¹ (e + r d) mod n`, with `k⁻¹ R` in `ACC`, and its check. -/
def scalar : Prog isa :=
  progs [mulCall c.SN (c.sl RM) (c.sl RR) (c.sl R2N),
    mulCall c.SN (c.sl DM) (c.sl D) (c.sl R2N),
    mulCall c.SN (c.sl EM) (c.sl E) (c.sl R2N),
    mulCall c.SN (c.sl TT) (c.sl RM) (c.sl DM),
    addCall c.SN (c.sl TT) (c.sl TT) (c.sl EM),
    mulCall c.SN (c.sl SM) (c.sl ACC) (c.sl TT),
    mulCall c.SN (c.sl SS) (c.sl SM) (c.sl ONE),
    .block (c.checkNonzero (c.sl SS) ++ c.finish)]

/-- `vg_ecdsa_<curve>_sign`. -/
def signWith (generator : Prog isa) : Prog isa :=
  .seq (.block c.setup) <|
  .seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n)) <|
  .seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n)) <|
  .seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n)) <|
  .seq generator <|
  .seq (pow c.powP c.SP) <|
  .seq c.middle <|
  .seq (pow c.powN c.SN) c.scalar

/-! ## `vg_<curve>_mul`

`[k]Q` (`Proof/Weierstrass/MulContract.lean`) as a function, which the signature,
the public key, ECDH and verification call: the ladder of `ladderP`, its
point at `ACC`, `PT`, `ONEP` (a copy of `Q`, which the contract has in
`R`'s first two slots), over the bits of `k` at `K`'s slot. It keeps `r31`
and `lr` past the numbered slots (slot 45's place, the start of the
contract's tail, below the point functions' slots and the field
arithmetic's own working space), and writes no other callee-saved register,
so a caller's `out` in `r14` stays known to be public through the call; it
returns with `r3` the working space. -/

/-- The ladder of `vg_<curve>_mul`: the signature's, from the point at `ACC`,
`PT`, `ONEP`. -/
def mulLadder : LadderCfg := { c.ladderCfg with G := c.pt ACC PT ONEP }

/-- Where `vg_<curve>_mul` keeps `r31` and `lr`: past the numbered slots. -/
def mulAt31 : Nat := c.sl nslots
def mulAtLr : Nat := c.sl nslots + 8

/-- `vg_<curve>_mul`'s body: the table of `k`'s bits, `Q` (in `R`'s first
two slots) copied to `ACC` and `PT`, `R = O = (0 : 1 : 0)` (from zero and
one), then `R = [k]Q` by the ladder. -/
def mulBody : Prog isa :=
  .seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n)) <|
  .seq (.block (copy c.n (c.sl ACC) (c.sl RX) ++ copy c.n (c.sl PT) (c.sl RY) ++
    copy c.n (c.sl RX) (c.sl ZERO) ++ copy c.n (c.sl RY) (c.sl ONEP) ++ copy c.n (c.sl RZ) (c.sl ZERO)))
    (Point.ladderP c.mulLadder c.SP)

/-- `vg_<curve>_mul`: `r31` and `lr` kept around the body, through `r0`. -/
def mulFn : Prog isa :=
  .seq (.block [.store .d .r31 wb c.mulAt31, .mflr .r0, .store .d .r0 wb c.mulAtLr]) <|
  .seq c.mulBody (.block [.load .d .r0 wb c.mulAtLr, .mtlr .r0, .load .d .r31 wb c.mulAt31])

/-- A call of `vg_<curve>_mul` (`C`'s) on the point at `px`, `py`: the point
copied to `R`'s first two slots, then the call, on the working space in
`r3`. -/
def mulAt (C : Impl.Weierstrass.Mul.Curve) (px py : Nat) : Prog isa :=
  .seq (.block (copy c.n (c.sl RX) (c.sl px) ++ copy c.n (c.sl RY) (c.sl py)))
    (.call s!"vg_{C.curve}_mul" c.mulFn)

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
  | none => Point.ladderP { c.ladderCfg with G := c.pt px py ONEP } c.SP c.qA0

/-- `R = [k]G`: `qMul` from `G`. -/
def gen : Prog isa := c.qMul GX GY

/-- Signing with `gen`. -/
def sign : Prog isa := c.signWith c.gen

end Cfg

end VG.Impl.Ecdsa.PPC64LE
