module

public import VerifiedGarbage.TCB.VectorCrypto -- shake: keep (re-exports the existing Arm names below)

/-!
# AArch64 AdvSIMD values and the cryptographic functions of the Arm ARM

**Trusted.** Helpers for the semantics of the AdvSIMD and cryptographic
instructions in `TCB/AArch64/Isa.lean`: the lanes of a 128-bit vector
register, and the shared pseudocode functions that the Arm Architecture
Reference Manual for A-profile (DDI 0487) uses in the descriptions of the
cryptographic instructions (chapter J1, "shared/functions/crypto").

Lanes are numbered from the least significant, as the pseudocode's
`Elem[vector, e, size]` does: lane `e` of size `size` is bits
`(e+1)*size-1 : e*size`. On a little-endian machine, lane `e` of a register
loaded by `LDR (immediate, SIMD&FP)` holds the `e`-th `size`-bit value in
memory.
-/

@[expose] public section

namespace VG.AArch64

-- Keep the existing names as aliases of the architecture-independent values.
export VectorCrypto (vbyte ofVBytes aesXtimes aesMul aesInv ofBits8 aesSbox aesInvSbox
  aesMapBytes aesShiftRows aesInvShiftRows aesMixWith aesMixColumns aesInvMixColumns polyMul)

/-- `Elem[x, e, 16]`: halfword `e` of `x`. -/
def vhalf (x : BitVec 128) (e : Nat) : BitVec 16 := x.extractLsb' (16 * e) 16

/-- `Elem[x, e, 32]`: word `e` of `x`. -/
def vword (x : BitVec 128) (e : Nat) : BitVec 32 := x.extractLsb' (32 * e) 32

/-- `Elem[x, e, 64]`: doubleword `e` of `x`. -/
def vdword (x : BitVec 128) (e : Nat) : BitVec 64 := x.extractLsb' (64 * e) 64

/-- The vector whose halfword `e` is `f e`. -/
def ofVHalves (f : Nat → BitVec 16) : BitVec 128 :=
  f 7 ++ f 6 ++ f 5 ++ f 4 ++ f 3 ++ f 2 ++ f 1 ++ f 0

/-- The vector whose words are `w0` (bits 31:0), `w1`, `w2`, `w3` (bits 127:96). -/
def ofVWords (w0 w1 w2 w3 : BitVec 32) : BitVec 128 := w3 ++ w2 ++ w1 ++ w0

/-- The vector whose doublewords are `d0` (bits 63:0) and `d1` (bits 127:64). -/
def ofVDwords (d0 d1 : BitVec 64) : BitVec 128 := d1 ++ d0

/-! ## SHA (DDI 0487, J1, "shared/functions/crypto") -/

/-- `SHAchoose(x, y, z) = ((y EOR z) AND x) EOR z`. -/
def shaChoose (x y z : BitVec 32) : BitVec 32 := ((y ^^^ z) &&& x) ^^^ z

/-- `SHAmajority(x, y, z) = ((x AND y) OR ((x OR y) AND z))`. -/
def shaMajority (x y z : BitVec 32) : BitVec 32 := (x &&& y) ||| ((x ||| y) &&& z)

/-- `SHAparity(x, y, z) = (x EOR y EOR z)`. -/
def shaParity (x y z : BitVec 32) : BitVec 32 := x ^^^ y ^^^ z

/-- `SHAhashSIGMA0(x) = ROR(x, 2) EOR ROR(x, 13) EOR ROR(x, 22)`. -/
def shaHashSigma0 (x : BitVec 32) : BitVec 32 :=
  x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22

/-- `SHAhashSIGMA1(x) = ROR(x, 6) EOR ROR(x, 11) EOR ROR(x, 25)`. -/
def shaHashSigma1 (x : BitVec 32) : BitVec 32 :=
  x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25

/-- One iteration of the loops of SHA1C, SHA1P and SHA1M, with the function
`f` (`SHAchoose`, `SHAparity` or `SHAmajority`), on `(Y, X)`:
`t = f(X<63:32>, X<95:64>, X<127:96>); Y = Y + ROL(X<31:0>, 5) + t +
Elem[W, e, 32]; X<63:32> = ROL(X<63:32>, 30); <Y, X> = ROL(Y:X, 32)`.
The 160-bit rotation leaves `X<127:96>` in `Y` and `X<95:0>:Y` in `X`. -/
def sha1Step (f : BitVec 32 → BitVec 32 → BitVec 32 → BitVec 32) (w : BitVec 32)
    (yx : BitVec 32 × BitVec 128) : BitVec 32 × BitVec 128 :=
  let (y, x) := yx
  let t := f (vword x 1) (vword x 2) (vword x 3)
  let y := y + (vword x 0).rotateLeft 5 + t + w
  let x := ofVWords (vword x 0) ((vword x 1).rotateLeft 30) (vword x 2) (vword x 3)
  (vword x 3, ofVWords y (vword x 0) (vword x 1) (vword x 2))

/-- SHA1C, SHA1P, SHA1M: `X = V[d]; Y = V[n]<31:0>; W = V[m]`, then the loop
`for e = 0 to 3` of `sha1Step`, and `V[d] = X`. -/
def sha1Hash (f : BitVec 32 → BitVec 32 → BitVec 32 → BitVec 32) (x : BitVec 128)
    (y : BitVec 32) (w : BitVec 128) : BitVec 128 :=
  (sha1Step f (vword w 3) (sha1Step f (vword w 2) (sha1Step f (vword w 1)
    (sha1Step f (vword w 0) (y, x))))).2

/-- SHA1SU0: `result = operand2<63:0> : operand1<127:64>; result = result
EOR operand1 EOR operand3`, where `operand1 = V[d]`, `operand2 = V[n]`,
`operand3 = V[m]`. -/
def sha1Su0 (op1 op2 op3 : BitVec 128) : BitVec 128 :=
  ofVDwords (vdword op1 1) (vdword op2 0) ^^^ op1 ^^^ op3

/-- SHA1SU1: `T = X EOR LSR(Y, 32); W0 = ROL(T<31:0>, 1); W1 = ROL(T<63:32>,
1); W2 = ROL(T<95:64>, 1); W3 = ROL(T<127:96>, 1) EOR ROL(T<31:0>, 2);
V[d] = W3:W2:W1:W0`, where `X = V[d]`, `Y = V[n]`. -/
def sha1Su1 (x y : BitVec 128) : BitVec 128 :=
  let t := x ^^^ (y >>> 32)
  ofVWords ((vword t 0).rotateLeft 1) ((vword t 1).rotateLeft 1) ((vword t 2).rotateLeft 1)
    ((vword t 3).rotateLeft 1 ^^^ (vword t 0).rotateLeft 2)

/-- One iteration of the loop of `SHA256hash(X, Y, W, part1)`:
`chs = SHAchoose(Y<31:0>, Y<63:32>, Y<95:64>); maj = SHAmajority(X<31:0>,
X<63:32>, X<95:64>); t = Y<127:96> + SHAhashSIGMA1(Y<31:0>) + chs +
Elem[W, e, 32]; X<127:96> = t + X<127:96>; Y<127:96> = t +
SHAhashSIGMA0(X<31:0>) + maj; <Y, X> = ROL(Y : X, 32)`. The 256-bit
rotation leaves `Y<95:0>:X<127:96>` in `Y` and `X<95:0>:Y<127:96>` in `X`. -/
def sha256Step (w : BitVec 32) (xy : BitVec 128 × BitVec 128) : BitVec 128 × BitVec 128 :=
  let (x, y) := xy
  let chs := shaChoose (vword y 0) (vword y 1) (vword y 2)
  let maj := shaMajority (vword x 0) (vword x 1) (vword x 2)
  let t := vword y 3 + shaHashSigma1 (vword y 0) + chs + w
  let x3 := t + vword x 3
  let y3 := t + shaHashSigma0 (vword x 0) + maj
  (ofVWords y3 (vword x 0) (vword x 1) (vword x 2),
    ofVWords x3 (vword y 0) (vword y 1) (vword y 2))

/-- `SHA256hash(X, Y, W, part1)`: the loop `for e = 0 to 3` of `sha256Step`,
then `X` if `part1`, else `Y`. -/
def sha256Hash (x y w : BitVec 128) (part1 : Bool) : BitVec 128 :=
  let r := sha256Step (vword w 3) (sha256Step (vword w 2) (sha256Step (vword w 1)
    (sha256Step (vword w 0) (x, y))))
  if part1 then r.1 else r.2

/-- SHA256SU0: `T = operand2<31:0> : operand1<127:32>`; for `e = 0 to 3`:
`elt = Elem[T, e, 32]; elt = ROR(elt, 7) EOR ROR(elt, 18) EOR LSR(elt, 3);
Elem[result, e, 32] = elt + Elem[operand1, e, 32]`, where `operand1 =
V[d]`, `operand2 = V[n]`. -/
def sha256Su0 (op1 op2 : BitVec 128) : BitVec 128 :=
  let t := ofVWords (vword op1 1) (vword op1 2) (vword op1 3) (vword op2 0)
  let f (e : Nat) : BitVec 32 :=
    let elt := vword t e
    (elt.rotateRight 7 ^^^ elt.rotateRight 18 ^^^ elt >>> 3) + vword op1 e
  ofVWords (f 0) (f 1) (f 2) (f 3)

/-- SHA256SU1: `T0 = operand3<31:0> : operand2<127:32>; T1 = operand3<127:64>`;
for `e = 0 to 1`: `elt = Elem[T1, e, 32]; elt = ROR(elt, 17) EOR ROR(elt, 19)
EOR LSR(elt, 10); elt = elt + Elem[operand1, e, 32] + Elem[T0, e, 32];
Elem[result, e, 32] = elt`; then `T1 = result<63:0>` and for `e = 2 to 3`
the same with `Elem[T1, e-2, 32]`. `operand1 = V[d]`, `operand2 = V[n]`,
`operand3 = V[m]`. -/
def sha256Su1 (op1 op2 op3 : BitVec 128) : BitVec 128 :=
  let t0 := ofVWords (vword op2 1) (vword op2 2) (vword op2 3) (vword op3 0)
  let sig (x : BitVec 32) : BitVec 32 := x.rotateRight 17 ^^^ x.rotateRight 19 ^^^ x >>> 10
  let r0 := sig (vword op3 2) + vword op1 0 + vword t0 0
  let r1 := sig (vword op3 3) + vword op1 1 + vword t0 1
  let r2 := sig r0 + vword op1 2 + vword t0 2
  let r3 := sig r1 + vword op1 3 + vword t0 3
  ofVWords r0 r1 r2 r3

/-- `ROR(x, a) EOR ROR(x, b) EOR ROR(x, c)` on 64 bits. -/
def ror3 (x : BitVec 64) (a b c : Nat) : BitVec 64 :=
  x.rotateRight a ^^^ x.rotateRight b ^^^ x.rotateRight c

/-- SHA512H, with `X = V[n]`, `Y = V[m]`, `W = V[d]`:
`MSigma1 = ROR(Y<127:64>, 14) EOR ROR(Y<127:64>, 18) EOR ROR(Y<127:64>, 41);
Vtmp<127:64> = (Y<127:64> AND X<63:0>) EOR (NOT(Y<127:64>) AND X<127:64>);
Vtmp<127:64> = (Vtmp<127:64> + MSigma1 + W<127:64>); tmp = Vtmp<127:64> +
Y<63:0>; MSigma1 = ROR(tmp, 14) EOR ROR(tmp, 18) EOR ROR(tmp, 41);
Vtmp<63:0> = (tmp AND Y<127:64>) EOR (NOT(tmp) AND X<63:0>); Vtmp<63:0> =
(Vtmp<63:0> + MSigma1 + W<63:0>); V[d] = Vtmp`. -/
def sha512H (w x y : BitVec 128) : BitVec 128 :=
  let y1 := vdword y 1
  let hi := ((y1 &&& vdword x 0) ^^^ (~~~y1 &&& vdword x 1)) + ror3 y1 14 18 41 + vdword w 1
  let tmp := hi + vdword y 0
  let lo := ((tmp &&& y1) ^^^ (~~~tmp &&& vdword x 0)) + ror3 tmp 14 18 41 + vdword w 0
  ofVDwords lo hi

/-- SHA512H2, with `X = V[n]`, `Y = V[m]`, `W = V[d]`:
`NSigma0 = ROR(Y<63:0>, 28) EOR ROR(Y<63:0>, 34) EOR ROR(Y<63:0>, 39);
Vtmp<127:64> = (X<63:0> AND Y<127:64>) EOR (X<63:0> AND Y<63:0>) EOR
(Y<127:64> AND Y<63:0>); Vtmp<127:64> = (Vtmp<127:64> + NSigma0 +
W<127:64>); NSigma0 = ROR(Vtmp<127:64>, 28) EOR ROR(Vtmp<127:64>, 34) EOR
ROR(Vtmp<127:64>, 39); Vtmp<63:0> = (Vtmp<127:64> AND Y<63:0>) EOR
(Vtmp<127:64> AND Y<127:64>) EOR (Y<127:64> AND Y<63:0>); Vtmp<63:0> =
(Vtmp<63:0> + NSigma0 + W<63:0>); V[d] = Vtmp`. -/
def sha512H2 (w x y : BitVec 128) : BitVec 128 :=
  let x0 := vdword x 0
  let y0 := vdword y 0
  let y1 := vdword y 1
  let hi := ((x0 &&& y1) ^^^ (x0 &&& y0) ^^^ (y1 &&& y0)) + ror3 y0 28 34 39 + vdword w 1
  let lo := ((hi &&& y0) ^^^ (hi &&& y1) ^^^ (y1 &&& y0)) + ror3 hi 28 34 39 + vdword w 0
  ofVDwords lo hi

/-- SHA512SU0, with `operand1 = V[d]`, `operand2 = V[n]`:
`sig0 = ROR(operand1<127:64>, 1) EOR ROR(operand1<127:64>, 8) EOR
('0000000':operand1<127:71>); Vtmp<63:0> = operand1<63:0> + sig0;
sig0 = ROR(operand2<63:0>, 1) EOR ROR(operand2<63:0>, 8) EOR
('0000000':operand2<63:7>); Vtmp<127:64> = operand1<127:64> + sig0`. -/
def sha512Su0 (op1 op2 : BitVec 128) : BitVec 128 :=
  let sig (x : BitVec 64) : BitVec 64 := x.rotateRight 1 ^^^ x.rotateRight 8 ^^^ x >>> 7
  ofVDwords (vdword op1 0 + sig (vdword op1 1)) (vdword op1 1 + sig (vdword op2 0))

/-- SHA512SU1, with `operand1 = V[d]`, `operand2 = V[n]`, `operand3 = V[m]`:
`sig1 = ROR(operand2<127:64>, 19) EOR ROR(operand2<127:64>, 61) EOR
('000000':operand2<127:70>); Vtmp<127:64> = operand1<127:64> + sig1 +
operand3<127:64>; sig1 = ROR(operand2<63:0>, 19) EOR ROR(operand2<63:0>, 61)
EOR ('000000':operand2<63:6>); Vtmp<63:0> = operand1<63:0> + sig1 +
operand3<63:0>`. -/
def sha512Su1 (op1 op2 op3 : BitVec 128) : BitVec 128 :=
  let sig (x : BitVec 64) : BitVec 64 := x.rotateRight 19 ^^^ x.rotateRight 61 ^^^ x >>> 6
  ofVDwords (vdword op1 0 + sig (vdword op2 0) + vdword op3 0)
    (vdword op1 1 + sig (vdword op2 1) + vdword op3 1)


end VG.AArch64
