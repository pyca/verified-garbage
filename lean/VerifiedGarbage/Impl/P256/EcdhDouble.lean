module

public import VerifiedGarbage.Impl.P256.VerifySparse
public import VerifiedGarbage.Impl.P256.EcdhAllocatedCode

/-! Jacobian doubling for `a = -3` with four products and four squares.

With `h = 2Y`, `g = h²`, `S = X g`, `M = 3 (X - Z²) (X + Z²)`:
`X' = M² - 2S`, `Z' = h Z` and `Y' = M (S - X') - g²/2`, as `g² = 16 Y⁴`. Every
operation but `3x` and `x/2` is one of `VerifySparse.op`. The scheduler is
untrusted; its output is certified against `raw`. -/

@[expose] public section

namespace VG.Impl.P256.EcdhDouble
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64

/-- `x8`–`x11` plus the prime under the mask `x17` (`x7 = 0`); the carry is left in the flag. -/
def addPrime : List Instr :=
  [.lsr .x .x1 .x17 32, .lsl .x .x2 .x17 32, .sub .x .x2 .x2 .x17,
   .adds .x .x8 .x8 .x17, .adcs .x .x9 .x9 .x1, .adcs .x .x10 .x10 .x7, .adcs .x .x11 .x11 .x2]

/-- `T = 3 x` in `x8`–`x11` and `x16`, which is at most 2. -/
def tripleSum : List Instr :=
  [.lsl .x .x12 .x8 1, .extr .x .x13 .x9 .x8 63, .extr .x .x14 .x10 .x9 63,
   .extr .x .x15 .x11 .x10 63, .lsr .x .x16 .x11 63,
   .adds .x .x8 .x8 .x12, .adcs .x .x9 .x9 .x13, .adcs .x .x10 .x10 .x14,
   .adcs .x .x11 .x11 .x15, .adc .x .x16 .x16 .x7]

/-- `T - q p` for `q = x16 + 1`, in `[-p, p)`, its sign as the mask `x17`: the top words of `T` and
`q p` are equal, and the low words of `q p` are `-q`, `2^32 q - 1`, `0` and `q - 2^32 q`. -/
def tripleReduce : List Instr :=
  [.movz .x .x2 1 0, .add .x .x16 .x16 .x2, .sub .x .x12 .x7 .x16, .lsl .x .x13 .x16 32,
   .sub .x .x15 .x16 .x13, .sub .x .x13 .x13 .x2,
   .subs .x .x8 .x8 .x12, .sbcs .x .x9 .x9 .x13, .sbcs .x .x10 .x10 .x7, .sbcs .x .x11 .x11 .x15,
   .sbc .x .x17 .x7 .x7]

/-- `[o] = 3 [a] mod p`, for `[a] < p`. -/
def triple (o a : Nat) : List Instr :=
  zero7 :: loads (low 4) a ++ (tripleSum ++ tripleReduce ++ addPrime) ++ stores (low 4) o

/-- The mask of an odd `x`, and `x`, plus the prime if it is odd, shifted right by one. -/
def halfMask : List Instr :=
  [.lsl .x .x17 .x8 63, .lsr .x .x17 .x17 63, .sub .x .x17 .x7 .x17]
def halfShift : List Instr :=
  [.adc .x .x12 .x7 .x7, .extr .x .x8 .x9 .x8 1, .extr .x .x9 .x10 .x9 1,
   .extr .x .x10 .x11 .x10 1, .extr .x .x11 .x12 .x11 1]

/-- `[o] = [a] / 2 mod p`, for `[a] < p`. -/
def half (o a : Nat) : List Instr :=
  zero7 :: loads (low 4) a ++ (halfMask ++ addPrime ++ halfShift) ++ stores (low 4) o

/-- `M / 3` in `864`. -/
def ops1 : List FOp :=
  [.mul 800 576 576, .add 832 544 544, .sub 864 512 800, .add 896 512 800, .mul 864 864 896]
/-- `X'`, `Z'`, `M (S - X')` in `544` and `g²` in `896`. -/
def ops2 : List FOp :=
  [.mul 896 832 832, .mul 928 512 896, .mul 576 832 576, .mul 512 864 864,
   .sub 512 512 928, .sub 512 512 928, .sub 928 928 512, .mul 544 864 928, .mul 896 896 896]
def ops3 : List FOp := [.sub 544 544 896]

def raw : List Instr :=
  ops1.flatMap VerifySparse.op ++ triple 864 864 ++ ops2.flatMap VerifySparse.op ++
    half 896 896 ++ ops3.flatMap VerifySparse.op

def code : List Instr := EcdhAllocatedCode.double

def program : Prog isa := .block code

end VG.Impl.P256.EcdhDouble
