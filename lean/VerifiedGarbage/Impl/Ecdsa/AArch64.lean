import VerifiedGarbage.Impl.Weierstrass.AArch64
import VerifiedGarbage.Spec.Weierstrass

/-!
# ECDSA signing on AArch64

`vg_ecdsa_<curve>_sign(out = x0, d = x1, digest = x2, k = x3,
scratch = x4) -> w0`, for a curve whose field elements and scalars are `n`
64-bit words (`n = 4` for the 256-bit curves), from the code of
`Impl/Weierstrass/AArch64.lean`, as on x86-64 (`Impl/Ecdsa/X86_64.lean`):

1. `x19` and `x20` are saved in the working space, whose base is then
   `x0`, and `out` is kept in `x20`; `k`, `d` and the hash are read
   big-endian into slots, and the constants (the moduli, `a`, `3b`, `G` and
   Montgomery's ones in Montgomery form, `R² mod n`, and the exponents
   `p - 2` and `n - 2`) are stored as immediates;
2. the bits of `k`, `p - 2` and `n - 2` are expanded into tables;
3. `R = [k]G` by the ladder from `R = O = (0 : 1 : 0)`, then
   `x = X Z^(p-2)` (Montgomery's form left by a multiplication by 1) and
   `r = x mod n` (a conditional subtraction, as `x < p < 2n`);
4. `s = k^(n-2) (e + r d) mod n`, in Montgomery form modulo `n`, then left;
5. the flag: `d` and `k` in `[1, n-1]`, `r ≠ 0` and `s ≠ 0`, as a mask, which
   selects `r ‖ s` or zeros for `out` (big-endian), and is returned as 0 or 1.

`R = O` (impossible for `k` in `[1, n-1]`) gives `Z = 0`, so `x = 0` and
`r = 0`, as the specification says. Everything is computed whatever the
flag, and only the pointers may affect timing.
-/

namespace VG.Impl.Ecdsa.AArch64

open VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64

/-- `-m⁻¹ mod 2⁶⁴`, for odd `m`, by Newton's iteration. -/
def minv (m : Nat) : Nat :=
  let inv := (List.range 6).foldl (fun x _ => x * ((2 + 2 ^ 64 - m * x % 2 ^ 64) % 2 ^ 64) % 2 ^ 64) 1
  (2 ^ 64 - inv) % 2 ^ 64

/-- The working space: the saved registers in bytes `[0, 16)`, then
slots of `n` words (`slot n i`) from byte 64, then the tables of bits
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

/-- The table of the bits of `k` (`j = 0`), `p - 2` (1) and `n - 2` (2). -/
def bitsAt (n j : Nat) : Nat := slot n nslots + 64 * n * j

/-- A curve as the code has it: `n` words, and its parameters. -/
structure Cfg where
  n : Nat
  C : Spec.Weierstrass.Curve

namespace Cfg

variable (c : Cfg)

/-- `R = 2^(64 n)`. -/
def R : Nat := 2 ^ (64 * c.n)

/-- `x R mod p`. -/
def mont (x : Nat) : Nat := x * c.R % c.C.p

def sl (i : Nat) : Nat := slot c.n i

def MP' : Mod := { n := c.n, mo := c.sl MP, tmp := c.sl TMP, minv := BitVec.ofNat 64 (minv c.C.p) }
def MN' : Mod := { n := c.n, mo := c.sl MN, tmp := c.sl TMP, minv := BitVec.ofNat 64 (minv c.C.n) }

def pt (x y z : Nat) : Pt := ⟨c.sl x, c.sl y, c.sl z⟩

def rcbSlots : RcbSlots := ⟨c.sl AP, c.sl B3P, c.sl T0, c.sl T1, c.sl T2, c.sl T3, c.sl T4, c.sl T5⟩

def ladderCfg : LadderCfg where
  M := c.MP'
  S := c.rcbSlots
  G := c.pt GX GY ONEP
  R := c.pt RX RY RZ
  D := c.pt DX DY DZ
  T := c.pt TX TY TZ
  bits := bitsAt c.n 0
  nbits := 64 * c.n

def powP : PowCfg := ⟨c.MP', c.sl ACC, c.sl PT, c.sl RZ, c.sl ONEP, bitsAt c.n 1, 64 * c.n⟩
def powN : PowCfg := ⟨c.MN', c.sl ACC, c.sl PT, c.sl KM, c.sl ONEN, bitsAt c.n 2, 64 * c.n⟩

/-- The callee-saved registers the code uses, and where they are saved. -/
def saved : List (Reg × Nat) := [(.x19, 0), (.x20, 8)]

/-- The constants, and `R = (0 : 1 : 0)`: slots and values. -/
def consts : List (Nat × Nat) :=
  [(MP, c.C.p), (MN, c.C.n), (ZERO, 0), (ONE, 1), (ONEP, c.mont 1), (AP, c.mont c.C.a),
    (B3P, c.mont (3 * c.C.b)), (GX, c.mont c.C.gx), (GY, c.mont c.C.gy), (R2N, c.R * c.R % c.C.n),
    (ONEN, c.R % c.C.n), (EXPP, c.C.p - 2), (EXPN, c.C.n - 2), (RX, 0), (RY, c.mont 1), (RZ, 0)]

/-- Saves them, with the working space in `x4`, which then goes to `x0`,
keeps `out` in `x20`; reads `k`, `d` and the hash; stores the constants; and sets
`R = (0 : 1 : 0)` and the flag to all ones. -/
def setup : List Instr :=
  saved.map (fun (r, d) => .str .x r .x4 d) ++
  [.addImm .x .x20 .x0 0, .addImm .x .x0 .x4 0] ++
  loadBE c.n (c.sl K) .x3 ++ loadBE c.n (c.sl D) .x1 ++ loadBE c.n (c.sl E) .x2 ++
  c.consts.flatMap (fun (i, x) => setConst c.n (c.sl i) x) ++
  setConst 1 (c.sl FLAG) (2 ^ 64 - 1)

/-- The mask `x2` of `[a] ≠ 0` (all ones if it is not zero), through `x1`,
`x7` and `x16`. -/
def nonzero (a : Nat) : List Instr :=
  [zero7, ld .x1 a] ++ ((List.range (c.n - 1)).flatMap fun j =>
    [ld .x2 (a + 8 * (j + 1)), .logic .orr .x .x1 .x1 .x2]) ++
  [.subs .x .x16 .x7 .x1, .sbc .x .x2 .x7 .x7]

/-- The mask `x2` of `[a] < n` (all ones if it is), through `x1`, `x7` and
`x16`. -/
def ltN (a : Nat) : List Instr :=
  zero7 :: ((List.range c.n).flatMap fun j =>
    [ld .x1 (a + 8 * j), ld .x2 (c.sl MN + 8 * j),
      if j = 0 then .subs .x .x16 .x1 .x2 else .sbcs .x .x16 .x1 .x2]) ++
  [.sbc .x .x2 .x7 .x7]

/-- The flag `&=` the mask `x2`, through `x1`. -/
def andFlag : List Instr :=
  [ld .x1 (c.sl FLAG), .logic .and .x .x1 .x1 .x2, st .x1 (c.sl FLAG)]

/-- `[a]` is in `[1, n-1]`: the flag `&=` both masks (the first kept in
`x4`). -/
def checkRange (a : Nat) : List Instr :=
  c.ltN a ++ [.addImm .x .x4 .x2 0] ++ c.nonzero a ++ [.logic .and .x .x2 .x2 .x4] ++ c.andFlag

/-- `[a] ≠ 0`: the flag `&=` its mask. -/
def checkNonzero (a : Nat) : List Instr := c.nonzero a ++ c.andFlag

/-- `x = X Z⁻¹`, `r = x mod n`, `k R mod n`, and the checks of `d`, `k`, `r`. -/
def middle : Prog isa :=
  blocks [Mont.AArch64.mul c.MP' (c.sl XM) (c.sl RX) (c.sl ACC),
    Mont.AArch64.mul c.MP' (c.sl X) (c.sl XM) (c.sl ONE),
    Mont.AArch64.add c.MN' (c.sl RR) (c.sl X) (c.sl ZERO),
    Mont.AArch64.mul c.MN' (c.sl KM) (c.sl K) (c.sl R2N),
    c.checkRange (c.sl D) ++ c.checkRange (c.sl K) ++ c.checkNonzero (c.sl RR)]

/-- `r ‖ s` (or zeros) to `out`, the callee-saved registers restored, and
the flag's low bit to `x0`. -/
def finish : List Instr :=
  [ld .x3 (c.sl FLAG)] ++
  storeBE c.n .x20 0 (c.sl RR) ++ storeBE c.n .x20 (8 * c.n) (c.sl SS) ++
  saved.map (fun (r, d) => ld r d) ++
  [.movz .x .x1 1 0, .logic .and .x .x0 .x3 .x1]

/-- `s = k⁻¹ (e + r d) mod n`, with `k⁻¹ R` in `ACC`, and its check. -/
def scalar : Prog isa :=
  blocks [Mont.AArch64.mul c.MN' (c.sl RM) (c.sl RR) (c.sl R2N),
    Mont.AArch64.mul c.MN' (c.sl DM) (c.sl D) (c.sl R2N),
    Mont.AArch64.mul c.MN' (c.sl EM) (c.sl E) (c.sl R2N),
    Mont.AArch64.mul c.MN' (c.sl TT) (c.sl RM) (c.sl DM),
    Mont.AArch64.add c.MN' (c.sl TT) (c.sl TT) (c.sl EM),
    Mont.AArch64.mul c.MN' (c.sl SM) (c.sl ACC) (c.sl TT),
    Mont.AArch64.mul c.MN' (c.sl SS) (c.sl SM) (c.sl ONE),
    c.checkNonzero (c.sl SS) ++ c.finish]

/-- `vg_ecdsa_<curve>_sign`. -/
def sign : Prog isa :=
  .seq (.block c.setup) <|
  .seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n)) <|
  .seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n)) <|
  .seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n)) <|
  .seq (ladder c.ladderCfg) <|
  .seq (pow c.powP) <|
  .seq c.middle <|
  .seq (pow c.powN) c.scalar

end Cfg

end VG.Impl.Ecdsa.AArch64
