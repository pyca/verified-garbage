import VerifiedGarbage.Impl.Weierstrass.Arm
import VerifiedGarbage.Spec.Weierstrass

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
3. `R = [k]G` by the ladder from `R = O = (0 : 1 : 0)`, then
   `x = X Z^(p-2)` (Montgomery's form left by a multiplication by 1) and
   `r = x mod n` (a conditional subtraction, as `x < p < 2n`);
4. `s = k^(n-2) (e + r d) mod n`, in Montgomery form modulo `n`, then left;
5. the flag: `d` and `k` in `[1, n-1]`, `r ≠ 0` and `s ≠ 0`, as a mask, which
   selects `r ‖ s` or zeros for `out` (big-endian), and is returned as 0 or 1.

The multiplications accumulate at `wk`, after the tables; every offset in
the working space is below 4096, which `ldr` and `str` reach from `r12`.
`R = O` (impossible for `k` in `[1, n-1]`) gives `Z = 0`, so `x = 0` and
`r = 0`, as the specification says. Everything is computed whatever the
flag, and only the pointers may affect timing.
-/

namespace VG.Impl.Ecdsa.Arm

open VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass

/-- `-m⁻¹ mod 2⁶⁴`, for odd `m`, by Newton's iteration. -/
def minv (m : Nat) : Nat :=
  let inv := (List.range 6).foldl (fun x _ => x * ((2 + 2 ^ 64 - m * x % 2 ^ 64) % 2 ^ 64) % 2 ^ 64) 1
  (2 ^ 64 - inv) % 2 ^ 64

/-- The working space: the saved registers in bytes `[0, 36)`, then
slots of `n` words (`slot n i`) from byte 64, then the tables of bits
(`bitsAt`), then the multiplications' accumulator (`wkAt`). -/
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

/-- The multiplications' accumulator: after the tables. -/
def wkAt (n : Nat) : Nat := bitsAt n 3

/-- The registers holding the arguments the setup reads: `k`, `d` and the
hash (the functions built on the signature's code read some of them from the
same argument); the working space is the argument on the stack. -/
structure Args where
  k : Reg
  d : Reg
  e : Reg

/-- The signature's: `(out, d, digest, k, scratch)`. -/
abbrev Args.sign : Args := ⟨.r3, .r1, .r2⟩

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

def wk : Nat := wkAt c.n

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

/-- The working space from its argument to `r12`; saves the callee-saved
registers there and moves `out` to `lr`; reads `k`, `d` and the hash from the registers
`A` names; stores the constants; and sets `R = (0 : 1 : 0)` and the flag (a
word) to all ones. -/
def setupWith (A : Args) : List Instr :=
  [.ldrSp wb 0] ++ saveCode ++ [.mov .lr (.reg .r0)] ++
  loadBE c.n (c.sl K) A.k ++ loadBE c.n (c.sl D) A.d ++ loadBE c.n (c.sl E) A.e ++
  c.consts.flatMap (fun (i, x) => setConst c.n (c.sl i) x) ++
  [.mov .r4 (.imm 0), .dp .sub .r4 .r4 (.imm 1), .str .r4 wb (c.sl FLAG)]

/-- The setup of `sign`. -/
def setup : List Instr := c.setupWith .sign

/-- The mask `r5` of `[a] ≠ 0` (all ones if it is not zero), through `r4`:
the words or'ed, then the top bit of `x | -x`, negated. -/
def nonzero (a : Nat) : List Instr :=
  [.ldr .r5 wb a] ++
  ((List.range (2 * c.n - 1)).flatMap fun j => [.ldr .r4 wb (a + 4 * (j + 1)), .dp .orr .r5 .r5 (.reg .r4)]) ++
  [.mov .r4 (.imm 0), .dp .sub .r4 .r4 (.reg .r5), .dp .orr .r4 .r4 (.reg .r5), .mov .r4 (.shifted .r4 .lsr 31),
    .mov .r5 (.imm 0), .dp .sub .r5 .r5 (.reg .r4)]

/-- Digit `j` of `[a] - n`, from the carry `r3` (1 for the first), its carry
to `r3`; `r7` and `r8` hold the words `j / 2` of `[a]` and of `n`. -/
def ltDigit (j : Nat) : List Instr :=
  [half .r4 .r7 (j % 2), half .r5 .r8 (j % 2), .dp .add .r4 .r4 (.reg .r6), .dp .sub .r4 .r4 (.reg .r5),
    .dp .add .r4 .r4 (.reg .r3), .mov .r3 (.shifted .r4 .lsr 16)]

/-- The mask `r5` of `[a] < n` (all ones if it is): the carry out of
`[a] - n` digit by digit is 0 if it borrowed. -/
def ltN (a : Nat) : List Instr :=
  [mask16, .mov .r3 (.imm 1)] ++
  ((List.range (2 * c.n)).flatMap fun k =>
    [.ldr .r7 wb (a + 4 * k), .ldr .r8 wb (c.sl MN + 4 * k)] ++ ltDigit (2 * k) ++ ltDigit (2 * k + 1)) ++
  [.dp .sub .r5 .r3 (.imm 1)]

/-- The flag `&=` the mask `r5`, through `r4`. -/
def andFlag : List Instr :=
  [.ldr .r4 wb (c.sl FLAG), .dp .and .r4 .r4 (.reg .r5), .str .r4 wb (c.sl FLAG)]

/-- `[a]` is in `[1, n-1]`: the flag `&=` both masks (the first kept in `r9`). -/
def checkRange (a : Nat) : List Instr :=
  c.ltN a ++ [.mov .r9 (.reg .r5)] ++ c.nonzero a ++ [.dp .and .r5 .r5 (.reg .r9)] ++ c.andFlag

/-- `[a] ≠ 0`: the flag `&=` its mask. -/
def checkNonzero (a : Nat) : List Instr := c.nonzero a ++ c.andFlag

/-- `x = X Z⁻¹`, `r = x mod n`, `k R mod n`, and the checks of `d`, `k`, `r`. -/
def middle : Prog isa :=
  progs [Mont.Arm.mul c.MP' c.wk (c.sl XM) (c.sl RX) (c.sl ACC),
    Mont.Arm.mul c.MP' c.wk (c.sl X) (c.sl XM) (c.sl ONE),
    .block (Mont.Arm.add c.MN' c.wk (c.sl RR) (c.sl X) (c.sl ZERO)),
    Mont.Arm.mul c.MN' c.wk (c.sl KM) (c.sl K) (c.sl R2N),
    .block (c.checkRange (c.sl D) ++ c.checkRange (c.sl K) ++ c.checkNonzero (c.sl RR))]

/-- The callee-saved registers restored. -/
def restore : List Instr := saved.map fun (r, d) => .ldr r wb d

/-- `r ‖ s` (or zeros) to `out` (in `lr`), the flag's low bit to `r0`, and
the callee-saved registers restored. -/
def finish : List Instr :=
  [.ldr .r10 wb (c.sl FLAG)] ++
  storeBE c.n .lr 0 (c.sl RR) ++ storeBE c.n .lr (8 * c.n) (c.sl SS) ++
  [.dp .and .r0 .r10 (.imm 1)] ++ restore

/-- `s = k⁻¹ (e + r d) mod n`, with `k⁻¹ R` in `ACC`, and its check. -/
def scalar : Prog isa :=
  progs [Mont.Arm.mul c.MN' c.wk (c.sl RM) (c.sl RR) (c.sl R2N),
    Mont.Arm.mul c.MN' c.wk (c.sl DM) (c.sl D) (c.sl R2N),
    Mont.Arm.mul c.MN' c.wk (c.sl EM) (c.sl E) (c.sl R2N),
    Mont.Arm.mul c.MN' c.wk (c.sl TT) (c.sl RM) (c.sl DM),
    .block (Mont.Arm.add c.MN' c.wk (c.sl TT) (c.sl TT) (c.sl EM)),
    Mont.Arm.mul c.MN' c.wk (c.sl SM) (c.sl ACC) (c.sl TT),
    Mont.Arm.mul c.MN' c.wk (c.sl SS) (c.sl SM) (c.sl ONE),
    .block (c.checkNonzero (c.sl SS) ++ c.finish)]

/-- `vg_ecdsa_<curve>_sign`. -/
def sign : Prog isa :=
  .seq (.block c.setup) <|
  .seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n)) <|
  .seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n)) <|
  .seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n)) <|
  .seq (ladder c.ladderCfg c.wk) <|
  .seq (pow c.powP c.wk) <|
  .seq c.middle <|
  .seq (pow c.powN c.wk) c.scalar

end Cfg

end VG.Impl.Ecdsa.Arm
