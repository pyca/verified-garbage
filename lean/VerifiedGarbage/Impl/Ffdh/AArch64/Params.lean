module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Domain

/-!
# Finite-field Diffie–Hellman on AArch64: a parameter candidate

`vg_ffdh_parameter_candidate(out, out_len, used, bits, generator, rand,
rand_len, scratch, scratch_len)`: the first eight arguments in `x0`–`x7`,
`scratch_len` on the stack. Everything it computes is public.

1. If `rand` is shorter than `out_len = k`, zeros to `out`, `used := 0`,
   and 0 returned.
2. The candidate p from the first `k` octets of `rand`, cut to `bits` bits
   with its top and low bits set (`cand`), to `out`; `used := k`.
3. The generator's shape (`p mod 24 = 11`, or `p mod 4 = 3` and
   `p mod 5 ∈ {2, 3}`) and the small primes 3 to 251: none divides p, and
   none divides `q = (p − 1) / 2`, that is, `p mod s ∉ {0, 1}`. The residue
   of `out`'s octets mod `s` is computed octet by octet,
   `r := (256 r + b) mod s`, the quotient by the multiplication with
   `⌈2^32 / s⌉` and a shift (`res`). If a check fails: zeros to `out`, and
   2 returned.
4. Miller–Rabin on q (`out` halved: `half`), then on p (`cand` again): the
   modulus `N` from `out` into the inner workspace and `R² mod N`; `out`
   then holds `d = (N − 1) / 2^s` (the low bit cleared, `half` until it is
   odd, `s` counted) and its first nonzero octet is scanned for; then
   `primeChecks` rounds (`rounds`), each drawing a witness: the next `L`
   octets of `rand` (`L` those of `N − 1`), cut to the bit length of `N`,
   drawn again until `1 < a < N − 1`; `z = a^d mod N` by the domain
   operations' exponentiation (`powA`) and the flag of `z = 1`, or of
   `z^(2^j) = N − 1` for some `j < s` (squarings in Montgomery form,
   `mrCheck`). A failed round ends with 2; `rand` running out ends with 0.
5. If both pass: p to `out` (`cand`), and 1 returned.

`used` is the octets of `rand` read, or 0 for 0. The outer header holds
the arguments and the state of the rounds in slots that the shared pieces
keep.
-/

@[expose] public section

namespace VG.Impl.Ffdh.AArch64.Domain.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sK)
open VG.Impl.Rsa.AArch64.Crt (ldw stw loadArr copyArr leave)
open VG.Impl.Bignum.Crt (sLink)
open VG.Impl.Ffdh.AArch64.Domain

/-! ## Header slots -/

/-- `used`. -/
def cUsedP : Nat := sY
def cBits : Nat := sX
/-- The generator, then the rounds' status: 1 while they pass, 2 when one
fails, 0 when `rand` runs out. -/
def cGen : Nat := sXl
def cRandLen : Nat := sXe
/-- The octets of `rand` read. -/
def cUsed : Nat := sG
/-- The bit length of the modulus being tested. -/
def cBl : Nat := sQ
/-- The octets of a witness, `L`. -/
def cL : Nat := sDom
/-- The rounds left. -/
def cCnt : Nat := sDomLen
/-- `s`, the twos of `N − 1`. -/
def cS : Nat := sMsk
/-- The next witness' octets, then the squarings left. -/
def cPtr : Nat := sF

/-! ## Entry, exit -/

/-- The arguments into the header at `scratch` (`x7`), whose base goes in
`x0`; the generator's upper half ignored. -/
def entry : List Instr :=
  [stw .x0 .x7 sOut, stw .x1 .x7 sK, stw .x2 .x7 cUsedP, stw .x3 .x7 cBits, .addImm .w .x4 .x4 0,
    stw .x4 .x7 cGen, stw .x5 .x7 sRand, stw .x6 .x7 cRandLen, mov .x0 .x7]

/-- `x3` to `used`, and `r` returned. -/
def finish (r : Nat) : List Instr := [ldh .x2 cUsedP, st .x3 .x2, movi .x0 r]

/-- Zeros to `out`, `used := 0`, 0 returned. -/
def fail0 : Prog isa := seqs [Keys.zeroOut sOut sK, .block ([movi .x3 0] ++ finish 0)]

/-- Zeros to `out`, `used` the octets read, 2 returned. -/
def fail2 : Prog isa := seqs [Keys.zeroOut sOut sK, .block ([ldh .x3 cUsed] ++ finish 2)]

/-- `x9 := 1` if `rand_len < out_len`. -/
def short : List Instr := [ldh .x3 cRandLen, ldh .x4 sK, .subs .x .x5 .x3 .x4] ++ borrow1

/-! ## The candidate -/

/-- Octet `x10` of `rand` (at `x1`) to `out` (at `x2`): the first and'ed with
the mask `x6` and or'ed with the top bit `x7`, the last or'ed with 1
(`x11 = k − 1`, `x13 = 255`, `x15 = 0`). -/
def candBody : List Instr :=
  [.ldrb .x4 .x1 0, .subs .x .x5 .x10 .x15, .cselc .x .x5 .x6 .x13 .eq, .cselc .x .x8 .x7 .x15 .eq,
    .logic .and .x .x4 .x4 .x5, .logic .orr .x .x4 .x4 .x8, .subs .x .x5 .x10 .x11, movi .x8 1,
    .cselc .x .x8 .x8 .x15 .eq, .logic .orr .x .x4 .x4 .x8, .strb .x4 .x2 0, .addImm .x .x1 .x1 1,
    .addImm .x .x2 .x2 1, .addImm .x .x10 .x10 1]

/-- In the outer header: p, from the first `k` octets of `rand`, to `out`:
`r = bits − 8 (k − 1)` bits of the first octet kept (the mask `2^r − 1` by
a loop), its top one set, and the low bit of the last. -/
def cand : List (Prog isa) := [
  .block [ldh .x3 cBits, ldh .x4 sK, .lsl .x .x5 .x4 3, .sub .x .x3 .x3 .x5, .addImm .x .x3 .x3 8, movi .x6 0],
  countLoop .x3 [.lsl .x .x6 .x6 1, .addImm .x .x6 .x6 1],
  .block [.lsr .x .x7 .x6 1, .sub .x .x7 .x6 .x7, ldh .x1 sRand, ldh .x2 sOut, ldh .x14 sK, movi .x10 0,
    .subImm .x .x11 .x14 1, movi .x13 255, movi .x15 0],
  countLoop .x14 candBody]

/-! ## Small primes -/

/-- The odd primes below 256. -/
def smallOdd : List Nat :=
  [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107,
    109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229,
    233, 239, 241, 251]

/-- `⌈2^32 / s⌉`. -/
def recip (s : Nat) : Nat := (2 ^ 32 + s - 1) / s

/-- `r := (256 r + b) mod s` for the octet at `x1` (`r` in `x2`, `s` in `x13`,
`⌈2^32 / s⌉` in `x15`). -/
def resBody : List Instr :=
  [.lsl .x .x2 .x2 8, .ldrb .x4 .x1 0, .add .x .x2 .x2 .x4, .mul .x .x5 .x2 .x15, .lsr .x .x5 .x5 32,
    .mul .x .x5 .x5 .x13, .sub .x .x2 .x2 .x5, .addImm .x .x1 .x1 1]

/-- `x2 := ` the number of `out`'s octets mod `s` (`x9` kept). -/
def res (s : Nat) : List (Prog isa) := [
  .block [ldh .x1 sOut, ldh .x14 sK, movi .x2 0, movi .x13 s, movi .x15 (recip s % 2 ^ 16),
    .movk .x .x15 (BitVec.ofNat 16 (recip s / 2 ^ 16)) 1],
  countLoop .x14 resBody]

/-- `x9 &= ` whether `x2 ∉ {0, 1}`: `x2 − 2` does not borrow. -/
def notSmall : List Instr := [movi .x6 2, .subs .x .x5 .x2 .x6, movi .x7 0, movi .x8 1, .csel .x .x5 .x8 .x7,
  .logic .and .x .x9 .x9 .x5]

/-- The check for the prime `s`. -/
def trialStep (s : Nat) : List (Prog isa) := res s ++ [.block notSmall]

/-- `x9 := 1` if `x3 = x4`, else 0 (`x7 = 0`, `x8 = 1`). -/
def eqFlag : List Instr := [.subs .x .x5 .x3 .x4, .cselc .x .x9 .x8 .x7 .eq]

/-- The generator's shape into `x9`, from `p mod 3` and `p mod 5` (in `cL`
and `cCnt`) and the last octet: `p mod 8 = 3` and `p mod 3 = 2` for 2;
`p mod 4 = 3` and `p mod 5 ∈ {2, 3}` for 5. -/
def shapeFlags : List Instr :=
  [ldh .x1 sOut, ldh .x2 sK, .add .x .x1 .x1 .x2, .subImm .x .x1 .x1 1, .ldrb .x10 .x1 0, movi .x7 0, movi .x8 1,
    -- p mod 8 = 3
    movi .x4 7, .logic .and .x .x3 .x10 .x4, movi .x4 3] ++ eqFlag ++ [mov .x11 .x9,
    -- p mod 3 = 2
    ldh .x3 cL, movi .x4 2] ++ eqFlag ++ [.logic .and .x .x11 .x11 .x9,
    -- p mod 4 = 3
    movi .x4 3, .logic .and .x .x3 .x10 .x4] ++ eqFlag ++ [mov .x12 .x9,
    -- p mod 5 ∈ {2, 3}
    ldh .x3 cCnt, movi .x4 2] ++ eqFlag ++ [mov .x13 .x9, movi .x4 3] ++ eqFlag ++
  [.logic .orr .x .x13 .x13 .x9, .logic .and .x .x12 .x12 .x13,
    -- the generator's
    ldh .x3 cGen, movi .x4 2, .subs .x .x5 .x3 .x4, .cselc .x .x9 .x11 .x12 .eq]

/-- In the outer header: `x9 := 1` if p has the generator's shape and no
odd prime below 256 divides p or q. -/
def trial : List (Prog isa) :=
  res 3 ++ [.block [sth .x2 cL]] ++ res 5 ++ [.block (sth .x2 cCnt :: shapeFlags)] ++
    (smallOdd.map trialStep).flatten

/-! ## Halving -/

/-- `out`'s number halved, from its first octet (`x6` the carry in the top
bit). -/
def half : List (Prog isa) := [
  .block [ldh .x1 sOut, ldh .x14 sK, movi .x6 0, movi .x7 1],
  countLoop .x14 [.ldrb .x4 .x1 0, .lsr .x .x5 .x4 1, .logic .orr .x .x5 .x5 .x6, .strb .x5 .x1 0,
    .logic .and .x .x6 .x4 .x7, .lsl .x .x6 .x6 7, .addImm .x .x1 .x1 1]]

/-- `x1 := ` the last octet's pointer, `x5 := ` the octet. -/
def lastOctet : List Instr := [ldh .x1 sOut, ldh .x2 sK, .add .x .x1 .x1 .x2, .subImm .x .x1 .x1 1, .ldrb .x5 .x1 0]

/-- `out := (N − 1) / 2^s`, `s` in `cS`: the low bit cleared, then halved
while even. -/
def twos : List (Prog isa) := [
  .block (lastOctet ++ [movi .x6 254, .logic .and .x .x5 .x5 .x6, .strb .x5 .x1 0, movi .x3 0, sth .x3 cS]),
  .loop (seqs (half ++ [.block ([ldh .x3 cS, .addImm .x .x3 .x3 1, sth .x3 cS] ++ lastOctet ++
      [movi .x6 1, .logic .and .x .x5 .x5 .x6, .logic .eor .x .x5 .x5 .x6])])) (.nonzero .x .x5)]

/-! ## Miller–Rabin -/

variable (window select : Prog isa) (mul : Nat → Nat → Nat → Prog isa)

/-- In the inner workspace: `[aY] := b^e mod N` for `b` in `aXm` and the
exponent `e` at the pointer and length in the outer slots `ep` and `el`:
`pow` without the base's load. -/
def powA (ep el : Nat) : List (Prog isa) :=
  [mul aY aR2 aOne, mul aXm aXm aR2] ++ copyArr aX aR2 ++ copyArr Crt.aXc aXm ++
  [WindowFive.expLoop window mul select ep el, mul aY aY aOne] ++ copyArr aR2 aX

/-- In the inner workspace: `[aXm]` cut to the bit length `b` in the outer
slot `cBl`: word `j` and'ed with all ones below `⌊b / 64⌋`, with
`2^(b mod 64) − 1` at it (by a loop of `b mod 64 + 1` steps and a shift), and with 0 above (`x10` the word's index, `x11`
`⌊b / 64⌋`, `x12` the mask at it). -/
def cutA : List (Prog isa) := [
  .block [ldh .x5 sLink, ldw .x3 .x5 cBl, .lsr .x .x11 .x3 6, movi .x4 63, .logic .and .x .x3 .x3 .x4,
    .addImm .x .x3 .x3 1, movi .x12 0, movi .x13 1],
  countLoop .x3 [.lsl .x .x12 .x12 1, .logic .orr .x .x12 .x12 .x13],
  .block [.lsr .x .x12 .x12 1, ldh .x16 (sArr aXm), ldh .x14 sW, movi .x10 0, movi .x7 0, .subImm .x .x8 .x7 1],
  countLoop .x14 [ld .x4 .x16, .subs .x .x5 .x10 .x11, .csel .x .x6 .x7 .x8, .logic .eor .x .x5 .x10 .x11,
    movi .x9 1, .subs .x .x5 .x5 .x9, .csel .x .x6 .x6 .x12, .logic .and .x .x4 .x4 .x6, st .x4 .x16,
    next .x16, .addImm .x .x10 .x10 1]]

/-- One draw, from the outer workspace: the next `L` octets of `rand` into
`aXm`, cut, `used += L`; back in the outer workspace, `x3 := 1` to draw
again (`a` out of range), 0 otherwise. -/
def drawOne : List (Prog isa) :=
  [.block [ldh .x1 sRand, ldh .x4 cUsed, .add .x .x1 .x1 .x4, sth .x1 cPtr, ldh .x6 cL, .add .x .x4 .x4 .x6,
    sth .x4 cUsed, enter]] ++ loadArr aXm cPtr cL ++ cutA ++ range aXm ++
  [.block [leave, movi .x3 1, .sub .x .x3 .x3 .x9]]

/-- A draw, or the end of `rand` (status 0, `x3 := 0`). -/
def draw : Prog isa :=
  .seq (.block [ldh .x3 cRandLen, ldh .x4 cUsed, .sub .x .x5 .x3 .x4, ldh .x6 cL, .subs .x .x7 .x5 .x6,
      movi .x7 0, movi .x8 1, .csel .x .x9 .x7 .x8])
    (.ite (.zero .x .x9) (seqs drawOne) (.block [movi .x3 0, sth .x3 cGen]))

/-- In the inner workspace, `z` in `aY`: `x9 := 1` if `z = 1` or
`z^(2^j) = N − 1` for some `j < s`: the flag in the inner `sF`, and `s`
squarings (`z := (z R) z R⁻¹`) each after the check of `z = N − 1`
(`¬ (z | 1 < N)`), counted in the outer `cPtr`. -/
def mrCheck : List (Prog isa) :=
  isOne aY ++ [.block [sth .x9 sF, ldh .x5 sLink, ldw .x3 .x5 cS, stw .x3 .x5 cPtr],
    .loop (seqs (ltP aY ++ [.block [ldh .x3 sF, movi .x4 1, .sub .x .x5 .x4 .x9, .logic .orr .x .x3 .x3 .x5,
        sth .x3 sF], mul aXm aY aR2, mul aY aXm aY,
      .block [ldh .x5 sLink, ldw .x3 .x5 cPtr, .subImm .x .x3 .x3 1, stw .x3 .x5 cPtr]]))
      (.nonzero .x .x3),
    .block [ldh .x9 sF]]

/-- One round, from the outer workspace: draws until a witness is in range
or `rand` runs out; if one is: `z = a^d mod N`, and the round's check
(status 2 if it fails); then `x3 := ` the rounds left if the status is
still 1, else 0. -/
def round : List (Prog isa) := [
  .loop draw (.nonzero .x .x3),
  .seq (.block [ldh .x9 cGen])
    (.ite (.zero .x .x9) (.block [])
      (seqs ([.block [enter]] ++ powA window select mul sEp sEl ++ mrCheck mul ++
        [.block [leave, movi .x4 2, movi .x5 1, .subs .x .x6 .x9 .x5, .csel .x .x9 .x5 .x4, sth .x9 cGen]]))),
  .block [ldh .x3 cCnt, .subImm .x .x3 .x3 1, sth .x3 cCnt, ldh .x9 cGen, movi .x4 1, .subs .x .x5 .x9 .x4,
    movi .x7 0, .cselc .x .x3 .x3 .x7 .eq]]

/-- Miller–Rabin on `N` (`out`'s octets, `cBl` its bit length), from the
outer workspace: status in `x9`. -/
def mr : List (Prog isa) :=
  [.block [ldh .x3 cBl, .addImm .x .x4 .x3 7, .lsr .x .x4 .x4 3, sth .x4 cL, movi .x5 64, movi .x6 128,
    movi .x7 2048, .subs .x .x8 .x7 .x3, .csel .x .x5 .x5 .x6, sth .x5 cCnt, movi .x9 1, sth .x9 cGen],
   .block (wsSetup sK ++ [enter])] ++ modSetup sOut sK ++ r2Steps mul ++ [.block [leave]] ++ twos ++
  scan sOut ++ [.loop (seqs (round window select mul)) (.nonzero .x .x3), .block [ldh .x9 cGen]]

/-- From the outer workspace, after the checks: Miller–Rabin on q, then on
p; p to `out` for 1. -/
def tests : List (Prog isa) :=
  half ++ [.block [ldh .x3 cBits, .subImm .x .x3 .x3 1, sth .x3 cBl]] ++ mr window select mul ++
  [.ite (.zero .x .x9) fail0 (.seq (.block [.subImm .x .x3 .x9 1]) (.ite (.zero .x .x3)
    (seqs (cand ++ [.block [ldh .x3 cBits, sth .x3 cBl]] ++ mr window select mul ++
      [.ite (.zero .x .x9) fail0 (.seq (.block [.subImm .x .x3 .x9 1]) (.ite (.zero .x .x3)
        (seqs (cand ++ [.block ([ldh .x3 cUsed] ++ finish 1)])) fail2))]))
    fail2))]

def main : Prog isa :=
  seqs (cand ++ [.block [ldh .x3 sK, sth .x3 cUsed], .block head, .block [movi .x9 1]] ++ trial ++
    [.ite (.zero .x .x9) fail2 (seqs (tests window select mul))])

/-- `vg_ffdh_parameter_candidate`. -/
def code : Prog isa :=
  .seq (.block (entry ++ short)) (.ite (.zero .x .x9) (main window select mul) fail0)

end VG.Impl.Ffdh.AArch64.Domain.ParameterCandidate
