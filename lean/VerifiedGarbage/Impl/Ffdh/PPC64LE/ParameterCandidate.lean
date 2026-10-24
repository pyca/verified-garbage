module

public import VerifiedGarbage.Impl.MillerRabin.PPC64LE.Prep
public import VerifiedGarbage.Impl.Bignum.PPC64LE.PublicChecked

/-!
# One FFDH parameter candidate on PPC64LE

`vg_ffdh_parameter_candidate(out = r3, out_len = r4, used = r5, bits = r6,
generator = r7, rand = r8, rand_len = r9, scratch = r10, scratch_len)`, the
last on the stack (`Spec.Ffdh.parameterCandidateContract`), in RSA's
Montgomery working space at `scratch` (`Spec.Rsa.Mont.Layout`, as the shared
Miller–Rabin round takes it): a header of 32 words, then arrays of `w + 2`
words, `w` set for each modulus. The arguments and the candidate's state are
in header words that neither the working space nor the round changes; the
link register and the nonvolatile registers are saved in the last 160 bytes
of `scratch`, and `r31` keeps `scratch` throughout (as `Env`, the working
space of the Miller–Rabin proofs, has it). The algorithm is
AArch64's (`Impl/Ffdh/AArch64/ParameterCandidate.lean`), in the steps of
`Proof.Ffdh.ParameterCandidate.checkedCandidate`:

1. `out` is zeroed; if `rand` is shorter than `out_len`, the result is 0.
2. With `w = ⌈bits / 64⌉`: p from the first `out_len` octets of `rand`
   (`Precompute.loadN`), its top word cut to `bits` bits (the mask `2^k − 1`,
   `k = bits − 64 (w − 1)`, by a loop of `k` steps) with its top bit set,
   and its low bit set. Its residue modulo 24 (generator 2) or 10 (generator
   5) by a bit-serial remainder (`smallMod`; the model has no division), and
   the congruence. Then the sieve of the 53 odd primes below 256 (the same
   remainder, unrolled over the primes), `q = (p − 1) / 2` in place, its
   oddness and its sieve. The result is 2 if any of them fails.
3. For q and then p, each with its own word count `w = ⌈mb / 64⌉` (`mb` its
   bit length: `bits − 1` or `bits`): the header (`w`, the arrays'
   addresses and size, and `−N⁻¹ mod 2⁶⁴` by Newton's iteration), `R² mod N`
   (`Precompute.r2`), `R mod N` into array 9 and `N − R mod N` into array 10,
   Miller–Rabin's exponent (`expSetup`); then witnesses: each the next
   `⌈mb / 8⌉` octets of `rand`, cut to `mb` bits, rejected unless `x ≥ 2` and
   `(x | 1) < N`, else in Montgomery form in array 5, and the shared round
   called. A witness that fails ends with 2, and `primeChecks mb` passing
   ones with 1; the result is 0 when `rand` runs out. p is loaded again from
   the start of `rand` for its test, and written to `out` when it passes.

`used` is written at the end: the octets read, or 0 for the result 0.
Every value is public: the code branches on the tape's contents.
-/

@[expose] public section

namespace VG.Impl.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE
open VG.Impl.Bignum.PPC64LE.PublicChecked (base montOp)
open VG.Impl.Bignum.PPC64LE.Precompute (zeroWords loadN copyWords)

/-! ## Header words

Those that neither RSA's Montgomery layout (`w` in word 6, `−N⁻¹` in word 7,
the arrays' addresses in words 8–15, their size in word 28) nor the round
(words 1, 23, 26, 29 and 30) uses. -/

def hWsLen : Nat := 0
def hOut : Nat := 2
def hLen : Nat := 3
def hUsedP : Nat := 4
def hBits : Nat := 5
def hGen : Nat := 16
def hRand : Nat := 17
def hRandLen : Nat := 18
def hUsed : Nat := 19
def hStat : Nat := 20
def hChecks : Nat := 21
def hIdx : Nat := 22
def hTop : Nat := 24
def hBad : Nat := 25
def hK : Nat := 27
def hMb : Nat := 31

/-- Header words of the layout. -/
def hW : Nat := 6
def hMinv : Nat := 7
def hStride : Nat := 28

/-- `r := ` header word `i`, and its store. -/
def ldh (r : Reg) (i : Nat) : Instr := .load .d r .r31 (8 * i)
def sth (r : Reg) (i : Nat) : Instr := .store .d r .r31 (8 * i)

/-- The bytes of the save area, at the end of `scratch`. -/
def saveBytes : Nat := 160

/-- The nonvolatile registers saved, `r31` last. -/
def saved (i : Nat) : Reg :=
  [.r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30,
    .r31].getD i .r14

/-! ## Comparisons -/

/-- `d := 1` if `a ≥ b` (unsigned), else 0, through `r0` and `t`: the
borrow of `a − b` is the top bit of `(¬a ∧ b) ∨ (¬(a ⊕ b) ∧ (a − b))`
(`t` other than `r0`). -/
def geFlag (d a b t : Reg) : List Instr :=
  [.li t 0, .subi t t 1, .logic .xor .r0 a t, .logic .and .r0 .r0 b, .logic .xor d a b, .logic .xor d d t,
    .sub t a b, .logic .and d d t, .logic .or d d .r0, .lsr .d d d 63, .li t 1, .logic .xor d d t]

/-! ## Entry and exit -/

/-- `scratch_len` from the stack; the save area at the end of `scratch`,
in `r11`; the link register and the nonvolatile registers saved there; then
`r31 := scratch` and the arguments in the header, `used := out_len`. -/
def entry : List Instr :=
  [.addSp .r11 96, .load .d .r12 .r11 0, .lsl .r11 .r12 3, .add .r11 .r10 .r11, .subi .r11 .r11 saveBytes,
    .mflr .r0, .store .d .r0 .r11 144] ++
  (List.range 18).map (fun i => .store .d (saved i) .r11 (8 * i)) ++
  [.addi .r31 .r10 0, sth .r12 hWsLen, sth .r3 hOut, sth .r4 hLen, sth .r4 hUsed, sth .r5 hUsedP,
    sth .r6 hBits, sth .r7 hGen, sth .r8 hRand, sth .r9 hRandLen]

/-- The registers back from the save area, `r31` last, and the result
`r3`. -/
def exit : List Instr :=
  [ldh .r11 hWsLen, .lsl .r11 .r11 3, .add .r11 .r31 .r11, .subi .r11 .r11 saveBytes, .load .d .r0 .r11 144,
    .mtlr .r0] ++ (List.range 18).map (fun i => .load .d (saved i) .r11 (8 * i))

/-- `out`'s `out_len` octets := 0. -/
def zeroOut : Prog isa :=
  .seq (.block [ldh .r4 hOut, ldh .r5 hLen, .li .r0 0])
    (countLoop .r5 [.stb .r0 .r4 0, .addi .r4 .r4 1])

/-- The result `r` (0, 1 or 2) in `r3`; `used := ` the octets read, or 0 for
0. -/
def finish (r : Nat) : List Instr :=
  [ldh .r4 hUsedP] ++ (if r = 0 then [.li .r5 0] else [ldh .r5 hUsed]) ++ [.store .d .r5 .r4 0, .li .r3 r]

/-! ## A modulus's working space -/

/-- For the modulus of `mb` bits (`bits − 1` for q, `bits` for p): `hMb`,
`hK := ⌈mb / 8⌉`, `w = ⌈mb / 64⌉` in the header, `r11 := 2 w`, the arrays'
size in `r29` and the header, array 0's base in `r10`, the addresses of
arrays 0–7 in the header, and the checks, 128 for `mb ≥ 2049`, else 64. -/
def phaseHead (q : Bool) : List Instr :=
  [ldh .r3 hBits] ++ (if q then [.subi .r3 .r3 1] else []) ++
  [sth .r3 hMb, .addi .r4 .r3 7, .lsr .d .r4 .r4 3, sth .r4 hK, .addi .r4 .r3 63, .lsr .d .r4 .r4 6, sth .r4 hW,
    .lsl .r11 .r4 1, .lsl .r29 .r4 3, .addi .r29 .r29 16, sth .r29 hStride, .addi .r10 .r31 hdrBytes,
    .addi .r5 .r10 0] ++
  (List.range 8).flatMap (fun j => [sth .r5 (8 + j), .add .r5 .r5 .r29]) ++
  [.subi .r5 .r3 2049, .lsr .d .r5 .r5 63, .lsl .r5 .r5 6, .li .r6 128, .sub .r5 .r6 .r5, sth .r5 hChecks]

/-- `hTop := 2^k − 1` for `k = mb − 64 (w − 1)`, in 1..=64: `k` steps of
`x := 2 x + 1`. -/
def topMask : Prog isa :=
  .seq (.block [ldh .r3 hMb, ldh .r4 hW, .lsl .r4 .r4 6, .sub .r3 .r3 .r4, .addi .r3 .r3 64, .li .r5 0])
    (.seq (countLoop .r3 [.add .r5 .r5 .r5, .addi .r5 .r5 1]) (.block [sth .r5 hTop]))

def phase (q : Bool) : Prog isa := .seq (.block (phaseHead q)) topMask

/-! ## The candidate -/

/-- p into array 0: the first `out_len` octets of `rand`, the top word
and'ed with `hTop` and its top bit set, the low bit set. -/
def shapeP : Prog isa :=
  .seq (.block [ldh .r12 hRand, ldh .r6 hLen]) (.seq loadN
    (.block [.lsl .r5 .r11 2, .add .r5 .r10 .r5, .subi .r5 .r5 8, ldh .r4 hTop, .load .d .r6 .r5 0,
      .logic .and .r6 .r6 .r4, .lsr .d .r4 .r4 1, .addi .r4 .r4 1, .logic .or .r6 .r6 .r4, .store .d .r6 .r5 0,
      .load .d .r6 .r10 0, .li .r4 1, .logic .or .r6 .r6 .r4, .store .d .r6 .r10 0]))

/-- `r3 := ` array 0 mod `r4` (for `r4` in 2..2^62), bit-serially from the
top of its `w` words: `r3 := 2 r3 + b`, less `r4` if that is not negative.
It writes `r3`, `r5`–`r9` and `r14`. -/
def smallMod : Prog isa :=
  .seq (.block [.lsl .r5 .r11 2, .add .r5 .r10 .r5, .lsr .d .r6 .r11 1, .li .r3 0])
    (.loop (.seq (.block [.subi .r5 .r5 8, .load .d .r7 .r5 0, .li .r8 64])
        (.seq (countLoop .r8 [.lsr .d .r9 .r7 63, .lsl .r7 .r7 1, .add .r3 .r3 .r3, .add .r3 .r3 .r9,
            .sub .r9 .r3 .r4, .lsr .d .r14 .r9 63, .subi .r14 .r14 1, .logic .xor .r9 .r9 .r3,
            .logic .and .r9 .r9 .r14, .logic .xor .r3 .r3 .r9])
          (.block [.subi .r6 .r6 1])))
      (.nonzero .d .r6))

/-- The generator's congruence: `r = p mod e` (`e` 24 for generator 2, 10
for 5); `hBad := r ⊕ 11` for generator 2, `(r | 4) ⊕ 7` for 5, zero iff
`r = 11` or `r ∈ {3, 7}`. -/
def residue : Prog isa :=
  .seq (.block [ldh .r3 hGen, .subi .r3 .r3 2])
    (.ite (.zero .d .r3)
      (.seq (.block [.li .r4 24]) (.seq smallMod (.block [.li .r4 11, .logic .xor .r3 .r3 .r4, sth .r3 hBad])))
      (.seq (.block [.li .r4 10]) (.seq smallMod (.block [.li .r4 4, .logic .or .r3 .r3 .r4, .li .r4 7,
        .logic .xor .r3 .r3 .r4, sth .r3 hBad]))))

/-- The odd primes below 256. -/
def sievePrimes : List Nat :=
  [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103,
    107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223,
    227, 229, 233, 239, 241, 251]

/-- `r22 |= ` (array 0 mod `d = 0`). -/
def trial (d : Nat) : Prog isa :=
  .seq (.block [.li .r4 d]) (.seq smallMod (.block [.subi .r3 .r3 1, .lsr .d .r3 .r3 63,
    .logic .or .r22 .r22 .r3]))

/-- The sieve: `hBad |= ` the flag of an odd prime below 256 dividing
array 0. -/
def sieve : Prog isa :=
  .seq (.block [ldh .r22 hBad]) (sievePrimes.foldr (fun d c => .seq (trial d) c) (.block [sth .r22 hBad]))

/-- `q := p / 2` in place over the `w` words of array 0, and `hBad |= ` its
evenness. -/
def halveQ : Prog isa :=
  .seq (.block [.addi .r5 .r10 0, .lsr .d .r6 .r11 1, .subi .r6 .r6 1])
    (.seq (countLoop .r6 [.load .d .r3 .r5 0, .load .d .r4 .r5 8, .lsr .d .r3 .r3 1, .lsl .r4 .r4 63,
        .logic .or .r3 .r3 .r4, .store .d .r3 .r5 0, .addi .r5 .r5 8])
      (.block [.load .d .r3 .r5 0, .lsr .d .r3 .r3 1, .store .d .r3 .r5 0, ldh .r5 hBad, .load .d .r3 .r10 0,
        .li .r4 1, .logic .and .r3 .r3 .r4, .logic .xor .r3 .r3 .r4, .logic .or .r5 .r5 .r3, sth .r5 hBad]))

/-! ## Miller–Rabin -/

/-- `−N⁻¹ mod 2⁶⁴` into the header by Newton's iteration `x := x (2 − N x)`
from `x = N` (five steps from three correct bits), and its low half into
`r12` for `montOp`. -/
def minv64 : List Instr :=
  [.load .d .r0 .r10 0, .load .d .r12 .r10 0] ++
    (List.range 5).flatMap (fun _ => [.mul .r3 .r0 .r12, .li .r4 2, .sub .r3 .r4 .r3, .mul .r12 .r12 .r3]) ++
    [.li .r3 0, .sub .r3 .r3 .r12, sth .r3 hMinv, .lsl .r12 .r3 32, .lsr .d .r12 .r12 32]

/-- `r12 :=` the low half of `−N⁻¹`, from the header. -/
def minv32 : List Instr := [ldh .r12 hMinv, .lsl .r12 .r12 32, .lsr .d .r12 .r12 32]

/-- `r10`, `r11` and `r29` from the header, after the round. -/
def regsBack : List Instr :=
  [.addi .r10 .r31 hdrBytes, ldh .r11 hW, .lsl .r11 .r11 1, ldh .r29 hStride] ++ minv32

/-- `−N⁻¹`, `R² mod N` into array 1, `R mod N` into array 6 (the product of
`R² mod N` and 1, in array 7), `N − R mod N` into array 10, `R mod N`
copied into array 9, and the exponent. -/
def montPrep : Prog isa :=
  .seq (.block (minv64 ++ base .r5 1 ++ base .r8 2 ++ base .r9 3)) (.seq Precompute.r2
    (.seq PublicChecked.one (.seq (montOp 6 1 7)
      (.seq (.block (base .r8 0 ++ base .r9 10 ++ base .r10 6)) (.seq subMod
        (.seq (.block ([.addi .r10 .r31 hdrBytes] ++ base .r15 6 ++ base .r14 9)) (.seq copyWords
          Impl.MillerRabin.PPC64LE.expSetup)))))))

/-- An accepted witness: in Montgomery form into array 5, the round called;
then `hStat := 2` if it failed, else the passing witnesses counted and
`hStat := 1` once there are `hChecks` of them. -/
def round (name : String) (roundCode : Prog isa) : Prog isa :=
  .seq (montOp 5 4 1) (.seq (.block [.addi .r3 .r31 0, ldh .r4 hWsLen]) (.seq (.call name roundCode)
    (.seq (.block regsBack)
      (.ite (.zero .d .r3) (.block [.li .r3 2, sth .r3 hStat])
        (.block [ldh .r3 hIdx, ldh .r4 hChecks, .addi .r3 .r3 1, sth .r3 hIdx, .sub .r4 .r4 .r3, .subi .r4 .r4 1,
          .lsr .d .r4 .r4 63, .li .r5 3, .mul .r4 .r4 .r5, .li .r5 4, .sub .r4 .r5 .r4, sth .r4 hStat])))))

/-- A draw: the next `hK` octets of `rand` into array 4 (`hUsed` advanced),
the top word and'ed with `hTop`; the round for `x ≥ 2` and `(x | 1) < N`
(the borrow of `subMod` of a copy of `x | 1`, in array 3 with its word `w`
zeroed, and N, into array 6), else nothing (`hStat` stays 4). -/
def draw (name : String) (roundCode : Prog isa) : Prog isa :=
  .seq (.block ([ldh .r12 hRand, ldh .r3 hUsed, .add .r12 .r12 .r3, ldh .r6 hK, .add .r3 .r3 .r6, sth .r3 hUsed] ++
      base .r10 4))
    (.seq loadN (.seq (.block ([.addi .r10 .r31 hdrBytes] ++ base .r5 4 ++ [.lsl .r6 .r11 2, .add .r5 .r5 .r6,
        .subi .r5 .r5 8, ldh .r4 hTop, .load .d .r6 .r5 0, .logic .and .r6 .r6 .r4, .store .d .r6 .r5 0] ++
        base .r5 4 ++ [.load .d .r24 .r5 0, .lsr .d .r24 .r24 1, .addi .r5 .r5 8, .lsr .d .r6 .r11 1, .subi .r6 .r6 1]))
      (.seq (countLoop .r6 [.load .d .r3 .r5 0, .logic .or .r24 .r24 .r3, .addi .r5 .r5 8])
        (.seq (.block (base .r14 3 ++ base .r15 4))
          (.seq copyWords (.seq (.block (base .r5 3 ++ [.load .d .r3 .r5 0, .li .r4 1, .logic .or .r3 .r3 .r4,
              .store .d .r3 .r5 0, .lsl .r6 .r11 2, .add .r5 .r5 .r6, .li .r0 0, .store .d .r0 .r5 0] ++ base .r8 3 ++
              base .r9 6)) (.seq subMod
            (.ite (.zero .d .r24) (.block [])
              (.ite (.zero .d .r20) (.block []) (round name roundCode))))))))))

/-- Witnesses while `hStat = 4`; 0 when fewer than `hK` octets of `rand`
are left (`rand_len − used`, which does not wrap). -/
def millerRabin (name : String) (roundCode : Prog isa) : Prog isa :=
  .seq (.block [.li .r3 0, sth .r3 hIdx, .li .r3 4, sth .r3 hStat])
    (.loop (.seq (.block ([ldh .r3 hRandLen, ldh .r4 hUsed, .sub .r3 .r3 .r4, ldh .r4 hK] ++ geFlag .r5 .r3 .r4 .r6))
        (.seq (.ite (.zero .d .r5) (.block [.li .r3 0, sth .r3 hStat]) (draw name roundCode))
          (.block [ldh .r3 hStat, .subi .r3 .r3 4])))
      (.zero .d .r3))

/-- The test of q (in array 0) or of p (loaded again). -/
def test (q : Bool) (name : String) (roundCode : Prog isa) : Prog isa :=
  .seq (phase q) (.seq (if q then .block [] else shapeP) (.seq montPrep (millerRabin name roundCode)))

/-! ## `vg_ffdh_parameter_candidate` -/

/-- p (array 0, `w` words) to `out`'s `out_len` octets, most significant
first. -/
def writeP : Prog isa :=
  .seq (.block [ldh .r4 hOut, ldh .r5 hLen, .add .r6 .r10 .r5, .subi .r6 .r6 1])
    (countLoop .r5 [.lbz .r0 .r6 0, .stb .r0 .r4 0, .addi .r4 .r4 1, .subi .r6 .r6 1])

/-- After p's test: 0, 1 (p to `out`) or 2. -/
def pResult : Prog isa :=
  .seq (.block [ldh .r3 hStat])
    (.ite (.zero .d .r3) (.block (finish 0))
      (.seq (.block [.subi .r3 .r3 1]) (.ite (.zero .d .r3) (.seq writeP (.block (finish 1))) (.block (finish 2)))))

/-- After a failed test of q: 0 or 2. -/
def qResult : Prog isa :=
  .seq (.block [ldh .r3 hStat]) (.ite (.zero .d .r3) (.block (finish 0)) (.block (finish 2)))

/-- The tests, once the shape passed. -/
def tests (name : String) (roundCode : Prog isa) : Prog isa :=
  .seq (test true name roundCode) (.seq (.block [ldh .r3 hStat, .subi .r3 .r3 1])
    (.ite (.zero .d .r3) (.seq (test false name roundCode) pResult) qResult))

/-- Once `rand` holds the candidate's octets: p, its congruence, rejected
before any other check (most candidates fail it); then the sieves of p and
q, and the tests. -/
def main (name : String) (roundCode : Prog isa) : Prog isa :=
  .seq (phase false) (.seq shapeP (.seq residue (.seq (.block [ldh .r5 hBad])
    (.ite (.zero .d .r5)
      (.seq sieve (.seq halveQ (.seq sieve (.seq (.block [ldh .r5 hBad])
        (.ite (.zero .d .r5) (tests name roundCode) (.block (finish 2)))))))
      (.block (finish 2))))))

/-- `vg_ffdh_parameter_candidate`. -/
def code (name : String) (roundCode : Prog isa) : Prog isa :=
  .seq (.block entry) (.seq zeroOut (.seq (.block ([ldh .r3 hRandLen, ldh .r4 hLen] ++ geFlag .r5 .r3 .r4 .r6))
    (.seq (.ite (.zero .d .r5) (.block (finish 0)) (main name roundCode)) (.block exit))))

end VG.Impl.Ffdh.PPC64LE.ParameterCandidate
