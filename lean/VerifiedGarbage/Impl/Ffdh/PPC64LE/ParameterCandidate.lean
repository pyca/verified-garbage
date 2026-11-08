module

public import VerifiedGarbage.Impl.MillerRabin.PPC64LE.Search
public import VerifiedGarbage.Impl.Bignum.PPC64LE.PublicChecked
public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Trial

/-!
# One FFDH parameter candidate on PPC64LE

`vg_ffdh_parameter_candidate_sieved(out = r3, out_len = r4, used = r5,
bits = r6, generator = r7, rand = r8, rand_len = r9, scratch = r10,
scratch_len)`, the last on the stack
(`Proof.Ffdh.sievedParameterCandidateContract`, with RSA's table of trial
division `VG_RSA_KEYGEN_TRIAL32`), in RSA's Montgomery working space at
`scratch` (`Proof.Rsa.Mont.Layout`, as the shared Miller–Rabin round takes
it): a header of 32 words, then arrays of `w + 2` words, `w` set for each
modulus. The arguments and the candidate's state are in header words that
neither the working space nor the round changes; the link register and the
nonvolatile registers are saved in the last 160 bytes of `scratch`, and
`r31` keeps `scratch` throughout (as `Env`, the working space of the
Miller–Rabin proofs, has it). The algorithm is AArch64's
(`Impl/Ffdh/AArch64/ParameterCandidate.lean`), in the steps of
`Spec.Ffdh.sievedParameterCandidate`:

1. `out` is zeroed; if `rand` is shorter than `out_len`, the result is 0.
2. With `w = ⌈bits / 64⌉`: p from the first `out_len` octets of `rand`
   (`Precompute.loadN`), its top word cut to `bits` bits (the mask `2^k − 1`,
   `k = bits − 64 (w − 1)`, by a loop of `k` steps) with its top bit set,
   and its low bit set. The congruence, from p modulo 8 (its low digit) and
   p modulo 3 (generator 2) or 5 (generator 5): the sum of p's digits of 32
   bits, congruent to p modulo `2³² − 1`, which 3 and 5 divide, reduced by
   a multiplication by the divisor's reciprocal (`mulhdu`; the model has no
   division). Then RSA's trial division by the first 512 entries of its
   table (1024 above 1024 bits), whose first 53 are the odd primes below 256
   that `Spec.Ffdh.primeShape` sieves by, stopping at the first divisor:
   first by the table's first 16 entries (`firstEntries`), then, with `q =
   (p − 1) / 2` in place, q's oddness and its trial division, and last, with
   p loaded again, p's whole trial division (so that a q with a small factor
   is rejected before p's whole division). The result is 2 if any of them
   fails.
3. In the order of `Spec.Ffdh.screenedParameterWitnesses`: one witness of
   p, all of q's, then p's other `primeChecks − 1`, each modulus with its own
   word count `w = ⌈mb / 64⌉` (`mb` its bit length: `bits − 1` or `bits`):
   the header (`w`, the arrays' addresses and size, and `−N⁻¹ mod 2⁶⁴` by
   Newton's iteration), `R² mod N` (`Precompute.r2`), `R mod N` into array 9
   and `N − R mod N` into array 10, Miller–Rabin's exponent (`expSetup`);
   then witnesses: each the next `⌈mb / 8⌉` octets of `rand`, cut to `mb`
   bits, rejected unless `x ≥ 2` and `(x | 1) < N`, else in Montgomery form
   in array 5, and the shared round called. A witness that fails ends with 2, and the test's count of passing
   ones with 1; the result is 0 when `rand` runs out. p is loaded again from
   the start of `rand` for each of its tests, q halved again from it, and p
   written to `out` when it passes.

`used` is written at the end: the octets read, or 0 for the result 0.
Every value is public: the code branches on the tape's contents.
-/

@[expose] public section

namespace VG.Impl.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE
open VG.Impl.Bignum.PPC64LE.PublicChecked (base montOp)
open VG.Impl.Bignum.PPC64LE.Precompute (zeroWords loadN copyWords)
open VG.Impl.MillerRabin.PPC64LE.Search

/-! ## Header words

The prime search's words are `Impl.MillerRabin.PPC64LE.Search`'s; these are
the candidate's own (the words it leaves to its caller). -/

def hOut : Nat := 2
def hLen : Nat := 3
def hUsedP : Nat := 4
def hBits : Nat := 5
def hGen : Nat := 16
/-- The count of trial division's entries, while it runs (a word the round
uses, free during the shape's checks). -/
def hTrialN : Nat := 26

/-- The bytes of the save area, at the end of `scratch`. -/
def saveBytes : Nat := 160

/-- The nonvolatile registers saved, `r31` last. -/
def saved (i : Nat) : Reg :=
  [.r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30,
    .r31].getD i .r14

/-! ## Entry and exit -/

/-- `scratch_len` from the stack; the save area at the end of `scratch`,
in `r11`; the link register and the nonvolatile registers saved there; then
`r31 := scratch` and the arguments in the header, `used := out_len`. -/
def entry : List Instr :=
  [.addSp .r11 96, .load .d .r12 .r11 0, .lsl .r11 .r12 3, .add .r11 .r10 .r11, .subi .r11 .r11 saveBytes,
    .mflr .r0, .store .d .r0 .r11 144] ++
  (List.range 18).map (fun i => .store .d (saved i) .r11 (8 * i)) ++
  [.addi .r31 .r10 0, sth .r12 hWsLen, sth .r3 hOut, sth .r4 hLen, sth .r4 hUsed, sth .r5 hUsedP,
    sth .r6 hBits, .lsr .w .r7 .r7 0, sth .r7 hGen, sth .r8 hRand, sth .r9 hRandLen]

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

/-- `r3 :=` the sum of the `2 w` digits of 32 bits of array 0, which is
congruent to it modulo `2³² − 1`. -/
def digitSum : Prog isa :=
  .seq (.block [.addi .r5 .r10 0, .addi .r4 .r11 0, .li .r3 0])
    (countLoop .r4 [.load .w .r0 .r5 0, .add .r3 .r3 .r0, .addi .r5 .r5 4])

/-- `r3 := r3 mod d`, by the quotient `⌊r3 m / 2^(64 + k)⌋` for the
reciprocal `m = ⌈2^(64 + k) / d⌉`, exact for every 64-bit `r3`: `m` is
built in `r6` from its 16-bit pieces `m₃ m₂ m₁ m₀`, most significant first
(`lis`, `ori`, a shift by 32, `oris`, `ori`). -/
def modSmall (d k : Nat) (m₃ m₂ m₁ m₀ : BitVec 16) : List Instr :=
  [.lis .r6 m₃, .ori .r6 .r6 m₂, .lsl .r6 .r6 32, .oris .r6 .r6 m₁, .ori .r6 .r6 m₀, .mulhu .r6 .r3 .r6,
    .lsr .d .r6 .r6 k, .li .r7 d, .mul .r6 .r6 .r7, .sub .r3 .r3 .r6]

/-- `r3 := r3 mod 3`: `m = 0xAAAAAAAAAAAAAAAB = ⌈2⁶⁵ / 3⌉`. -/
def mod3 : List Instr := modSmall 3 1 0xAAAA 0xAAAA 0xAAAA 0xAAAB

/-- `r3 := r3 mod 5`: `m = 0xCCCCCCCCCCCCCCCD = ⌈2⁶⁶ / 5⌉`. -/
def mod5 : List Instr := modSmall 5 2 0xCCCC 0xCCCC 0xCCCC 0xCCCD

/-- Generator 2's congruence, p ≡ 11 (mod 24): `hBad := ((p mod 8) ⊕ 3) |
((p mod 3) ⊕ 2)`, zero iff p ≡ 3 (mod 8) and p ≡ 2 (mod 3). -/
def residue2 : Prog isa :=
  .seq digitSum (.block ([.load .w .r4 .r10 0] ++ mod3 ++
    [.li .r6 7, .logic .and .r4 .r4 .r6, .li .r6 3, .logic .xor .r4 .r4 .r6, .li .r6 2, .logic .xor .r3 .r3 .r6,
      .logic .or .r3 .r3 .r4, sth .r3 hBad]))

/-- Generator 5's congruence, p ≡ 3 or 7 (mod 10): `hBad := ((p mod 2) ⊕ 1) |
((p mod 5) | 1) ⊕ 3`, zero iff p is odd and p ≡ 2 or 3 (mod 5). -/
def residue5 : Prog isa :=
  .seq digitSum (.block ([.load .w .r4 .r10 0] ++ mod5 ++
    [.li .r6 1, .logic .and .r4 .r4 .r6, .logic .xor .r4 .r4 .r6, .logic .or .r3 .r3 .r6, .li .r6 3,
      .logic .xor .r3 .r3 .r6, .logic .or .r3 .r3 .r4, sth .r3 hBad]))

/-- The generator's congruence: `hBad` zero iff p ≡ 11 (mod 24) for
generator 2, 3 or 7 (mod 10) for 5. -/
def residue : Prog isa :=
  .seq (.block [ldh .r3 hGen, .subi .r3 .r3 2]) (.ite (.zero .d .r3) residue2 residue5)

/-- RSA's trial division (`Spec.RsaKeyGen.obviouslyComposite`): `hBad |=`
the flag of one of the first 512 entries of `VG_RSA_KEYGEN_TRIAL32` (1024
above 1024 bits) dividing array 0, the count `1024 − 512 [bits ≤ 1024]` in
`hTrialN`. -/
def trialSieve : Prog isa :=
  .seq (.block [ldh .r3 hBits, .subi .r3 .r3 1025, .lsr .d .r3 .r3 63, .lsl .r3 .r3 9, .li .r4 1024,
      .sub .r3 .r4 .r3, sth .r3 hTrialN])
    (.seq (VG.Impl.RsaKeyGen.PPC64LE.Trial.trial hTrialN)
      (.block [ldh .r5 hBad, .logic .or .r5 .r5 .r22, sth .r5 hBad]))

/-- `q := p / 2` in place over the `w` words of array 0, and `hBad |= ` its
evenness. -/
def halveQ : Prog isa :=
  .seq (.block [.addi .r5 .r10 0, .lsr .d .r6 .r11 1, .subi .r6 .r6 1])
    (.seq (countLoop .r6 [.load .d .r3 .r5 0, .load .d .r4 .r5 8, .lsr .d .r3 .r3 1, .lsl .r4 .r4 63,
        .logic .or .r3 .r3 .r4, .store .d .r3 .r5 0, .addi .r5 .r5 8])
      (.block [.load .d .r3 .r5 0, .lsr .d .r3 .r3 1, .store .d .r3 .r5 0, ldh .r5 hBad, .load .d .r3 .r10 0,
        .li .r4 1, .logic .and .r3 .r3 .r4, .logic .xor .r3 .r3 .r4, .logic .or .r5 .r5 .r3, sth .r5 hBad]))

/-- The test of q (in array 0) or of p (loaded again), its witness count
`hChecks` changed by `adjust` once the working space is set. -/
def test (q : Bool) (adjust : Prog isa) (name : String) (roundCode : Prog isa) : Prog isa :=
  .seq (phase q) (.seq (if q then .block [] else shapeP) (.seq adjust (.seq montPrep (millerRabin name roundCode))))

/-- p's first witness alone: `hChecks := 1`. -/
def firstCheck : Prog isa := .block [.li .r3 1, sth .r3 hChecks]

/-- p's other witnesses: `hChecks := hChecks − 1`. -/
def restChecks : Prog isa := .block [ldh .r3 hChecks, .subi .r3 .r3 1, sth .r3 hChecks]

/-! ## `vg_ffdh_parameter_candidate_sieved` -/

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

/-- After a failed test of p's first witness or of q: 0 or 2. -/
def qResult : Prog isa :=
  .seq (.block [ldh .r3 hStat]) (.ite (.zero .d .r3) (.block (finish 0)) (.block (finish 2)))

/-- After q passed: p's other witnesses. -/
def testRest (name : String) (roundCode : Prog isa) : Prog isa :=
  .seq (test false restChecks name roundCode) pResult

/-- After p's first witness passed: q from p in array 0, and its test. -/
def testQ (name : String) (roundCode : Prog isa) : Prog isa :=
  .seq halveQ (.seq (test true (.block []) name roundCode) (.seq (.block [ldh .r3 hStat, .subi .r3 .r3 1])
    (.ite (.zero .d .r3) (testRest name roundCode) qResult)))

/-- The tests, once the shape passed: one witness of p, then all of q's,
then p's others (`Spec.Ffdh.screenedParameterWitnesses`). -/
def tests (name : String) (roundCode : Prog isa) : Prog isa :=
  .seq (test false firstCheck name roundCode) (.seq (.block [ldh .r3 hStat, .subi .r3 .r3 1])
    (.ite (.zero .d .r3) (testQ name roundCode) qResult))

/-- Trial division by the first `n` entries of the table only (`n` below
`2^15`): `hBad |=` the flag of one of them dividing array 0. -/
def trialSieveN (n : Nat) : Prog isa :=
  .seq (.block [.li .r3 n, sth .r3 hTrialN])
    (.seq (VG.Impl.RsaKeyGen.PPC64LE.Trial.trial hTrialN)
      (.block [ldh .r5 hBad, .logic .or .r5 .r5 .r22, sth .r5 hBad]))

/-- The entries p is divided by before q's trial division: most of p's
small factors, at a fraction of the whole division's cost. -/
def firstEntries : Nat := 16

/-- After q passed: p again in array 0, its whole trial division, and the
tests. -/
def mainP (name : String) (roundCode : Prog isa) : Prog isa :=
  .seq shapeP (.seq trialSieve (.seq (.block [ldh .r5 hBad])
    (.ite (.zero .d .r5) (tests name roundCode) (.block (finish 2)))))

/-- After p's congruence and its first entries passed: q from p, its
oddness and whole trial division, then `mainP`. A q with a small factor
is rejected before p's whole division. -/
def mainQ (name : String) (roundCode : Prog isa) : Prog isa :=
  .seq halveQ (.seq trialSieve (.seq (.block [ldh .r5 hBad])
    (.ite (.zero .d .r5) (mainP name roundCode) (.block (finish 2)))))

/-- Once `rand` holds the candidate's octets: p, its congruence, rejected
before any other check (most candidates fail it); then trial division by
the table's first entries, q's (`mainQ`), p's whole (`mainP`), and the
tests. -/
def main (name : String) (roundCode : Prog isa) : Prog isa :=
  .seq (phase false) (.seq shapeP (.seq residue (.seq (.block [ldh .r5 hBad])
    (.ite (.zero .d .r5)
      (.seq (trialSieveN firstEntries) (.seq (.block [ldh .r5 hBad])
        (.ite (.zero .d .r5) (mainQ name roundCode) (.block (finish 2)))))
      (.block (finish 2))))))

/-- `vg_ffdh_parameter_candidate_sieved`. -/
def code (name : String) (roundCode : Prog isa) : Prog isa :=
  .seq (.block entry) (.seq zeroOut (.seq (.block ([ldh .r3 hRandLen, ldh .r4 hLen] ++ geFlag .r5 .r3 .r4))
    (.seq (.ite (.zero .d .r5) (.block (finish 0)) (main name roundCode)) (.block exit))))

end VG.Impl.Ffdh.PPC64LE.ParameterCandidate
