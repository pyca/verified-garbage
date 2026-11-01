module

public import VerifiedGarbage.Impl.MillerRabin.PPC64LE.Search
public import VerifiedGarbage.Impl.Bignum.PPC64LE.PublicChecked

/-!
# One FFDH parameter candidate on PPC64LE

`vg_ffdh_parameter_candidate(out = r3, out_len = r4, used = r5, bits = r6,
generator = r7, rand = r8, rand_len = r9, scratch = r10, scratch_len)`, the
last on the stack (`Proof.Ffdh.parameterCandidateContract`), in RSA's
Montgomery working space at `scratch` (`Proof.Rsa.Mont.Layout`, as the shared
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
open VG.Impl.MillerRabin.PPC64LE.Search

/-! ## Header words

The prime search's words are `Impl.MillerRabin.PPC64LE.Search`'s; these are
the candidate's own (the words it leaves to its caller). -/

def hOut : Nat := 2
def hLen : Nat := 3
def hUsedP : Nat := 4
def hBits : Nat := 5
def hGen : Nat := 16

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

/-- The generator's congruence: `r = p mod e` (`e` 24 for generator 2, 10
for 5); `hBad := r ⊕ 11` for generator 2, `(r | 4) ⊕ 7` for 5, zero iff
`r = 11` or `r ∈ {3, 7}`. -/
def residue : Prog isa :=
  .seq (.block [ldh .r3 hGen, .subi .r3 .r3 2])
    (.ite (.zero .d .r3)
      (.seq (.block [.li .r4 24]) (.seq smallMod (.block [.li .r4 11, .logic .xor .r3 .r3 .r4, sth .r3 hBad])))
      (.seq (.block [.li .r4 10]) (.seq smallMod (.block [.li .r4 4, .logic .or .r3 .r3 .r4, .li .r4 7,
        .logic .xor .r3 .r3 .r4, sth .r3 hBad]))))

/-- The sieve: `hBad |= ` the flag of an odd prime below 256 dividing
array 0. -/
def sieve : Prog isa := VG.Impl.MillerRabin.PPC64LE.Search.sieve oddPrimes256

/-- `q := p / 2` in place over the `w` words of array 0, and `hBad |= ` its
evenness. -/
def halveQ : Prog isa :=
  .seq (.block [.addi .r5 .r10 0, .lsr .d .r6 .r11 1, .subi .r6 .r6 1])
    (.seq (countLoop .r6 [.load .d .r3 .r5 0, .load .d .r4 .r5 8, .lsr .d .r3 .r3 1, .lsl .r4 .r4 63,
        .logic .or .r3 .r3 .r4, .store .d .r3 .r5 0, .addi .r5 .r5 8])
      (.block [.load .d .r3 .r5 0, .lsr .d .r3 .r3 1, .store .d .r3 .r5 0, ldh .r5 hBad, .load .d .r3 .r10 0,
        .li .r4 1, .logic .and .r3 .r3 .r4, .logic .xor .r3 .r3 .r4, .logic .or .r5 .r5 .r3, sth .r5 hBad]))

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
  .seq (.block entry) (.seq zeroOut (.seq (.block ([ldh .r3 hRandLen, ldh .r4 hLen] ++ geFlag .r5 .r3 .r4))
    (.seq (.ite (.zero .d .r5) (.block (finish 0)) (main name roundCode)) (.block exit))))

end VG.Impl.Ffdh.PPC64LE.ParameterCandidate
