module

public import VerifiedGarbage.Impl.MillerRabin.RISCV64.Search

/-!
# One FFDH parameter candidate on RISC-V

`vg_ffdh_parameter_candidate(out = a0, out_len = a1, used = a2, bits = a3,
generator = a4, rand = a5, rand_len = a6, scratch = a7, scratch_len)`, the
last on the stack (`Proof.Ffdh.parameterCandidateContract`), as on PPC64LE
(`Impl/Ffdh/PPC64LE/ParameterCandidate.lean`), in RSA's Montgomery working
space at `scratch` (`Proof.Rsa.Mont.Layout`, as the shared Miller–Rabin
round takes it): a header of 32 words, then arrays of `w + 2` words, `w`
set for each modulus. The arguments and the candidate's state are in header
words that neither the working space nor the round changes; the
callee-saved registers and `ra`, which the round's call writes, are saved
in the last 104 bytes of `scratch` (and restored on exit, so that only the
save area says what the calling convention keeps), and `s6`
keeps `scratch` throughout (as `Env`, the working space of the Miller–Rabin
proofs, has it). In the steps of
`Proof.Ffdh.ParameterCandidate.checkedCandidate`:

1. `out` is zeroed; if `rand` is shorter than `out_len`, the result is 0.
2. With `w = ⌈bits / 64⌉`: p from the first `out_len` octets of `rand`
   (`Precompute.loadN`), its top word cut to `bits` bits (the mask `2^k − 1`,
   `k = bits − 64 (w − 1)`, by a loop of `k` steps) with its top bit set,
   and its low bit set. Its residue modulo 24 (generator 2) or 10 (generator
   5) by a bit-serial remainder (`smallMod`), and the congruence. Then the
   sieve of the 53 odd primes below 256, `q = (p − 1) / 2` in place, its
   oddness and its sieve. The result is 2 if any of them fails.
3. For q and then p, each with its own word count `w = ⌈mb / 64⌉` (`mb` its
   bit length: `bits − 1` or `bits`): the header (`w`, the arrays'
   addresses and size), the Montgomery constants and Miller–Rabin's
   exponent (`montPrep`); then witnesses (`millerRabin`): a witness that
   fails ends with 2, and `primeChecks mb` passing ones with 1; the result
   is 0 when `rand` runs out. p is loaded again from the start of `rand` for
   its test, and written to `out` when it passes.

`used` is written at the end: the octets read, or 0 for the result 0.
Every value is public: the code branches on the tape's contents.
-/

@[expose] public section

namespace VG.Impl.Ffdh.RISCV64.ParameterCandidate

open VG VG.RISCV64 VG.Impl.Bignum VG.Impl.Bignum.RISCV64
open VG.Impl.Bignum.RISCV64.Precompute (loadN)
open VG.Impl.MillerRabin.RISCV64.Search

/-! ## Header words

The prime search's words are `Impl.MillerRabin.RISCV64.Search`'s; these are
the candidate's own (the words it leaves to its caller). -/

def hOut : Nat := 2
def hLen : Nat := 3
def hUsedP : Nat := 4
def hBits : Nat := 5
def hGen : Nat := 16

/-- The bytes of the save area, at the end of `scratch`. -/
def saveBytes : Nat := 104

/-- The registers saved: the callee-saved ones, then `ra`. -/
def saved (i : Nat) : Reg := [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11, .ra].getD i .s0

/-! ## Entry and exit -/

/-- `scratch_len` from the stack into `t3`; the save area (`saveBytes`
before the end of `scratch`) at `t4`; the registers saved there; then
`s6 := scratch` and the arguments in the header, `used := out_len`, the
generator zero-extended. -/
def entry : List Instr :=
  [.addSp .t3 0, .load .d .t3 .t3 0, .shift .sll .d .t4 .t3 3, .add .t4 .a7 .t4, .addi .t4 .t4 (-104)] ++
  (List.range 13).map (fun i => .store .d (saved i) .t4 (8 * i)) ++
  [.addi .s6 .a7 0, sth .t3 hWsLen, sth .a0 hOut, sth .a1 hLen, sth .a1 hUsed, sth .a2 hUsedP, sth .a3 hBits,
    .shift .sll .d .a4 .a4 32, .shift .srl .d .a4 .a4 32, sth .a4 hGen, sth .a5 hRand, sth .a6 hRandLen]

/-- The registers back from the save area, through `t3`. -/
def exit : List Instr :=
  [ldh .t3 hWsLen, .shift .sll .d .t3 .t3 3, .add .t3 .s6 .t3, .addi .t3 .t3 (-104)] ++
    (List.range 13).map (fun i => .load .d (saved i) .t3 (8 * i))

/-- `out`'s `out_len` octets := 0. -/
def zeroOut : Prog isa :=
  .seq (.block [ldh .t3 hOut, ldh .t4 hLen, .li .t5 0]) (countLoop .t4 [.store .b .t5 .t3 0, .addi .t3 .t3 1])

/-- The result `r` (0, 1 or 2) in `a0`; `used := ` the octets read, or 0 for
0. -/
def finish (r : Nat) : List Instr :=
  [ldh .t3 hUsedP] ++ (if r = 0 then [.li .t4 0] else [ldh .t4 hUsed]) ++ [.store .d .t4 .t3 0, .li .a0 r]

/-! ## A modulus's working space -/

/-- For the modulus of `mb` bits (`bits − 1` for q, `bits` for p): `hMb`,
`hK := ⌈mb / 8⌉`, `w = ⌈mb / 64⌉` in the header and `t0`, the arrays' size
in `s5` and the header, array 0's base in `a7`, the addresses of arrays 0–7
in the header, and the checks, 128 for `mb ≥ 2049`, else 64 (`mb − 2049`
by two `addi`s, whose immediates reach −2048). -/
def phaseHead (q : Bool) : List Instr :=
  [ldh .t3 hBits] ++ (if q then [.addi .t3 .t3 (-1)] else []) ++
  [sth .t3 hMb, .addi .t4 .t3 7, .shift .srl .d .t4 .t4 3, sth .t4 hK, .addi .t4 .t3 63,
    .shift .srl .d .t4 .t4 6, sth .t4 hW, .addi .t0 .t4 0, .shift .sll .d .s5 .t4 3, .addi .s5 .s5 16,
    sth .s5 hStride, .addi .a7 .s6 hdrBytes, .addi .t5 .a7 0] ++
  (List.range 8).flatMap (fun j => [sth .t5 (8 + j), .add .t5 .t5 .s5]) ++
  [.addi .t5 .t3 (-2048), .addi .t5 .t5 (-1), .shift .srl .d .t5 .t5 63, .shift .sll .d .t5 .t5 6, .li .t6 128,
    .sub .t5 .t6 .t5, sth .t5 hChecks]

/-- `hTop := 2^k − 1` for `k = mb − 64 (w − 1)`, in 1..=64: `k` steps of
`x := 2 x + 1`. -/
def topMask : Prog isa :=
  .seq (.block [ldh .t3 hMb, ldh .t4 hW, .shift .sll .d .t4 .t4 6, .sub .t3 .t3 .t4, .addi .t3 .t3 64, .li .t5 0])
    (.seq (countLoop .t3 [.add .t5 .t5 .t5, .addi .t5 .t5 1]) (.block [sth .t5 hTop]))

def phase (q : Bool) : Prog isa := .seq (.block (phaseHead q)) topMask

/-! ## The candidate -/

/-- p into array 0: the first `out_len` octets of `rand`, the top word
and'ed with `hTop` and its top bit set, the low bit set. -/
def shapeP : Prog isa :=
  .seq (.block [ldh .s7 hRand, ldh .s8 hLen]) (.seq loadN
    (.block [.shift .sll .d .t3 .t0 3, .add .t3 .a7 .t3, .addi .t3 .t3 (-8), ldh .t4 hTop, .load .d .t5 .t3 0,
      .logic .and .t5 .t5 .t4, .shift .srl .d .t4 .t4 1, .addi .t4 .t4 1, .logic .or .t5 .t5 .t4,
      .store .d .t5 .t3 0, .load .d .t5 .a7 0, .logicImm .or .t5 .t5 1, .store .d .t5 .a7 0]))

/-- The generator's congruence: `r = p mod e` (`e` 24 for generator 2, 10
for 5); `hBad := r ⊕ 11` for generator 2, `(r | 4) ⊕ 7` for 5, zero iff
`r = 11` or `r ∈ {3, 7}`. -/
def residue : Prog isa :=
  .seq (.block [ldh .t3 hGen, .addi .t3 .t3 (-2)])
    (.ite (.zero .t3)
      (.seq (.block [.li .s1 24]) (.seq smallMod (.block [.logicImm .xor .s0 .s0 11, sth .s0 hBad])))
      (.seq (.block [.li .s1 10]) (.seq smallMod (.block [.logicImm .or .s0 .s0 4, .logicImm .xor .s0 .s0 7,
        sth .s0 hBad]))))

/-- The sieve: `hBad |= ` the flag of an odd prime below 256 dividing
array 0. -/
def sieve : Prog isa := VG.Impl.MillerRabin.RISCV64.Search.sieve oddPrimes256

/-- `q := p / 2` in place over the `w` words of array 0, and `hBad |= ` its
evenness. -/
def halveQ : Prog isa :=
  .seq (.block [.addi .t3 .a7 0, .addi .t4 .t0 (-1)])
    (.seq (countLoop .t4 [.load .d .t5 .t3 0, .load .d .t6 .t3 8, .shift .srl .d .t5 .t5 1,
        .shift .sll .d .t6 .t6 63, .logic .or .t5 .t5 .t6, .store .d .t5 .t3 0, .addi .t3 .t3 8])
      (.block [.load .d .t5 .t3 0, .shift .srl .d .t5 .t5 1, .store .d .t5 .t3 0, ldh .t4 hBad,
        .load .d .t5 .a7 0, .logicImm .and .t5 .t5 1, .logicImm .xor .t5 .t5 1, .logic .or .t4 .t4 .t5,
        sth .t4 hBad]))

/-- The test of q (in array 0) or of p (loaded again). -/
def test (q : Bool) (name : String) (roundCode : Prog isa) : Prog isa :=
  .seq (phase q) (.seq (if q then .block [] else shapeP) (.seq montPrep (millerRabin name roundCode)))

/-! ## `vg_ffdh_parameter_candidate` -/

/-- p (array 0, `w` words) to `out`'s `out_len` octets, most significant
first. -/
def writeP : Prog isa :=
  .seq (.block [ldh .t3 hOut, ldh .t4 hLen, .add .t5 .a7 .t4, .addi .t5 .t5 (-1)])
    (countLoop .t4 [.load .b .t6 .t5 0, .store .b .t6 .t3 0, .addi .t3 .t3 1, .addi .t5 .t5 (-1)])

/-- After p's test: 0, 1 (p to `out`) or 2. -/
def pResult : Prog isa :=
  .seq (.block [ldh .t3 hStat])
    (.ite (.zero .t3) (.block (finish 0))
      (.seq (.block [.addi .t3 .t3 (-1)]) (.ite (.zero .t3) (.seq writeP (.block (finish 1))) (.block (finish 2)))))

/-- After a failed test of q: 0 or 2. -/
def qResult : Prog isa :=
  .seq (.block [ldh .t3 hStat]) (.ite (.zero .t3) (.block (finish 0)) (.block (finish 2)))

/-- The tests, once the shape passed. -/
def tests (name : String) (roundCode : Prog isa) : Prog isa :=
  .seq (test true name roundCode) (.seq (.block [ldh .t3 hStat, .addi .t3 .t3 (-1)])
    (.ite (.zero .t3) (.seq (test false name roundCode) pResult) qResult))

/-- Once `rand` holds the candidate's octets: p, its congruence, rejected
before any other check (most candidates fail it); then the sieves of p and
q, and the tests. -/
def main (name : String) (roundCode : Prog isa) : Prog isa :=
  .seq (phase false) (.seq shapeP (.seq residue (.seq (.block [ldh .t3 hBad])
    (.ite (.zero .t3)
      (.seq sieve (.seq halveQ (.seq sieve (.seq (.block [ldh .t3 hBad])
        (.ite (.zero .t3) (tests name roundCode) (.block (finish 2)))))))
      (.block (finish 2))))))

/-- `vg_ffdh_parameter_candidate`. -/
def code (name : String) (roundCode : Prog isa) : Prog isa :=
  .seq (.block entry) (.seq zeroOut (.seq (.block ([ldh .t3 hRandLen, ldh .t4 hLen] ++ geFlag .t5 .t3 .t4))
    (.seq (.ite (.zero .t5) (.block (finish 0)) (main name roundCode)) (.block exit))))

end VG.Impl.Ffdh.RISCV64.ParameterCandidate
