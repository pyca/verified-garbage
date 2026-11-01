module

public import VerifiedGarbage.Impl.RsaKeyGen.AArch64.Candidate

/-!
# One FFDH parameter candidate on AArch64

`vg_ffdh_parameter_candidate(out = x0, out_len = x1, used = x2, bits = x3,
generator = x4, rand = x5, rand_len = x6, scratch = x7, scratch_len = [sp])`
(`Proof.Ffdh.parameterCandidateContract`), in the working space of RSA's key
routines (`Impl/Rsa/AArch64/Keys.lean`, as the RSA candidate's,
`Impl/RsaKeyGen/AArch64/Candidate.lean`): a header of 32 words, then arrays
of `w + 2` words, `w` set for each modulus by `Keys.head` from the length
in `sK`. The arguments stay in header slots that neither the working space
nor the shared Miller–Rabin round changes.

1. `out` is zeroed; if `rand` is shorter than `out_len`, the result is 0.
2. With `w = ⌈bits / 64⌉`: `p` from the first `out_len` octets of `rand`,
   cut to `bits` bits with its top and low bits set (`shapeP`: the top
   word's mask `2^k − 1`, `k = bits − 64 (w − 1)`, is computed by a loop of
   `k` steps); `p mod 24` (generator 2) or `p mod 10` (generator 5) by RSA's
   bit-serial reduction, and its congruence; the sieve of the 53 odd primes
   below 256 (RSA's trial division by the first 53 entries of its table);
   then `q = (p − 1) / 2` in place, its oddness and its sieve. Their flags
   are or'ed in `fBad`; the result is 2 if it is set.
3. For `q` and then `p`, each with its own word count `w = ⌈mb / 64⌉`
   (`mb` its bit length: `bits − 1` or `bits`): RSA's Montgomery setup
   (`-N⁻¹`, `R² mod N`, `R mod N`, `N − R mod N`), Miller–Rabin's exponent,
   then witnesses: each the next `⌈mb / 8⌉` octets of `rand`, its top word
   cut to `mb` bits, rejected unless `2 ≤ x ≤ N − 2` (`x ≥ 2` and
   `(x | 1) < N`), then in Montgomery form, and the shared round called;
   a witness that fails ends with 2, and `primeChecks mb` passing ones with 1.
   The result is 0 when `rand` runs out. `p` is loaded again from the start
   of `rand` for its test, and written to `out` when it passes.

`used` is written at the end: the octets read, or 0 for the result 0.
Every value is public: the code branches on the tape's contents.
-/

@[expose] public section

namespace VG.Impl.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.AArch64.Candidate

/-! ## Header slots

Besides the RSA candidate's `kOut`, `kUsedP`, `kLen` (`sK`, the current
modulus's length in octets), `kRand`, `kRandLen`, `kUsed` and `kStat`: the
uniform witnesses needed (`fChecks`), the top word's mask (`fTop`), the
passing witnesses so far (`fIdx`), the flag of a rejected shape (`fBad`),
`bits`, the generator and `out_len`. -/

def fChecks : Nat := 0
def fTop : Nat := 2
def fIdx : Nat := 3
def fBad : Nat := 4
def fBits : Nat := sFn 3
def fGen : Nat := sFn 4
def fLen : Nat := sFn 5

/-! ## Entry -/

/-- The arguments in the header at `scratch` (`x7`), whose base goes in
`x0`; `used := out_len`. -/
def entry : List Instr :=
  [.str .x .x0 .x7 (8 * kOut), .str .x .x1 .x7 (8 * kLen), .str .x .x1 .x7 (8 * fLen),
    .str .x .x1 .x7 (8 * kUsed), .str .x .x2 .x7 (8 * kUsedP), .str .x .x3 .x7 (8 * fBits), .addImm .w .x4 .x4 0,
    .str .x .x4 .x7 (8 * fGen), .str .x .x5 .x7 (8 * kRand), .str .x .x6 .x7 (8 * kRandLen), mov .x0 .x7]

/-! ## A modulus's working space -/

/-- For the modulus of `mb` bits (`bits − 1` for `q`, `bits` for `p`):
`sK := ⌈mb / 8⌉`, `x6 := mb + 64 − 64 ⌈mb / 64⌉` (`k`, in 1..=64) and the
checks, 128 for `mb ≥ 2049`, else 64. -/
def phaseHead (q : Bool) : List Instr :=
  [ldh .x3 fBits] ++ (if q then [.subImm .x .x3 .x3 1] else []) ++
  [.addImm .x .x4 .x3 7, .lsr .x .x4 .x4 3, sth .x4 sK, .addImm .x .x6 .x3 63, .lsr .x .x6 .x6 6,
    .lsl .x .x6 .x6 6, .addImm .x .x8 .x3 64, .sub .x .x6 .x8 .x6, movi .x5 64, movi .x9 128, movi .x8 2049,
    .subs .x .x8 .x3 .x8, .csel .x .x5 .x9 .x5, sth .x5 fChecks]

/-- The working space for the modulus, and `fTop := 2^k − 1`. -/
def phase (q : Bool) : List (Prog isa) :=
  [.block (phaseHead q ++ Keys.head ++ [movi .x9 0]), countLoop .x6 [.add .x .x9 .x9 .x9, .addImm .x .x9 .x9 1],
    .block [sth .x9 fTop]]

/-! ## The candidate -/

/-- `p` into `aN`: the first `out_len` octets of `rand`, the top word and'ed
with `fTop` and its top bit set, the low bit set. -/
def shapeP : List (Prog isa) :=
  loadA aN kRand kLen ++
  [.block (ws ++ base aN .x16 ++ [.lsl .x .x5 .x12 3, .add .x .x5 .x16 .x5, .subImm .x .x5 .x5 8, ldh .x4 fTop,
    ld .x3 .x16, ld .x6 .x5, movi .x9 1, .logic .orr .x .x3 .x3 .x9, .logic .and .x .x6 .x6 .x4, .lsr .x .x9 .x4 1,
    .addImm .x .x9 .x9 1, .logic .orr .x .x6 .x6 .x9, st .x3 .x16, st .x6 .x5])]

/-- The generator's congruence: `r = p mod e` (`e` 24 for generator 2, 10
for 5) by RSA's bit-serial reduction of `aN`'s words from the top; `fBad :=
r ⊕ 11` for generator 2, `(r | 4) ⊕ 7` for 5, zero iff `r = 11` or
`r ∈ {3, 7}`. -/
def residue : List (Prog isa) := [
  .block (ws ++ base aN .x16 ++ [.lsl .x .x5 .x12 3, .add .x .x10 .x16 .x5, mov .x14 .x12, ldh .x9 fGen,
    movi .x6 3, .subs .x .x8 .x9 .x6, movi .x13 10, movi .x6 24, .csel .x .x13 .x13 .x6, movi .x3 0, movi .x7 0,
    .subImm .x .x8 .x7 1]),
  .loop (seqs [.block [.subImm .x .x10 .x10 8, ld .x2 .x10, movi .x9 64], countLoop .x9 modBit,
    .block [.subImm .x .x14 .x14 1]]) (.nonzero .x .x14),
  .block [ldh .x9 fGen, movi .x6 3, .subs .x .x8 .x9 .x6, movi .x4 4, .logic .orr .x .x5 .x3 .x4,
    .csel .x .x5 .x5 .x3, movi .x6 7, movi .x7 11, .csel .x .x6 .x6 .x7, .logic .eor .x .x5 .x5 .x6, sth .x5 fBad]]

/-- RSA's table of small primes at `aTab`. -/
def tableWrite : Prog isa := .block (ws ++ base aTab .x9 ++ tabWrite)

/-- The sieve: the mask of an entry of the table's first 53 (13 words, then
an entry) dividing `aN`, or'ed into `fBad`. -/
def sieve : List (Prog isa) := [
  .block (ws ++ base aTab .x9 ++ [movi .x10 13, movi .x1 0, movi .x7 0, .subImm .x .x8 .x7 1]),
  .loop (seqs (([.block [ld .x17 .x9, next .x9]] : List (Prog isa)) ++ trialEntry 0 ++ trialEntry 1 ++
    trialEntry 2 ++ trialEntry 3 ++ ([.block [.subImm .x .x10 .x10 1]] : List (Prog isa)))) (.nonzero .x .x10),
  .block [ld .x17 .x9]] ++ trialEntry 0 ++
  [.block [ldh .x5 fBad, .logic .orr .x .x5 .x5 .x1, sth .x5 fBad]]

/-- `q := p / 2` in place, and its evenness or'ed into `fBad`. -/
def halveQ : List (Prog isa) :=
  .block (ws ++ base aN .x16 ++ [mov .x17 .x16, movi .x7 0, .subImm .x .x15 .x7 1]) :: halfPass ++
  [.block (ws ++ base aN .x16 ++ [ldh .x5 fBad, ld .x3 .x16, movi .x4 1, .logic .and .x .x3 .x3 .x4,
    .logic .eor .x .x3 .x3 .x4, .logic .orr .x .x5 .x5 .x3, sth .x5 fBad])]

/-! ## Miller–Rabin -/

/-- `-N⁻¹`, the number 1, `R² mod N`, `R mod N` into `aR1` and `N − R mod N`
into `aRm1`: RSA's `montSetup` without its count of checks. -/
def montPrep (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) :=
  ([.block ([ldh .x8 (sArr aN), ld .x3 .x8] ++ minv ++ [sth .x15 sMinv, ldh .x12 sW, movi .x9 1, movi .x13 0]),
    setWord aOne] : List (Prog isa)) ++
  r2Steps mul ++ [mul aY aR2 aOne, copyA aR1 aY] ++ subA aRm1 aN aR1

/-- An accepted witness: its Montgomery form into `aXm`, the round; then
`kStat := 2` if it failed, else the passing witnesses counted and `kStat :=
1` once there are `fChecks` of them, 4 before. -/
def round (mul : Nat → Nat → Nat → Prog isa) (roundCode : List (Prog isa)) : List (Prog isa) :=
  [mul aXm aX aR2] ++ roundCode ++ [
  .block [ldh .x3 kFlag],
  .ite (.zero .x .x3) (.block [movi .x3 2, sth .x3 kStat])
    (.block [ldh .x3 fIdx, ldh .x4 fChecks, .addImm .x .x3 .x3 1, .subs .x .x5 .x3 .x4, movi .x6 4, movi .x7 1,
      .csel .x .x5 .x7 .x6, sth .x3 fIdx, sth .x5 kStat])]

/-- A draw: the next `sK` octets of `rand` into `aX` (`used` advanced), the
top word and'ed with `fTop`; the mask of `x ≥ 2` and `(x | 1) < N` into
`x9`; `kStat := 4` for a rejected draw, else the round. -/
def draw (mul : Nat → Nat → Nat → Prog isa) (roundCode : List (Prog isa)) : List (Prog isa) := [
  zeroA aX,
  .block (ws ++ base aX .x8 ++ [ldh .x1 kRand, ldh .x3 kUsed, .add .x .x1 .x1 .x3, ldh .x2 kLen,
    .add .x .x3 .x3 .x2, sth .x3 kUsed]),
  loadBE,
  .block (ws ++ base aX .x16 ++ [.lsl .x .x5 .x12 3, .add .x .x5 .x16 .x5, .subImm .x .x5 .x5 8, ldh .x4 fTop,
    ld .x3 .x5, .logic .and .x .x3 .x3 .x4, st .x3 .x5]),
  .block (ws ++ base aX .x16 ++ [ld .x5 .x16, .lsr .x .x5 .x5 1, next .x16, .subImm .x .x14 .x12 1]),
  countLoop .x14 [ld .x3 .x16, .logic .orr .x .x5 .x5 .x3, next .x16],
  .block ([movi .x7 0, .subImm .x .x8 .x7 1, movi .x4 1, .subs .x .x3 .x5 .x4, .csel .x .x9 .x8 .x7] ++ ws ++
    base aX .x16 ++ base aN .x17 ++ [ld .x3 .x16, .logic .orr .x .x3 .x3 .x4, ld .x4 .x17, .subs .x .x3 .x3 .x4,
    next .x16, next .x17, .subImm .x .x14 .x12 1]),
  cmpLoop,
  .block [.csel .x .x15 .x7 .x8, .logic .and .x .x9 .x9 .x15],
  .ite (.zero .x .x9) (.block [movi .x3 4, sth .x3 kStat]) (seqs (round mul roundCode))]

/-- Witnesses while `kStat = 4`; 0 when fewer than `sK` octets of `rand`
are left (`rand_len − used`, which does not wrap). -/
def millerRabin (mul : Nat → Nat → Nat → Prog isa) (roundCode : List (Prog isa)) : List (Prog isa) := [
  .block [movi .x3 0, sth .x3 fIdx],
  .loop (seqs [
    .block ([ldh .x3 kRandLen, ldh .x4 kUsed, .sub .x .x3 .x3 .x4, ldh .x4 kLen] ++ geFlag),
    .ite (.zero .x .x5) (.block [movi .x3 0, sth .x3 kStat]) (seqs (draw mul roundCode)),
    .block [ldh .x3 kStat, .subImm .x .x3 .x3 4]]) (.zero .x .x3)]

/-- The test of `q` (with `q` in `aN`) or of `p` (loaded again). -/
def test (q : Bool) (mul : Nat → Nat → Nat → Prog isa) (roundCode : List (Prog isa)) : List (Prog isa) :=
  phase q ++ (if q then [] else shapeP) ++ montPrep mul ++ expSetup ++ millerRabin mul roundCode

/-! ## `vg_ffdh_parameter_candidate` -/

/-- After `p`'s test: 0, 1 (`p` to `out`) or 2. -/
def pResult : Prog isa :=
  .seq (.block [ldh .x3 kStat])
    (.ite (.zero .x .x3) finNone (.seq (.block [.subImm .x .x3 .x3 1]) (.ite (.zero .x .x3) finPrime (finUsed 2))))

/-- After a failed test of `q`: 0 or 2. -/
def qResult : Prog isa := .seq (.block [ldh .x3 kStat]) (.ite (.zero .x .x3) finNone (finUsed 2))

/-- The tests, once the shape passed. -/
def tests (mul : Nat → Nat → Nat → Prog isa) (roundCode : List (Prog isa)) : Prog isa :=
  seqs (test true mul roundCode ++ [.block [ldh .x3 kStat, .subImm .x .x3 .x3 1],
    .ite (.zero .x .x3) (seqs (test false mul roundCode ++ [pResult])) qResult])

/-- Once `rand` holds the candidate's octets: `p`, its congruence, rejected
before any other check (most candidates fail it); then the sieves of `p`
and `q`, and the tests. -/
def main (mul : Nat → Nat → Nat → Prog isa) (roundCode : List (Prog isa)) : Prog isa :=
  seqs (phase false ++ shapeP ++ residue ++ [.block [ldh .x5 fBad], .ite (.zero .x .x5)
    (seqs ([tableWrite] ++ sieve ++ halveQ ++ sieve ++
      [.block [ldh .x5 fBad], .ite (.zero .x .x5) (tests mul roundCode) (finUsed 2)]))
    (finUsed 2)])

/-- `vg_ffdh_parameter_candidate`. -/
def code (mul : Nat → Nat → Nat → Prog isa) (roundCode : List (Prog isa)) : Prog isa :=
  seqs [.block entry, zeroOut kOut kLen, .block ([ldh .x3 kRandLen, ldh .x4 kLen] ++ geFlag),
    .ite (.zero .x .x5) finNone (main mul roundCode)]

end VG.Impl.Ffdh.AArch64.ParameterCandidate
