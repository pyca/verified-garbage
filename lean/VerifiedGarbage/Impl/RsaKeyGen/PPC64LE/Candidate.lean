module

public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Witness

/-!
# A candidate for a prime of an RSA key on PPC64LE

`vg_rsa_keygen_candidate(out, out_len, used, e, e_len, p, p_len, rand,
rand_len, scratch, scratch_len)`: the first eight arguments in `r3`–`r10`,
the others on the stack, at `sp + 96 + 8 i` for the `i`-th of them
(`rand_len` is the 0th). The return address is moved to `r0` and pushed, a
frame of `frameBytes` is allocated, and `r14`–`r31` are saved in it.

The numbers live in the Montgomery working space of RSA's functions at
`scratch` (`Proof.Rsa.Mont.Layout`: a header of 32 words, then arrays of
`w + 2` words for `w = out_len / 8`), as the shared Miller–Rabin round takes
it, with the prime search's state in its header
(`Impl/MillerRabin/PPC64LE/Search.lean`). The candidate `c` is array 0.
The pointers and lengths stay in nonvolatile registers that neither the
Montgomery routines nor the round write: `out` in `r23`, `out_len` in
`r24`, `used` in `r25`, `rand` in `r26`, `rand_len` in `r27`, and the octets
of `rand` read so far in `r28`; `e` (its pointer, then its value) in `r21`
and `e_len` in `r30`; `p` and `p_len` in `r18` and `r19` until the check
against `p`, which comes before anything that writes them.

1. `out` is zeroed; if `rand` is shorter than `out_len`, the result is 0.
2. The working space's header (`w`, the stride, the arrays' addresses and
   `scratch_len`), its first `nArr` arrays zeroed; `c`: the first `out_len`
   octets of `rand` (`loadN`), its two top bits and its low bit set.
3. If `p` is given: `c − p` and `p − c` (`subMod`), the one that does not
   borrow selected (`selectAcc`) under the mask of the first's borrow,
   compared with `2^(8 out_len − 100)`; the result is 2 if it is not above.
4. `gcd(c − 1, e)`: 3 if `e` is even; nothing for `e = 1`; otherwise
   `(c − 1) mod e`, bit by bit from the top, then 128 steps of a binary gcd
   on words with masks (`Proof/RsaKeyGen/Gcd.lean`); 3 unless it is 1.
   Without the carry bit, `ltU` compares 64-bit numbers by their top bits
   and the borrow of their low 63 bits.
5. The prime test, as `Spec.RsaKeyGen.candidateStep` does it after the check
   of `gcd(c − 1, e)` (which does not draw from `rand`, so its place before
   or after trial division changes nothing): trial division by the first
   512 entries of the table of small primes (1024 above 1024 bits), by
   `trial` (the shared `Trial.trial`, whose count is in `hTrial`; it writes
   `r22`–`r24`, so `out` and `out_len` are saved around it), 3 if one
   divides `c`; then `montPrepHi` (`c` has its top bit set) and RSA's witnesses (`Witness.millerRabin`)
   from `rand` after the candidate, with `rand`, its length, the octets
   read, a witness's octets (`out_len`) and the uniform witnesses needed
   (`checksW w`) in the header. Their status (`hStat`: 0 if `rand` ran out,
   1 for a probable prime, 2 for a rejection) gives the result 0, 1 or 3.
6. `out`: `c`, most significant octet first, for the result 1 (it was
   zeroed otherwise); `used`: the octets read, or 0 for the result 0.

The code branches on the lengths, `e` and what the leak allows: whether `c`
is too close to `p`, whether `gcd(c − 1, e) = 1`, whether a small prime
divides it, and whether each witness passed.
-/

@[expose] public section

namespace VG.Impl.RsaKeyGen.PPC64LE.Candidate

open VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE
open VG.Impl.Bignum.PPC64LE.PublicChecked (base)
open VG.Impl.Bignum.PPC64LE.Precompute (loadN)
open VG.Impl.MillerRabin.PPC64LE.Search (ldh sth geFlag hWsLen hRand hRandLen hUsed hStat hChecks hK hW
  hStride montPrepHi)

/-- Right-nested sequencing. -/
def seqs : List (Prog isa) → Prog isa
  | [] => .block []
  | [c] => c
  | c :: cs => .seq c (seqs cs)

/-! ## The frame -/

/-- The frame allocated after the push of the return address. -/
def frameBytes : Nat := 176

/-- The nonvolatile registers saved in the frame, at `32 + 8 i`. -/
def saved : List Reg :=
  [.r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30,
    .r31]

/-- `r14`–`r31` into the frame, through `r11`. -/
def save : List Instr := .addSp .r11 0 :: (saved.zipIdx.map fun (r, i) => .store .d r .r11 (32 + 8 * i))

/-- `r14`–`r31` from the frame, through `r11`. -/
def restore : List Instr := .addSp .r11 0 :: (saved.zipIdx.map fun (r, i) => .load .d r .r11 (32 + 8 * i))

/-- The caller's stack argument `i` (`rand_len`, `scratch`, `scratch_len`)
into `r`, above the push and the frame. -/
def stackArg (r : Reg) (i : Nat) : List Instr := [.addSp r (48 + frameBytes + 96 + 8 * i), .load .d r r 0]

/-! ## The arrays -/

/-- `p`, the differences and `|c − p|`, the bound, a temporary, and `c − 1`. -/
def aP : Nat := 28
def aD1 : Nat := 29
def aD2 : Nat := 30
def aAbs : Nat := 31
def aBnd : Nat := 32
def aTmp : Nat := 33
def aCm1 : Nat := 34
/-- The arrays zeroed at the start: the round's 28 and these. -/
def nArr : Nat := 35

/-! ## Entry and exit -/

/-- The arguments into their registers; `scratch` into `r31`, `scratch_len`
into `r11`, and `used := 0`. -/
def entry : List Instr :=
  save ++ [.addi .r23 .r3 0, .addi .r24 .r4 0, .addi .r25 .r5 0, .addi .r21 .r6 0, .addi .r30 .r7 0,
    .addi .r18 .r8 0, .addi .r19 .r9 0, .addi .r26 .r10 0] ++
  stackArg .r27 0 ++ stackArg .r31 1 ++ stackArg .r11 2 ++ [.li .r28 0]

/-- `out`'s `out_len` octets := 0. -/
def zeroOut : Prog isa :=
  .seq (.block [.addi .r14 .r23 0, .addi .r17 .r24 0, .li .r0 0])
    (Precompute.countLoop .r17 [.stb .r0 .r14 0, .addi .r14 .r14 1])

/-- `used := r28` and the result `r`. -/
def finish (r : Nat) : Prog isa := .block [.store .d .r28 .r25 0, .li .r3 r]

/-- The result 0: `used := 0`. -/
def finNone : Prog isa := .seq (.block [.li .r28 0]) (finish 0)

/-- The result 1: `c`'s `out_len` octets, most significant first, to `out`. -/
def finPrime : Prog isa :=
  .seq (.block [.addi .r10 .r31 hdrBytes, .add .r15 .r10 .r24, .subi .r15 .r15 1, .addi .r16 .r23 0, .addi .r17 .r24 0])
    (.seq (Precompute.countLoop .r17 [.lbz .r0 .r15 0, .stb .r0 .r16 0, .addi .r16 .r16 1, .subi .r15 .r15 1])
      (finish 1))

/-! ## The candidate -/

/-- `scratch_len`, `w = out_len / 8`, the stride (`r29`), `2 w` (`r11`),
array 0 (`r10`) and the arrays' addresses into the header; then the first
`nArr` arrays zeroed. -/
def setup : Prog isa :=
  .seq (.block ([sth .r11 hWsLen, .lsr .d .r3 .r24 3, sth .r3 hW, .addi .r29 .r3 2, .lsl .r29 .r29 3,
      sth .r29 hStride, .addi .r10 .r31 hdrBytes, .lsl .r11 .r3 1] ++
      (List.range 8).flatMap (fun j => base .r3 j ++ [sth .r3 (8 + j)]) ++
      [.addi .r14 .r10 0, .li .r17 nArr, .mul .r17 .r17 .r29, .lsr .d .r17 .r17 3, .li .r0 0]))
    (Precompute.countLoop .r17 [.store .d .r0 .r14 0, .addi .r14 .r14 8])

/-- `c`: the first `out_len` octets of `rand` into array 0, its low bit and
two top bits set; `used := out_len`. -/
def loadC : Prog isa :=
  .seq (.block [.addi .r12 .r26 0, .addi .r6 .r24 0]) (.seq loadN
    (.block [.load .d .r3 .r10 0, .li .r4 1, .logic .or .r3 .r3 .r4, .store .d .r3 .r10 0,
      .lsl .r5 .r11 2, .add .r5 .r5 .r10, .subi .r5 .r5 8, .load .d .r3 .r5 0, .lis .r4 0xC000,
      .lsl .r4 .r4 32, .logic .or .r3 .r3 .r4, .store .d .r3 .r5 0, .addi .r28 .r24 0]))

/-! ## Too close to `p` -/

/-- `[o] := [a] − [b]` (`subMod`, into `o` through `r9`), the mask of the
borrow in `r20`; `r10` back at array 0. -/
def sub (o a b : Nat) : Prog isa :=
  .seq (.block (base .r8 a ++ base .r9 o ++ base .r10 b)) (.seq subMod (.block [.addi .r10 .r31 hdrBytes]))

/-- `p` into `aP`. -/
def loadP : Prog isa :=
  .seq (.block (base .r10 aP ++ [.addi .r12 .r18 0, .addi .r6 .r24 0]))
    (.seq loadN (.block [.addi .r10 .r31 hdrBytes]))

/-- `r22 := 1` if `|c − p| ≤ 2^(64 w − 100)`, else 0: `c − p` (its borrow's
mask kept in `r22`) and `p − c`, the latter selected under the mask, then
the borrow of `bound − |c − p|`, whose word `w − 2` is `2^28`. -/
def closeCalc : List (Prog isa) :=
  [loadP, sub aD1 0 aP, .block [.addi .r22 .r20 0], sub aD2 aP 0,
    .seq (.block (base .r8 aD2 ++ base .r9 aD1 ++ base .r5 aAbs ++ [.addi .r20 .r22 0])) selectAcc,
    .block (base .r5 aBnd ++ [.lsl .r6 .r11 2, .add .r5 .r5 .r6, .subi .r5 .r5 16, .lis .r0 0x1000,
      .store .d .r0 .r5 0]),
    sub aTmp aBnd aAbs,
    .block [.li .r0 1, .logic .and .r22 .r20 .r0, .logic .xor .r22 .r22 .r0]]

/-- `r22`: whether `c` is too close to `p`, 0 without `p`. -/
def closeCheck : Prog isa := .ite (.zero .d .r19) (.block [.li .r22 0]) (seqs closeCalc)

/-! ## `gcd(c − 1, e)` -/

/-- `e`'s `e_len` octets, most significant first, into `r21`. -/
def loadE : Prog isa :=
  .seq (.block [.li .r3 0, .addi .r14 .r21 0, .addi .r17 .r30 0])
    (.seq (Precompute.countLoop .r17 [.lsl .r3 .r3 8, .lbz .r0 .r14 0, .add .r3 .r3 .r0, .addi .r14 .r14 1])
      (.block [.addi .r21 .r3 0]))

/-- `d := 1` if `a < b`, else 0, for any 64-bit `a` and `b` (`d`, `r0`,
`r15` and `r16` written): by their top bits `x = a₆₃ ⊕ b₆₃`, `b₆₃` if they
differ, else the borrow of their low 63 bits. -/
def ltU (d a b : Reg) : List Instr :=
  [.lsl .r15 a 1, .lsr .d .r15 .r15 1, .lsl .r16 b 1, .lsr .d .r16 .r16 1, .sub .r15 .r15 .r16,
    .lsr .d .r15 .r15 63, .lsr .d d a 63, .lsr .d .r16 b 63, .logic .xor d d .r16,
    .logic .and .r16 .r16 d, .li .r0 1, .logic .xor d d .r0, .logic .and d d .r15, .logic .or d d .r16]

/-- One bit of `(c − 1) mod e`: `r3 := 2 r3 + ` the top bit of `r7` (its
carry into `r8`), `r7` shifted; then `r3 − e` kept if that carried or did
not borrow. -/
def modBit : List Instr :=
  [.lsr .d .r8 .r3 63, .lsr .d .r9 .r7 63, .lsl .r3 .r3 1, .add .r3 .r3 .r9, .lsl .r7 .r7 1] ++
  ltU .r9 .r3 .r21 ++
  [.li .r0 1, .logic .xor .r9 .r9 .r0, .logic .or .r9 .r9 .r8, .li .r0 0, .sub .r9 .r0 .r9,
    .sub .r4 .r3 .r21, .logic .xor .r4 .r4 .r3, .logic .and .r4 .r4 .r9, .logic .xor .r3 .r3 .r4]

/-- `r3 := (c − 1) mod e`: `c` copied to `aCm1`, less 1 (its low word is odd),
then its words from the top (`r14` walking down, `r17` counting), 64 bits
each (`r6` counting). -/
def modE : Prog isa :=
  .seq (.block (base .r14 aCm1 ++ [.addi .r15 .r10 0])) (.seq Precompute.copyWords
    (.seq (.block (base .r14 aCm1 ++ [.load .d .r3 .r14 0, .subi .r3 .r3 1, .store .d .r3 .r14 0,
        .lsl .r5 .r11 2, .add .r14 .r14 .r5, .lsr .d .r17 .r11 1, .li .r3 0]))
      (.loop (.seq (.block [.subi .r14 .r14 8, .load .d .r7 .r14 0, .li .r6 64]) (.seq (Precompute.countLoop .r6 modBit)
          (.block [.subi .r17 .r17 1])))
        (.nonzero .d .r17))))

/-- One step of the binary gcd on `u = r3` and the odd `v = r21`: if `u` is
odd, `(|u − v|, min u v)`; then `u / 2`. -/
def gcdStep : List Instr :=
  ltU .r5 .r3 .r21 ++
  [.li .r0 0, .sub .r5 .r0 .r5, .li .r0 1, .logic .and .r4 .r3 .r0, .li .r0 0, .sub .r4 .r0 .r4,
    .sub .r6 .r3 .r21, .sub .r7 .r21 .r3, .logic .xor .r7 .r7 .r6, .logic .and .r7 .r7 .r5,
    .logic .xor .r6 .r6 .r7,
    .logic .xor .r7 .r3 .r21, .logic .and .r7 .r7 .r5, .logic .xor .r7 .r7 .r21,
    .logic .xor .r6 .r6 .r3, .logic .and .r6 .r6 .r4, .logic .xor .r3 .r3 .r6,
    .logic .xor .r7 .r7 .r21, .logic .and .r7 .r7 .r4, .logic .xor .r21 .r21 .r7,
    .lsr .d .r3 .r3 1]

/-- `r22 := gcd(c − 1, e) − 1` for the odd `e > 1` in `r21`: `(c − 1) mod e`,
then 128 steps. -/
def gcdE : Prog isa :=
  .seq modE (.seq (.block [.li .r9 128]) (.seq (Precompute.countLoop .r9 gcdStep) (.block [.subi .r22 .r21 1])))

/-- `r22` nonzero iff `gcd(c − 1, e) ≠ 1`: 1 for an even `e`, 0 for `e = 1`. -/
def gcdCheck : Prog isa :=
  .seq loadE (.seq (.block [.li .r0 1, .logic .and .r5 .r21 .r0])
    (.ite (.zero .d .r5) (.block [.li .r22 1])
      (.seq (.block [.subi .r5 .r21 1]) (.ite (.zero .d .r5) (.block [.li .r22 0]) gcdE))))

/-! ## The prime test -/

/-- The table entries trial division uses, and `out` and `out_len` saved
around it: header words the search leaves to its caller. -/
def hTrial : Nat := 16
def hOut : Nat := 3
def hOutLen : Nat := 5

/-- `r5 := v` if `w ≥ k`, for `w` in `r3` (`r4`, `r6` written). -/
def checksIf (k v : Nat) : List Instr :=
  [.subi .r4 .r3 k, .lsr .d .r4 .r4 63, .subi .r4 .r4 1, .li .r6 v, .logic .xor .r6 .r6 .r5,
    .logic .and .r6 .r6 .r4, .logic .xor .r5 .r5 .r6]

/-- The test's inputs in the header: `rand`, its length, the octets read, a
witness's octets, `checksW w`, and the table entries (`512 (1 + [w > 16])`). -/
def testArgs : List Instr :=
  [sth .r26 hRand, sth .r27 hRandLen, sth .r28 hUsed, sth .r24 hK, ldh .r3 hW, .li .r5 27] ++
  checksIf 5 8 ++ checksIf 6 7 ++ checksIf 7 6 ++ checksIf 8 5 ++ checksIf 22 4 ++ checksIf 59 3 ++
  [sth .r5 hChecks, .li .r4 16, .sub .r4 .r4 .r3, .lsr .d .r4 .r4 63, .li .r5 512, .mul .r4 .r4 .r5,
    .add .r4 .r4 .r5, sth .r4 hTrial]

/-- Trial division (`r22` nonzero if a small prime divides `c`), with `out`
and `out_len` saved around it. -/
def trialDiv (trial : Prog isa) : Prog isa :=
  .seq (.block [sth .r23 hOut, sth .r24 hOutLen]) (.seq trial (.block [ldh .r23 hOut, ldh .r24 hOutLen]))

/-- The test's result: 0, 1 or 3 from its status 0, 1 or 2, with the octets
read. -/
def testResult : Prog isa :=
  .seq (.block [ldh .r28 hUsed, ldh .r3 hStat])
    (.ite (.zero .d .r3) finNone (.seq (.block [.subi .r3 .r3 1]) (.ite (.zero .d .r3) finPrime (finish 3))))

/-- Once `gcd(c − 1, e) = 1`: trial division, then Miller–Rabin. -/
def test (trial : Prog isa) (name : String) (round : Prog isa) : Prog isa :=
  seqs [.block testArgs, trialDiv trial,
    .ite (.nonzero .d .r22) (finish 3) (seqs [montPrepHi, Witness.millerRabin name round, testResult])]

/-! ## `vg_rsa_keygen_candidate` -/

/-- Once `rand` has the candidate's octets. -/
def main (trial : Prog isa) (name : String) (round : Prog isa) : Prog isa :=
  seqs [setup, loadC, closeCheck,
    .ite (.nonzero .d .r22) (finish 2)
      (.seq gcdCheck (.ite (.nonzero .d .r22) (finish 3) (test trial name round)))]

/-- The body, in the frame. -/
def body (trial : Prog isa) (name : String) (round : Prog isa) : Prog isa :=
  seqs [.block entry, zeroOut, .block (geFlag .r5 .r27 .r24), .ite (.zero .d .r5) finNone (main trial name round),
    .block restore]

/-- `vg_rsa_keygen_candidate`, with trial division `trial` and calling the
Miller–Rabin round `round` named `name`. -/
def code (trial : Prog isa) (name : String) (round : Prog isa) : Prog isa :=
  .seq (.block [.mflr .r0])
    (.seq (.frame (.push .r0) (.frame (.alloc frameBytes) (body trial name round) (.free frameBytes)) (.pop .r0))
      (.block [.mtlr .r0]))

end VG.Impl.RsaKeyGen.PPC64LE.Candidate
