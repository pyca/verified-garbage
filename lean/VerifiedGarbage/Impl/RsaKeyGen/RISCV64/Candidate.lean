module

public import VerifiedGarbage.Impl.RsaKeyGen.RISCV64.Witness

/-!
# A candidate for a prime of an RSA key on RISC-V

`vg_rsa_keygen_candidate(out, out_len, used, e, e_len, p, p_len, rand,
rand_len, scratch, scratch_len)`: the first eight arguments in `a0`–`a7`,
the others on the stack, at `sp + 8 i` for the `i`-th of them (`rand_len`
is the 0th). A frame of `frameBytes` is allocated; `s0`–`s11` and the return
address are saved in it, and the arguments kept there (RISC-V has too few
registers that neither the Montgomery routines, the prime search's pieces
nor the round write), its address in `s11`.

The numbers live in the Montgomery working space of RSA's functions at
`scratch` (`s6`; `Proof.Rsa.Mont.Layout`: a header of 32 words, then arrays
of `w + 2` words for `w = out_len / 8`), as the shared Miller–Rabin round
takes it, with the prime search's state in its header
(`Impl/MillerRabin/RISCV64/Search.lean`) and its registers: `a7` array 0's
base, `s5` the arrays' size, `t0` `w`. The candidate `c` is array 0. As on
PPC64LE (`Impl/RsaKeyGen/PPC64LE/Candidate.lean`):

1. `out` is zeroed; if `rand` is shorter than `out_len`, the result is 0.
2. The working space's header (`w`, the stride, the arrays' addresses and
   `scratch_len`), its first `nArr` arrays zeroed; `c`: the first `out_len`
   octets of `rand` (`loadN`), its two top bits and its low bit set.
3. If `p` is given: `c − p` and `p − c` (`subMod64`), the one that does not
   borrow selected (`selectAcc64`) under the mask of the first's borrow,
   compared with `2^(8 out_len − 100)`; the result is 2 if it is not above.
4. `gcd(c − 1, e)`: 3 if `e` is even; nothing for `e = 1`; otherwise
   `(c − 1) mod e`, bit by bit from the top, then 128 steps of a binary gcd
   on words with masks (`Proof/RsaKeyGen/Gcd.lean`); 3 unless it is 1.
5. The prime test: trial division by the first 512 entries of the table of
   small primes (1024 above 1024 bits), by `Trial.trial` (whose count is in
   `hTrial`), 3 if one divides `c`; then `montPrepHi` (`c` has its top bit
   set) and RSA's witnesses (`Witness.millerRabin`) from `rand` after the
   candidate, with `rand`, its length, the octets read, a witness's octets
   (`out_len`) and the uniform witnesses needed (`checksW w`) in the header.
   Their status (`hStat`: 0 if `rand` ran out, 1 for a probable prime, 2
   for a rejection) gives the result 0, 1 or 3.
6. `out`: `c`, most significant octet first, for the result 1 (it was
   zeroed otherwise); `used`: the octets read, or 0 for the result 0.

The flags of steps 3 and 4 are in `s9`, and `e`'s value in `s10`. The code
branches on the lengths, `e` and what the leak allows: whether `c` is too
close to `p`, whether `gcd(c − 1, e) = 1`, whether a small prime divides it,
and whether each witness passed.
-/

@[expose] public section

namespace VG.Impl.RsaKeyGen.RISCV64.Candidate

open VG VG.RISCV64 VG.Impl.Bignum VG.Impl.Bignum.RISCV64
open VG.Impl.Bignum.RISCV64.PublicChecked (base)
open VG.Impl.Bignum.RISCV64.Precompute (loadN copyWords)
open VG.Impl.MillerRabin.RISCV64.Search (ldh sth geFlag hWsLen hRand hRandLen hUsed hStat hChecks hK hW
  hStride montPrepHi)

/-- Right-nested sequencing. -/
def seqs : List (Prog isa) → Prog isa
  | [] => .block []
  | [c] => c
  | c :: cs => .seq c (seqs cs)

/-! ## The frame -/

/-- The frame: `s0`–`s11` at `8 i`, the return address, then the arguments. -/
def frameBytes : Nat := 192

/-- The callee-saved registers, saved at `8 i`. -/
def saved : List Reg := [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11]

def oRa : Nat := 96
def oOut : Nat := 104
def oOutLen : Nat := 112
def oUsed : Nat := 120
def oE : Nat := 128
def oELen : Nat := 136
def oP : Nat := 144
def oPLen : Nat := 152
def oRand : Nat := 160
def oRandLen : Nat := 168
/-- The octets of `rand` read so far. -/
def oRead : Nat := 176
def oWsLen : Nat := 184

/-- `r :=` the frame's word at `o`, and its store. -/
def ldf (r : Reg) (o : Nat) : Instr := .load .d r .s11 o
def stf (r : Reg) (o : Nat) : Instr := .store .d r .s11 o

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

/-- `s0`–`s11` and the return address into the frame (through `t2`), its
address into `s11`; the arguments into it, `scratch` into `s6`, and the
octets read := 0. -/
def entry : List Instr :=
  .addSp .t2 0 :: (saved.zipIdx.map fun (r, i) => .store .d r .t2 (8 * i)) ++
  [.store .d .ra .t2 oRa, .addi .s11 .t2 0, stf .a0 oOut, stf .a1 oOutLen, stf .a2 oUsed, stf .a3 oE,
    stf .a4 oELen, stf .a5 oP, stf .a6 oPLen, stf .a7 oRand, ldf .t3 frameBytes, stf .t3 oRandLen,
    ldf .s6 (frameBytes + 8), ldf .t3 (frameBytes + 16), stf .t3 oWsLen, .li .t3 0, stf .t3 oRead]

/-- `s0`–`s11` and the return address back from the frame, through `t2`
(`a0` kept). -/
def restore : List Instr :=
  [.addSp .t2 0, .load .d .ra .t2 oRa] ++ saved.zipIdx.map fun (r, i) => .load .d r .t2 (8 * i)

/-- `out`'s `out_len` octets := 0. -/
def zeroOut : Prog isa :=
  .seq (.block [ldf .t3 oOut, ldf .t5 oOutLen, .li .t2 0])
    (countLoop .t5 [.store .b .t2 .t3 0, .addi .t3 .t3 1])

/-- `used :=` the octets read, and the result `r`. -/
def finish (r : Nat) : Prog isa := .block [ldf .t2 oRead, ldf .t3 oUsed, .store .d .t2 .t3 0, .li .a0 r]

/-- The result 0: `used := 0`. -/
def finNone : Prog isa := .seq (.block [.li .t2 0, stf .t2 oRead]) (finish 0)

/-- The result 1: `c`'s `out_len` octets, most significant first, to `out`. -/
def finPrime : Prog isa :=
  .seq (.block [ldf .t5 oOutLen, .add .t3 .a7 .t5, .addi .t3 .t3 (-1), ldf .t4 oOut])
    (.seq (countLoop .t5 [.load .b .t2 .t3 0, .store .b .t2 .t4 0, .addi .t4 .t4 1, .addi .t3 .t3 (-1)])
      (finish 1))

/-! ## The candidate -/

/-- `scratch_len`, `w = out_len / 8` (`t0`), the stride (`s5`), array 0 (`a7`)
and the arrays' addresses into the header; then the first `nArr` arrays
zeroed. -/
def setup : Prog isa :=
  .seq (.block ([ldf .t2 oWsLen, sth .t2 hWsLen, ldf .t2 oOutLen, .shift .srl .d .t0 .t2 3, sth .t0 hW,
      .addi .s5 .t0 2, .shift .sll .d .s5 .s5 3, sth .s5 hStride, .addi .a7 .s6 hdrBytes] ++
      (List.range 8).flatMap (fun j => base .t2 j ++ [sth .t2 (8 + j)]) ++
      [.addi .t3 .a7 0, .li .t5 nArr, .mul .t5 .t5 .s5, .shift .srl .d .t5 .t5 3, .li .t2 0]))
    (countLoop .t5 [.store .d .t2 .t3 0, .addi .t3 .t3 8])

/-- `c`: the first `out_len` octets of `rand` into array 0, its low bit and
two top bits set; the octets read := `out_len`. -/
def loadC : Prog isa :=
  .seq (.block [ldf .s7 oRand, ldf .s8 oOutLen]) (.seq loadN
    (.block [.load .d .t2 .a7 0, .logicImm .or .t2 .t2 1, .store .d .t2 .a7 0,
      .shift .sll .d .t3 .t0 3, .add .t3 .t3 .a7, .addi .t3 .t3 (-8), .load .d .t2 .t3 0, .li .t4 3,
      .shift .sll .d .t4 .t4 62, .logic .or .t2 .t2 .t4, .store .d .t2 .t3 0, ldf .t2 oOutLen, stf .t2 oRead]))

/-! ## Too close to `p` -/

/-- `[o] := [a] − [b]` (`subMod64`, with `a7` at `b` meanwhile), the mask of
the borrow in `s4`; `a7` back at array 0. -/
def sub (o a b : Nat) : Prog isa :=
  .seq (.block (base .a5 a ++ base .a6 o ++ base .t2 b ++ [.addi .a7 .t2 0]))
    (.seq subMod64 (.block [.addi .a7 .s6 hdrBytes]))

/-- `p` into `aP`. -/
def loadP : Prog isa :=
  .seq (.block (base .t2 aP ++ [.addi .a7 .t2 0, ldf .s7 oP, ldf .s8 oOutLen]))
    (.seq loadN (.block [.addi .a7 .s6 hdrBytes]))

/-- `s9 := 1` if `|c − p| ≤ 2^(64 w − 100)`, else 0: `c − p` (its borrow's
mask kept in `s9`) and `p − c`, the latter selected under the mask, then
the borrow of `bound − |c − p|`, whose word `w − 2` is `2^28`. -/
def closeCalc : List (Prog isa) :=
  [loadP, sub aD1 0 aP, .block [.addi .s9 .s4 0], sub aD2 aP 0,
    .seq (.block (base .a5 aD2 ++ base .a6 aD1 ++ base .a2 aAbs ++ [.addi .s4 .s9 0])) selectAcc64,
    .block (base .t3 aBnd ++ [.shift .sll .d .t4 .t0 3, .add .t3 .t3 .t4, .addi .t3 .t3 (-16), .li .t2 1,
      .shift .sll .d .t2 .t2 28, .store .d .t2 .t3 0]),
    sub aTmp aBnd aAbs,
    .block [.logicImm .and .s9 .s4 1, .logicImm .xor .s9 .s9 1]]

/-- `s9`: whether `c` is too close to `p`, 0 without `p`. -/
def closeCheck : Prog isa :=
  .seq (.block [ldf .t2 oPLen]) (.ite (.zero .t2) (.block [.li .s9 0]) (seqs closeCalc))

/-! ## `gcd(c − 1, e)` -/

/-- `e`'s `e_len` octets, most significant first, into `s10`. -/
def loadE : Prog isa :=
  .seq (.block [.li .t2 0, ldf .t3 oE, ldf .t5 oELen])
    (.seq (countLoop .t5 [.shift .sll .d .t2 .t2 8, .load .b .t4 .t3 0, .add .t2 .t2 .t4, .addi .t3 .t3 1])
      (.block [.addi .s10 .t2 0]))

/-- One bit of `(c − 1) mod e`: `a1 := 2 a1 + ` the top bit of `a2` (its
carry into `a3`), `a2` shifted; then `a1 − e` kept if that carried or did
not borrow. -/
def modBit : List Instr :=
  [.shift .srl .d .a3 .a1 63, .shift .srl .d .a4 .a2 63, .shift .sll .d .a1 .a1 1, .add .a1 .a1 .a4,
    .shift .sll .d .a2 .a2 1, .sltu .a4 .a1 .s10, .logicImm .xor .a4 .a4 1, .logic .or .a4 .a4 .a3, .li .a5 0,
    .sub .a4 .a5 .a4, .sub .a5 .a1 .s10, .logic .xor .a5 .a5 .a1, .logic .and .a5 .a5 .a4,
    .logic .xor .a1 .a1 .a5]

/-- `a1 := (c − 1) mod e`: `c` copied to `aCm1`, less 1 (its low word is
odd), then its words from the top (`t3` walking down, `a6` counting), 64
bits each (`t5` counting). -/
def modE : Prog isa :=
  .seq (.block (base .t3 aCm1 ++ [.addi .t4 .a7 0])) (.seq copyWords
    (.seq (.block (base .t3 aCm1 ++ [.load .d .t2 .t3 0, .addi .t2 .t2 (-1), .store .d .t2 .t3 0,
        .shift .sll .d .t4 .t0 3, .add .t3 .t3 .t4, .addi .a6 .t0 0, .li .a1 0]))
      (.loop (.seq (.block [.addi .t3 .t3 (-8), .load .d .a2 .t3 0, .li .t5 64]) (.seq (countLoop .t5 modBit)
          (.block [.addi .a6 .a6 (-1)])))
        (.nonzero .a6))))

/-- One step of the binary gcd on `u = a1` and the odd `v = s10`: if `u` is
odd, `(|u − v|, min u v)`; then `u / 2`. -/
def gcdStep : List Instr :=
  [.sltu .a3 .a1 .s10, .li .t2 0, .sub .a3 .t2 .a3, .logicImm .and .a4 .a1 1, .sub .a4 .t2 .a4,
    .sub .a5 .a1 .s10, .sub .a2 .s10 .a1, .logic .xor .a2 .a2 .a5, .logic .and .a2 .a2 .a3,
    .logic .xor .a5 .a5 .a2,
    .logic .xor .a2 .a1 .s10, .logic .and .a2 .a2 .a3, .logic .xor .a2 .a2 .s10,
    .logic .xor .a5 .a5 .a1, .logic .and .a5 .a5 .a4, .logic .xor .a1 .a1 .a5,
    .logic .xor .a2 .a2 .s10, .logic .and .a2 .a2 .a4, .logic .xor .s10 .s10 .a2,
    .shift .srl .d .a1 .a1 1]

/-- `s9 := gcd(c − 1, e) − 1` for the odd `e > 1` in `s10`: `(c − 1) mod e`,
then 128 steps. -/
def gcdE : Prog isa :=
  .seq modE (.seq (.block [.li .t5 128]) (.seq (countLoop .t5 gcdStep) (.block [.addi .s9 .s10 (-1)])))

/-- `s9` nonzero iff `gcd(c − 1, e) ≠ 1`: 1 for an even `e`, 0 for `e = 1`. -/
def gcdCheck : Prog isa :=
  .seq loadE (.seq (.block [.logicImm .and .t2 .s10 1])
    (.ite (.zero .t2) (.block [.li .s9 1])
      (.seq (.block [.addi .t2 .s10 (-1)]) (.ite (.zero .t2) (.block [.li .s9 0]) gcdE))))

/-! ## The prime test -/

/-- The table entries trial division uses: a header word the search leaves
to its caller. -/
def hTrial : Nat := 16

/-- `s0 := v` if `w ≥ k`, for `w` in `t0` (`t3`, `t4` written). -/
def checksIf (k v : Nat) : List Instr :=
  [.li .t4 k, .sltu .t3 .t0 .t4, .addi .t3 .t3 (-1), .li .t4 v, .logic .xor .t4 .t4 .s0,
    .logic .and .t4 .t4 .t3, .logic .xor .s0 .s0 .t4]

/-- The test's inputs in the header: `rand`, its length, the octets read, a
witness's octets, `checksW w`, and the table entries (`512 (1 + [w > 16])`). -/
def testArgs : List Instr :=
  [ldf .t2 oRand, sth .t2 hRand, ldf .t2 oRandLen, sth .t2 hRandLen, ldf .t2 oRead, sth .t2 hUsed,
    ldf .t2 oOutLen, sth .t2 hK, .li .s0 27] ++
  checksIf 5 8 ++ checksIf 6 7 ++ checksIf 7 6 ++ checksIf 8 5 ++ checksIf 22 4 ++ checksIf 59 3 ++
  [sth .s0 hChecks, .li .t2 16, .sltu .t2 .t2 .t0, .shift .sll .d .t2 .t2 9, .addi .t2 .t2 512, sth .t2 hTrial]

/-- The test's result: 0, 1 or 3 from its status 0, 1 or 2, with the octets
read. -/
def testResult : Prog isa :=
  .seq (.block [ldh .t2 hUsed, stf .t2 oRead, ldh .t2 hStat])
    (.ite (.zero .t2) finNone (.seq (.block [.addi .t2 .t2 (-1)]) (.ite (.zero .t2) finPrime (finish 3))))

/-- Once `gcd(c − 1, e) = 1`: trial division (`a4` nonzero if a small prime
divides `c`), then Miller–Rabin. -/
def test (trial : Prog isa) (name : String) (round : Prog isa) : Prog isa :=
  seqs [.block testArgs, trial,
    .ite (.nonzero .a4) (finish 3) (seqs [montPrepHi, Witness.millerRabin name round, testResult])]

/-! ## `vg_rsa_keygen_candidate` -/

/-- Once `rand` has the candidate's octets. -/
def main (trial : Prog isa) (name : String) (round : Prog isa) : Prog isa :=
  seqs [setup, loadC, closeCheck,
    .ite (.nonzero .s9) (finish 2)
      (.seq gcdCheck (.ite (.nonzero .s9) (finish 3) (test trial name round)))]

/-- The body, in the frame. -/
def body (trial : Prog isa) (name : String) (round : Prog isa) : Prog isa :=
  seqs [.block entry, zeroOut, .block ([ldf .t3 oRandLen, ldf .t4 oOutLen] ++ geFlag .t2 .t3 .t4),
    .ite (.zero .t2) finNone (main trial name round), .block restore]

/-- `vg_rsa_keygen_candidate`, with trial division `trial` and calling the
Miller–Rabin round `round` named `name`. -/
def code (trial : Prog isa) (name : String) (round : Prog isa) : Prog isa :=
  .frame (.alloc frameBytes) (body trial name round) (.free frameBytes)

end VG.Impl.RsaKeyGen.RISCV64.Candidate
