module

public import VerifiedGarbage.Impl.MillerRabin.PPC64LE.Search

/-!
# RSA's Miller–Rabin witnesses on PPC64LE

`Spec.RsaKeyGen.loop (mrStep c checks a m) (1, 0)`, the witnesses of RSA's
key generation, over the prime search's pieces (`Search.lean`), after
`montPrep`, in the Montgomery working space with the search's header. Unlike
`Search.millerRabin`, every draw is a witness, and nothing branches on a
draw: as ARMv7's `witnessFix` and `onPass` (`Impl/RsaKeyGen/Arm/Candidate.lean`)
and AArch64's `mrWitness` and `mrRound`, a draw `x` (the next `hK` octets of
the tape, most significant first, into array 4) is uniform if
`2 ≤ x < c − 1` (`x ≥ 2`, and the borrow of `(x | 1) − c`), its flag a mask;
the forced witness (`Spec.RsaKeyGen.witness`: bit 1 set, the top bit
cleared) is selected under the mask's complement, and the flag added to the
uniform witnesses so far (`hUni`). Its round follows (`Search.roundCall`);
then

* the round failed: `hStat := 2`;
* it passed: one more witness (`hIdx`, from 1), and `hStat := 1` once there
  are more than `blindedChecks` (16) of them and `hChecks` uniform ones,
  else `hStat := 4`, which goes on;
* the tape had fewer than `hK` octets left: `hStat := 0`.

The code branches on whether each round passed and whether more witnesses
are needed, which the leak of an accepted candidate (the octets read)
determines, and on the tape's length.

It writes `r21` (the mask) and what the search's pieces write; `r23`–`r28`
and `r30` are kept.
-/

@[expose] public section

namespace VG.Impl.RsaKeyGen.PPC64LE.Witness

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE
open VG.Impl.Bignum.PPC64LE.PublicChecked (base)
open VG.Impl.Bignum.PPC64LE.Precompute (loadN copyWords)
open VG.Impl.MillerRabin.PPC64LE.Search (ldh sth geFlag roundCall hRand hRandLen hUsed hStat hChecks hIdx hK)

/-- The uniform witnesses so far: a header word the search leaves to its
caller. -/
def hUni : Nat := 2

/-- The next `hK` octets of `rand` into array 4 (`hUsed` advanced); `r10`
back at array 0. -/
def load : Prog isa :=
  .seq (.block ([ldh .r12 hRand, ldh .r3 hUsed, .add .r12 .r12 .r3, ldh .r6 hK, .add .r3 .r3 .r6, sth .r3 hUsed] ++
      base .r10 4))
    (.seq loadN (.block [.addi .r10 .r31 hdrBytes]))

/-- `r21 := 1` if `x ≥ 2`, else 0: `x₀ >> 1` or'ed with the other words, then
whether that is not zero. -/
def atLeast2 : Prog isa :=
  .seq (.block (base .r5 4 ++ [.load .d .r21 .r5 0, .lsr .d .r21 .r21 1, .addi .r5 .r5 8, .lsr .d .r6 .r11 1,
      .subi .r6 .r6 1]))
    (.seq (Precompute.countLoop .r6 [.load .d .r3 .r5 0, .logic .or .r21 .r21 .r3, .addi .r5 .r5 8])
      (.block [.lsr .d .r3 .r21 1, .li .r0 1, .logic .and .r21 .r21 .r0, .logic .or .r21 .r21 .r3,
        .subi .r21 .r21 1, .lsr .d .r21 .r21 63, .logic .xor .r21 .r21 .r0]))

/-- `x` into array 3, its word `w` zeroed. -/
def toThree : Prog isa :=
  .seq (.block (base .r14 3 ++ base .r15 4))
    (.seq copyWords (.block (base .r5 3 ++ [.lsl .r6 .r11 2, .add .r5 .r5 .r6, .li .r0 0, .store .d .r0 .r5 0])))

/-- `r21 :=` 1 if `x` is uniform, else 0: `r21 &=` the borrow of `(x | 1) − c`
(`subMod` of a copy of `x | 1`, in array 3, and `c`, into array 6). -/
def uniform : Prog isa :=
  .seq atLeast2 (.seq toThree (.seq (.block (base .r5 3 ++ [.load .d .r3 .r5 0, .li .r4 1,
      .logic .or .r3 .r3 .r4, .store .d .r3 .r5 0] ++ base .r8 3 ++ base .r9 6)) (.seq subMod
    (.block [.li .r0 1, .logic .and .r3 .r20 .r0, .logic .and .r21 .r21 .r3]))))

/-- The forced witness in array 3: `x` with bit 1 set and its top bit cleared. -/
def forced : Prog isa :=
  .seq toThree (.block (base .r5 3 ++ [.load .d .r3 .r5 0, .li .r4 2, .logic .or .r3 .r3 .r4, .store .d .r3 .r5 0,
    .lsl .r6 .r11 2, .add .r5 .r5 .r6, .subi .r5 .r5 8, .li .r4 0, .subi .r4 .r4 1, .lsr .d .r4 .r4 1,
    .load .d .r3 .r5 0, .logic .and .r3 .r3 .r4, .store .d .r3 .r5 0]))

/-- The witness into array 4: `x` if uniform, else the forced one (selected
into array 6, then copied); the flag added to `hUni`. -/
def witness : Prog isa :=
  .seq uniform (.seq forced
    (.seq (.block [.li .r0 0, .sub .r20 .r0 .r21]) (.seq (MillerRabin.PPC64LE.sel 6 4 3)
      (.seq (MillerRabin.PPC64LE.copy 4 6) (.block [ldh .r3 hUni, .add .r3 .r3 .r21, sth .r3 hUni])))))

/-- After a passing round: one more witness, and `hStat := 1` if there are at
least 17 (from 1) and `hChecks` uniform ones, else 4. -/
def passed : List Instr :=
  [ldh .r3 hIdx, .addi .r3 .r3 1, sth .r3 hIdx, .li .r4 17] ++ geFlag .r5 .r3 .r4 ++
    [.addi .r7 .r5 0, ldh .r3 hUni, ldh .r4 hChecks] ++ geFlag .r5 .r3 .r4 ++
    [.logic .and .r5 .r5 .r7, .li .r4 3, .mul .r5 .r5 .r4, .li .r4 4, .sub .r5 .r4 .r5, sth .r5 hStat]

/-- A witness's round, and its outcome. -/
def round (name : String) (roundCode : Prog isa) : Prog isa :=
  .seq (roundCall name roundCode)
    (.ite (.zero .d .r3) (.block [.li .r3 2, sth .r3 hStat]) (.block passed))

/-- One draw: its witness and round. -/
def draw (name : String) (roundCode : Prog isa) : Prog isa :=
  .seq load (.seq witness (round name roundCode))

/-- Witnesses while `hStat = 4`; 0 when fewer than `hK` octets of `rand` are
left (`rand_len − used`, which does not wrap). -/
def millerRabin (name : String) (roundCode : Prog isa) : Prog isa :=
  .seq (.block [.li .r3 1, sth .r3 hIdx, .li .r3 0, sth .r3 hUni, .li .r3 4, sth .r3 hStat])
    (.loop (.seq (.block ([ldh .r3 hRandLen, ldh .r4 hUsed, .sub .r3 .r3 .r4, ldh .r4 hK] ++ geFlag .r5 .r3 .r4))
        (.seq (.ite (.zero .d .r5) (.block [.li .r3 0, sth .r3 hStat]) (draw name roundCode))
          (.block [ldh .r3 hStat, .subi .r3 .r3 4])))
      (.zero .d .r3))

end VG.Impl.RsaKeyGen.PPC64LE.Witness
