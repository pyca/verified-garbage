module

public import VerifiedGarbage.Impl.MillerRabin.PPC64LE.Search

/-!
# RSA's blinded Miller–Rabin loop on PPC64LE

`Spec.RsaKeyGen.loop (mrStep c checks a m) (1, 0)`, the loop of RSA's key
generation and DSA's probable-prime test, over the prime search's pieces
(`Search.lean`), after `montPrep`: unlike `Search.millerRabin`, every draw
is a witness. A draw `x` (the next `hK` octets of the tape, most significant
first, its word at byte `hTopOff` of array 4 and'ed with `hTop`, which cuts
it to the bits of `c − 1`) is uniform if `2 ≤ x < c − 1` (`Search.draw`'s
test: `x ≥ 2`, and the borrow of `(x | 1) − c`); otherwise it is forced
into the range (`Spec.RsaKeyGen.witness`): bit 1 set, and the top bit of
its top word cleared (`hTop >> 1`, `hTop` being `2^b − 1` with that bit
`b − 1`). Its round follows; then

* the round failed: `hStat := 2`;
* it passed: one more witness (`hIdx`), and `hStat := 1` once there are at
  least `blindedChecks` (16) of them and `hChecks` uniform ones (`hUni`,
  counted before the round), else `hStat := 4`, which goes on;
* the tape had fewer than `hK` octets left: `hStat := 0`.

Every value is public: the code branches on the tape's contents.
-/

@[expose] public section

namespace VG.Impl.MillerRabin.PPC64LE.Blinded

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE
open VG.Impl.Bignum.PPC64LE.PublicChecked (base)
open VG.Impl.Bignum.PPC64LE.Precompute (loadN copyWords)
open VG.Impl.MillerRabin.PPC64LE.Search

/-- The uniform witnesses so far, and the byte offset of a witness's top
word in its array: header words the search leaves to its caller. -/
def hUni : Nat := 4
def hTopOff : Nat := 16

/-- The next `hK` octets of `rand` into array 4 (`hUsed` advanced), its top
word and'ed with `hTop`; `r10` back at array 0. -/
def load : Prog isa :=
  .seq (.block ([ldh .r12 hRand, ldh .r3 hUsed, .add .r12 .r12 .r3, ldh .r6 hK, .add .r3 .r3 .r6, sth .r3 hUsed] ++
      base .r10 4))
    (.seq loadN (.block ([.addi .r10 .r31 hdrBytes] ++ base .r5 4 ++ [ldh .r6 hTopOff, .add .r5 .r5 .r6,
      ldh .r4 hTop, .load .d .r6 .r5 0, .logic .and .r6 .r6 .r4, .store .d .r6 .r5 0])))

/-- `r24 :=` nonzero exactly if `x ≥ 2`: `x₀ >> 1` or'ed with the other words. -/
def atLeast2 : Prog isa :=
  .seq (.block (base .r5 4 ++ [.load .d .r24 .r5 0, .lsr .d .r24 .r24 1, .addi .r5 .r5 8, .lsr .d .r6 .r11 1,
      .subi .r6 .r6 1]))
    (countLoop .r6 [.load .d .r3 .r5 0, .logic .or .r24 .r24 .r3, .addi .r5 .r5 8])

/-- `r20 :=` all ones exactly if `(x | 1) < c`: `subMod` of a copy of `x | 1`
(array 3, its word `w` zeroed) and `c`, into array 6. -/
def below : Prog isa :=
  .seq (.block (base .r14 3 ++ base .r15 4))
    (.seq copyWords (.seq (.block (base .r5 3 ++ [.load .d .r3 .r5 0, .li .r4 1, .logic .or .r3 .r3 .r4,
        .store .d .r3 .r5 0, .lsl .r6 .r11 2, .add .r5 .r5 .r6, .li .r0 0, .store .d .r0 .r5 0] ++ base .r8 3 ++
        base .r9 6)) subMod))

/-- The draw forced into the range: bit 1 set, and its top bit cleared. -/
def force : List Instr :=
  base .r5 4 ++ [.load .d .r3 .r5 0, .li .r4 2, .logic .or .r3 .r3 .r4, .store .d .r3 .r5 0, ldh .r6 hTopOff,
    .add .r5 .r5 .r6, ldh .r4 hTop, .lsr .d .r4 .r4 1, .load .d .r3 .r5 0, .logic .and .r3 .r3 .r4,
    .store .d .r3 .r5 0]

/-- One more uniform witness. -/
def countUni : List Instr := [ldh .r3 hUni, .addi .r3 .r3 1, sth .r3 hUni]

/-- The draw a witness: counted if uniform, forced otherwise. -/
def witness : Prog isa :=
  .seq atLeast2 (.seq below
    (.ite (.zero .d .r24) (.block force) (.ite (.zero .d .r20) (.block force) (.block countUni))))

/-- After a passing round: one more witness, and `hStat := 1` if there are
at least 16 and `hChecks` uniform ones, else 4. -/
def passed : List Instr :=
  [ldh .r3 hIdx, .addi .r3 .r3 1, sth .r3 hIdx, .li .r4 16] ++ geFlag .r5 .r3 .r4 ++
    [.addi .r7 .r5 0, ldh .r3 hUni, ldh .r4 hChecks] ++ geFlag .r5 .r3 .r4 ++
    [.logic .and .r5 .r5 .r7, .li .r4 3, .mul .r5 .r5 .r4, .li .r4 4, .sub .r5 .r4 .r5, sth .r5 hStat]

/-- A witness's round, and its outcome. -/
def round (name : String) (roundCode : Prog isa) : Prog isa :=
  .seq (roundCall name roundCode)
    (.ite (.zero .d .r3) (.block [.li .r3 2, sth .r3 hStat]) (.block passed))

/-- One draw: its witness and round. -/
def draw (name : String) (roundCode : Prog isa) : Prog isa :=
  .seq load (.seq witness (round name roundCode))

/-- Witnesses while `hStat = 4`; 0 when fewer than `hK` octets of `rand`
are left (`rand_len − used`, which does not wrap). -/
def millerRabin (name : String) (roundCode : Prog isa) : Prog isa :=
  .seq (.block [.li .r3 0, sth .r3 hIdx, sth .r3 hUni, .li .r3 4, sth .r3 hStat])
    (.loop (.seq (.block ([ldh .r3 hRandLen, ldh .r4 hUsed, .sub .r3 .r3 .r4, ldh .r4 hK] ++ geFlag .r5 .r3 .r4))
        (.seq (.ite (.zero .d .r5) (.block [.li .r3 0, sth .r3 hStat]) (draw name roundCode))
          (.block [ldh .r3 hStat, .subi .r3 .r3 4])))
      (.zero .d .r3))

end VG.Impl.MillerRabin.PPC64LE.Blinded
