module

public import VerifiedGarbage.Impl.MillerRabin.RISCV64.Search

/-!
# RSA's Miller–Rabin witnesses on RISC-V

`Spec.RsaKeyGen.loop (mrStep c checks a m) (1, 0)`, the witnesses of RSA's
key generation, over the prime search's pieces (`Search.lean`), after
`montPrep`, in the Montgomery working space with the search's header, as on
PPC64LE (`Impl/RsaKeyGen/PPC64LE/Witness.lean`). Unlike
`Search.millerRabin`, every draw is a witness, and nothing branches on a
draw: a draw `x` (the next `hK` octets of the tape, most significant first,
into array 4) is uniform if `2 ≤ x < c − 1` (`x ≥ 2`, and the borrow of
`(x | 1) − c`), its flag in `s9`; the forced witness
(`Spec.RsaKeyGen.witness`: bit 1 set, the top bit cleared) is selected under
the flag's complement, and the flag added to the uniform witnesses so far
(`hUni`). Its round follows (`Search.roundCall`); then

* the round failed: `hStat := 2`;
* it passed: one more witness (`hIdx`, from 1), and `hStat := 1` once there
  are more than `blindedChecks` (16) of them and `hChecks` uniform ones,
  else `hStat := 4`, which goes on;
* the tape had fewer than `hK` octets left: `hStat := 0`.

The code branches on whether each round passed and whether more witnesses
are needed, which the leak of an accepted candidate (the octets read)
determines, and on the tape's length.

It writes `s9` (the flag) and what the search's pieces write; `s5`, `s6`,
`s10` and `s11` are kept.
-/

@[expose] public section

namespace VG.Impl.RsaKeyGen.RISCV64.Witness

open VG VG.RISCV64 VG.Impl.Bignum VG.Impl.Bignum.RISCV64
open VG.Impl.Bignum.RISCV64.PublicChecked (base)
open VG.Impl.Bignum.RISCV64.Precompute (copyWords)
open VG.Impl.MillerRabin.RISCV64.Search (ldh sth geFlag roundCall loadDraw atLeast2 ltN hStat hChecks hIdx)

/-- The uniform witnesses so far: a header word the search leaves to its
caller. -/
def hUni : Nat := 2

/-- `s9 :=` 1 if `x` is uniform, else 0: `x ≥ 2` (`atLeast2`'s `a3` not
zero) and `(x | 1) < c` (`ltN`'s mask `s4`). -/
def uniform : Prog isa :=
  .seq atLeast2 (.seq (.block [.li .t2 0, .sltu .s9 .t2 .a3]) (.seq ltN (.block [.logic .and .s9 .s9 .s4])))

/-- The forced witness in array 3: `x` with bit 1 set and its top bit
cleared. -/
def forced : Prog isa :=
  .seq (.block (base .t3 3 ++ base .t4 4)) (.seq copyWords
    (.block (base .t3 3 ++ [.load .d .t2 .t3 0, .logicImm .or .t2 .t2 2, .store .d .t2 .t3 0,
      .shift .sll .d .t4 .t0 3, .add .t3 .t3 .t4, .addi .t3 .t3 (-8), .li .t4 (-1), .shift .srl .d .t4 .t4 1,
      .load .d .t2 .t3 0, .logic .and .t2 .t2 .t4, .store .d .t2 .t3 0])))

/-- The witness into array 4: `x` if uniform, else the forced one (selected
into array 6 under the mask of the flag, then copied); the flag added to
`hUni`. -/
def witness : Prog isa :=
  .seq uniform (.seq forced
    (.seq (.block ([.li .t2 0, .sub .s4 .t2 .s9] ++ base .a5 4 ++ base .a6 3 ++ base .a2 6)) (.seq selectAcc64
      (.seq (ModExp.copy 4 6) (.block [ldh .t2 hUni, .add .t2 .t2 .s9, sth .t2 hUni])))))

/-- After a passing round: one more witness, and `hStat := 1` if there are at
least 17 (from 1) and `hChecks` uniform ones, else 4. -/
def passed : List Instr :=
  [ldh .t2 hIdx, .addi .t2 .t2 1, sth .t2 hIdx, .li .t3 17] ++ geFlag .t5 .t2 .t3 ++
    [ldh .t2 hUni, ldh .t3 hChecks] ++ geFlag .t4 .t2 .t3 ++
    [.logic .and .t4 .t4 .t5, .li .t3 3, .mul .t4 .t4 .t3, .li .t3 4, .sub .t4 .t3 .t4, sth .t4 hStat]

/-- A witness's round, and its outcome. -/
def round (name : String) (roundCode : Prog isa) : Prog isa :=
  .seq (roundCall name roundCode)
    (.ite (.zero .a0) (.block [.li .t2 2, sth .t2 hStat]) (.block passed))

/-- One draw: its witness and round. -/
def draw (name : String) (roundCode : Prog isa) : Prog isa :=
  .seq loadDraw (.seq witness (round name roundCode))

/-- Witnesses while `hStat = 4`; 0 when fewer than `hK` octets of `rand` are
left (`rand_len − used`, which does not wrap). -/
def millerRabin (name : String) (roundCode : Prog isa) : Prog isa :=
  .seq (.block [.li .t2 1, sth .t2 hIdx, .li .t2 0, sth .t2 hUni, .li .t2 4, sth .t2 hStat])
    (.loop (.seq (.block MillerRabin.RISCV64.Search.tapeShort)
        (.seq (.ite (.nonzero .t4) (.block [.li .t2 0, sth .t2 hStat]) (draw name roundCode))
          (.block [ldh .t2 hStat, .addi .t2 .t2 (-4)])))
      (.zero .t2))

end VG.Impl.RsaKeyGen.RISCV64.Witness
