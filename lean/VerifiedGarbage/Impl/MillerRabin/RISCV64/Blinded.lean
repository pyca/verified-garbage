module

public import VerifiedGarbage.Impl.MillerRabin.RISCV64.Search

/-!
# RSA's blinded Miller–Rabin loop on RISC-V

`Spec.RsaKeyGen.loop (mrStep c checks a m) (1, 0)`, the loop of RSA's key
generation and DSA's probable-prime test, over the prime search's pieces
(`Search.lean`), after `montPrep`, as on PPC64LE
(`Impl/MillerRabin/PPC64LE/Blinded.lean`): unlike `Search.millerRabin`,
every draw is a witness. A draw `x` (the next `hK` octets of the tape, most
significant first, its word at byte `hTopOff` of array 4 and'ed with `hTop`,
which cuts it to the bits of `c − 1`) is uniform if `2 ≤ x < c − 1`
(`Search.draw`'s test: `x ≥ 2`, and the borrow of `(x | 1) − c`); otherwise
it is forced into the range (`Spec.RsaKeyGen.witness`): bit 1 set, and the
top bit of its top word cleared (`hTop >> 1`, `hTop` being `2^b − 1` with that
bit `b − 1`). Its round follows; then

* the round failed: `hStat := 2`;
* it passed: one more witness (`hIdx`), and `hStat := 1` once there are at
  least 16 of them and `hChecks` uniform ones (`hUni`, counted before the
  round), else `hStat := 4`, which goes on;
* the tape had fewer than `hK` octets left: `hStat := 0`.

Every value is public: the code branches on the tape's contents.
-/

@[expose] public section

namespace VG.Impl.MillerRabin.RISCV64.Blinded

open VG.RISCV64 VG.Impl.Bignum VG.Impl.Bignum.RISCV64
open VG.Impl.Bignum.RISCV64.PublicChecked (base)
open VG.Impl.MillerRabin.RISCV64.Search

/-- The uniform witnesses so far, and the byte offset of a witness's top
word in its array: header words the search leaves to its caller. -/
def hUni : Nat := 4
def hTopOff : Nat := 16

/-- `t3 :=` the address of the witness's top word, at byte `hTopOff` of
array 4. -/
def topAddr : List Instr := base .t3 4 ++ [ldh .t2 hTopOff, .add .t3 .t3 .t2]

/-- The next `hK` octets of `rand` into array 4, its top word and'ed with
`hTop`. -/
def load : Prog isa :=
  .seq loadDraw (.block (topAddr ++ [ldh .t4 hTop, .load .d .t2 .t3 0, .logic .and .t2 .t2 .t4,
    .store .d .t2 .t3 0]))

/-- The draw forced into the range: bit 1 set, and its top bit cleared. -/
def force : List Instr :=
  base .t3 4 ++ [.load .d .t2 .t3 0, .logicImm .or .t2 .t2 2, .store .d .t2 .t3 0] ++ topAddr ++
    [ldh .t4 hTop, .shift .srl .d .t4 .t4 1, .load .d .t2 .t3 0, .logic .and .t2 .t2 .t4, .store .d .t2 .t3 0]

/-- One more uniform witness. -/
def countUni : List Instr := [ldh .t2 hUni, .addi .t2 .t2 1, sth .t2 hUni]

/-- The draw a witness: counted if uniform, forced otherwise. -/
def witness : Prog isa :=
  .seq atLeast2 (.seq ltN
    (.ite (.zero .a3) (.block force) (.ite (.zero .s4) (.block force) (.block countUni))))

/-- After a passing round: one more witness, and `hStat := 1` if there are
at least 16 and `hChecks` uniform ones, else 4. -/
def passed : List Instr :=
  [ldh .t2 hIdx, .addi .t2 .t2 1, sth .t2 hIdx, .li .t3 16] ++ geFlag .t5 .t2 .t3 ++
    [ldh .t2 hUni, ldh .t3 hChecks] ++ geFlag .t4 .t2 .t3 ++
    [.logic .and .t4 .t4 .t5, .li .t3 3, .mul .t4 .t4 .t3, .li .t3 4, .sub .t4 .t3 .t4, sth .t4 hStat]

/-- A witness's round, and its outcome. -/
def round (name : String) (roundCode : Prog isa) : Prog isa :=
  .seq (roundCall name roundCode)
    (.ite (.zero .a0) (.block [.li .t2 2, sth .t2 hStat]) (.block passed))

/-- One draw: its witness and round. -/
def draw (name : String) (roundCode : Prog isa) : Prog isa :=
  .seq load (.seq witness (round name roundCode))

/-- Witnesses while `hStat = 4`; 0 when fewer than `hK` octets of `rand`
are left. -/
def millerRabin (name : String) (roundCode : Prog isa) : Prog isa :=
  .seq (.block [.li .t2 0, sth .t2 hIdx, sth .t2 hUni, .li .t2 4, sth .t2 hStat])
    (.loop (.seq (.block tapeShort)
        (.seq (.ite (.nonzero .t4) (.block [.li .t2 0, sth .t2 hStat]) (draw name roundCode))
          (.block [ldh .t2 hStat, .addi .t2 .t2 (-4)])))
      (.zero .t2))

end VG.Impl.MillerRabin.RISCV64.Blinded
