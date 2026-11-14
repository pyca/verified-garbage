module

public import VerifiedGarbage.Impl.MillerRabin.RISCV64.Search

/-!
# FFDH's prime search on RISC-V: the sieve and the Miller–Rabin loop

The pieces of `Impl/MillerRabin/RISCV64/Search.lean` only FFDH's parameter
candidate uses (`Impl/Ffdh/RISCV64/ParameterCandidate.lean`), as on PPC64LE
(`Impl/MillerRabin/PPC64LE/Search.lean`), in the same working space and
header:

* `smallMod`: the candidate modulo a small number, bit-serially; `sieve ds`:
  `hBad` or'ed with a flag of a divisor in `ds` of the candidate
  (`oddPrimes256`).
* `montPrep`: the modulus's Montgomery constants (`montPrepWith`), `R² mod N`
  by `128 w` doublings (`r2Any`).
* `millerRabin`: witnesses drawn from the tape, `hK` octets each, the top
  word cut by `hTop`, the round called for those in range, until one fails
  (`hStat := 2`), `hChecks` pass (`hStat := 1`) or the tape runs out (`hStat
  := 0`).

Every value is public: the code branches on the tape's contents.
-/

@[expose] public section

namespace VG.Impl.Ffdh.RISCV64.Search

open VG.RISCV64 VG.Impl.Bignum VG.Impl.Bignum.RISCV64
open VG.Impl.Bignum.RISCV64.PublicChecked (base)
open VG.Impl.Bignum.RISCV64.Precompute (zeroWords doubleMod64)
open VG.Impl.MillerRabin.RISCV64.Search

/-! ## Header words -/

/-- The mask of a witness's top word. -/
def hTop : Nat := 24
/-- Nonzero once the candidate is rejected. -/
def hBad : Nat := 25
/-- The modulus's bits. -/
def hMb : Nat := 31

/-! ## The sieve -/

/-- `s0 := ` array 0 mod `s1` (for `s1` in 2..2^62), bit-serially from the
top of its `w` words: `s0 := 2 s0 + b`, less `s1` if that is not below it.
It writes `s0`, `s2`–`s4` and `t3`–`t5`. -/
def smallMod : Prog isa :=
  .seq (.block [.shift .sll .d .t3 .t0 3, .add .t3 .a7 .t3, .addi .t4 .t0 0, .li .s0 0])
    (.loop (.seq (.block [.addi .t3 .t3 (-8), .load .d .s2 .t3 0, .li .t5 64])
        (.seq (countLoop .t5 [.shift .srl .d .s3 .s2 63, .shift .sll .d .s2 .s2 1, .add .s0 .s0 .s0,
            .add .s0 .s0 .s3, .sub .s3 .s0 .s1, .sltu .s4 .s0 .s1, .addi .s4 .s4 (-1), .logic .xor .s3 .s3 .s0,
            .logic .and .s3 .s3 .s4, .logic .xor .s0 .s0 .s3])
          (.block [.addi .t4 .t4 (-1)])))
      (.nonzero .t4))

/-- `a4 |= ` (array 0 mod `d = 0`). -/
def trial (d : Nat) : Prog isa :=
  .seq (.block [.li .s1 d]) (.seq smallMod (.block [.li .t2 1, .sltu .t2 .s0 .t2, .logic .or .a4 .a4 .t2]))

/-- `hBad |= ` the flag of a divisor in `ds` of array 0. -/
def sieve (ds : List Nat) : Prog isa :=
  .seq (.block [ldh .a4 hBad]) (ds.foldr (fun d c => .seq (trial d) c) (.block [sth .a4 hBad]))

/-- The odd primes below 256. -/
def oddPrimes256 : List Nat :=
  [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103,
    107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223,
    227, 229, 233, 239, 241, 251]

/-! ## Miller–Rabin -/

/-- `x := R² mod N = 2^(128 w) mod N` in array 1 from `x = 1`, by `128 w`
modular doublings (counted by `a1`), and `t1 := −N⁻¹ mod 2⁶⁴`
(`Precompute.minv`): for any odd `N ≥ 3`. -/
def r2Any : Prog isa :=
  .seq (.block [.addi .t3 .a2 0]) (.seq zeroWords
    (.seq (.block [.li .s0 1, .store .d .s0 .a2 0, .shift .sll .d .a1 .t0 7])
      (.seq (.loop (.seq doubleMod64 (.block [.addi .a1 .a1 (-1)])) (.nonzero .a1)) (.block Precompute.minv))))

/-- `montPrepWith`, `R² mod N` by `128 w` doublings. -/
def montPrep : Prog isa := montPrepWith r2Any

/-- An accepted witness's round; then `hStat := 2` if it failed, else the
passing witnesses counted and `hStat := 1` once there are `hChecks` of
them, else 4. -/
def round (name : String) (roundCode : Prog isa) : Prog isa :=
  .seq (roundCall name roundCode)
    (.ite (.zero .a0) (.block [.li .t2 2, sth .t2 hStat])
      (.block ([ldh .t2 hIdx, ldh .t3 hChecks, .addi .t2 .t2 1, sth .t2 hIdx] ++ geFlag .t3 .t2 .t3 ++
        [.li .t4 3, .mul .t3 .t3 .t4, .li .t4 4, .sub .t3 .t4 .t3, sth .t3 hStat])))

/-- A draw: the next `hK` octets of `rand` into array 4, the top word
and'ed with `hTop`; the round for `x ≥ 2` and `(x | 1) < N`, else nothing
(`hStat` stays 4). -/
def draw (name : String) (roundCode : Prog isa) : Prog isa :=
  .seq loadDraw (.seq (.block (base .t3 4 ++ [.shift .sll .d .t2 .t0 3, .add .t3 .t3 .t2, .addi .t3 .t3 (-8),
      ldh .t4 hTop, .load .d .t2 .t3 0, .logic .and .t2 .t2 .t4, .store .d .t2 .t3 0]))
    (.seq atLeast2 (.seq ltN
      (.ite (.zero .a3) (.block []) (.ite (.zero .s4) (.block []) (round name roundCode))))))

/-- Witnesses while `hStat = 4`; 0 when the tape runs out. -/
def millerRabin (name : String) (roundCode : Prog isa) : Prog isa :=
  .seq (.block [.li .t2 0, sth .t2 hIdx, .li .t2 4, sth .t2 hStat])
    (.loop (.seq (.block tapeShort)
        (.seq (.ite (.nonzero .t4) (.block [.li .t2 0, sth .t2 hStat]) (draw name roundCode))
          (.block [ldh .t2 hStat, .addi .t2 .t2 (-4)])))
      (.zero .t2))

end VG.Impl.Ffdh.RISCV64.Search
