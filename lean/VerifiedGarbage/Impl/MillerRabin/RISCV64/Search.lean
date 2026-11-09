module

public import VerifiedGarbage.Impl.MillerRabin.RISCV64.Prep

/-!
# A prime search's Miller–Rabin tests on RISC-V

The pieces FFDH's and DSA's parameter generation and RSA's key generation
share, as on PPC64LE (`Impl/MillerRabin/PPC64LE/Search.lean`), in RSA's
Montgomery working space at `s6` (`Proof.Rsa.Mont.Layout`, as the shared
round takes it: a header of 32 words, then arrays of `w + 2` words), with
the public-key operation's registers: `a7` array 0's base, `s5` the arrays'
size, `t0` `w`, `t1` `−N⁻¹ mod 2⁶⁴`. The search's state is in the same header
words as on PPC64LE, which neither the layout (`w` in word 6, `−N⁻¹` in word
7, the arrays' addresses in words 8–15, their size in word 28) nor the round
(words 1, 23, 26, 29 and 30) uses; words 2–5 and 16 are the caller's.

* `montPrepWith r2c`: the modulus's Montgomery constants (`−N⁻¹` by
  Newton's iteration, `R² mod N` by `r2c`, `R mod N`, `N − R mod N`) and
  Miller–Rabin's exponent (`expSetup`); `montPrepHi`, for a modulus whose top
  word is not zero, `R² mod N` by `64 + w` doublings and six Montgomery
  squares (`Precompute.r2`).
* `loadDraw`, `tapeShort`, `ltN`, `atLeast2` and `roundCall`: a witness of
  `hK` octets drawn from the tape, its range checks, and the round's call.

Every value is public: the code branches on the tape's contents. Besides
the registers above, the pieces write `a0`–`a6`, `t2`–`t6`, `s0`–`s4`,
`s7` and `s8`; the round's call writes `ra`, which the caller saves.
-/

@[expose] public section

namespace VG.Impl.MillerRabin.RISCV64.Search

open VG.RISCV64 VG.Impl.Bignum VG.Impl.Bignum.RISCV64
open VG.Impl.Bignum.RISCV64.PublicChecked (base montOp)
open VG.Impl.Bignum.RISCV64.Precompute (loadN copyWords zeroWords doubleMod64)

/-! ## Header words -/

/-- `scratch_len`, in words. -/
def hWsLen : Nat := 0
/-- The tape, its length and the octets read. -/
def hRand : Nat := 17
def hRandLen : Nat := 18
def hUsed : Nat := 19
/-- The tests' result, the witnesses needed and those passed. -/
def hStat : Nat := 20
def hChecks : Nat := 21
def hIdx : Nat := 22
/-- The octets of a witness. -/
def hK : Nat := 27

/-- Header words of the layout. -/
def hW : Nat := 6
def hMinv : Nat := 7
def hStride : Nat := 28

/-- `r := ` header word `i`, and its store. -/
def ldh (r : Reg) (i : Nat) : Instr := .load .d r .s6 (8 * i)
def sth (r : Reg) (i : Nat) : Instr := .store .d r .s6 (8 * i)

/-! ## Comparisons -/

/-- `d := 1` if `a ≥ b` (unsigned), else 0. -/
def geFlag (d a b : Reg) : List Instr := [.sltu d a b, .logicImm .xor d d 1]

/-! ## Miller–Rabin -/

/-- `r2c`'s registers: `x` (array 1) at `a2`, the accumulator (array 2) at
`a5` and the temporary (array 3) at `a6`. -/
def r2Bases : List Instr := base .a2 1 ++ base .a5 2 ++ base .a6 3

/-- `−N⁻¹` and `R² mod N` into the header and array 1 (by `r2c`, which
leaves `−N⁻¹` in `t1`), `R mod N` into array 6 (the product of `R² mod N`
and 1, in array 7), `N − R mod N` into array 10 (`subMod64` of array 0 and
array 6, with `a7` at array 6 meanwhile), `R mod N` copied into array 9, and
the exponent. -/
def montPrepWith (r2c : Prog isa) : Prog isa :=
  .seq (.block r2Bases) (.seq r2c (.seq (.block [sth .t1 hMinv]) (.seq PublicChecked.one (.seq (montOp 6 1 7)
    (.seq (.block (base .a5 0 ++ base .a6 10 ++ base .t2 6 ++ [.addi .a7 .t2 0])) (.seq subMod64
      (.seq (.block [.addi .a7 .s6 hdrBytes]) (.seq (ModExp.copy 9 6) expSetup))))))))

/-- `montPrepWith`, `R² mod N` by `Precompute.r2`, for `N` above
`2^(64 (w − 1))`. -/
def montPrepHi : Prog isa := montPrepWith Precompute.r2

/-- `a7`, `t0` and `t1` from the header, after the round (`s5` is
callee-saved). -/
def regsBack : List Instr := [.addi .a7 .s6 hdrBytes, ldh .t0 hW, ldh .t1 hMinv]

/-- An accepted witness (array 4) in Montgomery form into array 5, and the
round called; its result (a `u32`) zero-extended in `a0`, and `a7`, `t0`
and `t1` from the header. -/
def roundCall (name : String) (roundCode : Prog isa) : Prog isa :=
  .seq (montOp 5 4 1) (.seq (.block [.addi .a0 .s6 0, ldh .a1 hWsLen])
    (.seq (.call name roundCode) (.block ([.shift .sll .d .a0 .a0 32, .shift .srl .d .a0 .a0 32] ++ regsBack))))

/-- The next `hK` octets of `rand` into array 4 (`hUsed` advanced), most
significant first, by `Precompute.loadN` (`s7` the octets, `s8` their
number, `a7` array 4 meanwhile). -/
def loadDraw : Prog isa :=
  .seq (.block ([ldh .s7 hRand, ldh .t2 hUsed, .add .s7 .s7 .t2, ldh .s8 hK, .add .t2 .t2 .s8, sth .t2 hUsed] ++
      base .a7 4))
    (.seq loadN (.block [.addi .a7 .s6 hdrBytes]))

/-- `s4 :=` all ones exactly if `(x | 1) < N`: `subMod64` of a copy of `x |
1` (array 3, its word `w` zeroed) and `N`, into array 6. -/
def ltN : Prog isa :=
  .seq (.block (base .t3 3 ++ base .t4 4)) (.seq copyWords
    (.seq (.block (base .t3 3 ++ [.load .d .t2 .t3 0, .logicImm .or .t2 .t2 1, .store .d .t2 .t3 0,
        .shift .sll .d .t4 .t0 3, .add .t3 .t3 .t4, .li .t2 0, .store .d .t2 .t3 0] ++ base .a5 3 ++ base .a6 6))
      subMod64))

/-- `a3 :=` nonzero exactly if `x ≥ 2`: `x₀ >> 1` or'ed with the other words. -/
def atLeast2 : Prog isa :=
  .seq (.block (base .t3 4 ++ [.load .d .a3 .t3 0, .shift .srl .d .a3 .a3 1, .addi .t3 .t3 8, .addi .t5 .t0 (-1)]))
    (countLoop .t5 [.load .d .t2 .t3 0, .logic .or .a3 .a3 .t2, .addi .t3 .t3 8])

/-- `t4 := 1` if fewer than `hK` octets of `rand` are left (`rand_len −
used`, which does not wrap), else 0. -/
def tapeShort : List Instr := [ldh .t2 hRandLen, ldh .t3 hUsed, .sub .t2 .t2 .t3, ldh .t3 hK, .sltu .t4 .t2 .t3]

end VG.Impl.MillerRabin.RISCV64.Search
