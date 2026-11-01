module

public import VerifiedGarbage.Impl.MillerRabin.PPC64LE.Prep
public import VerifiedGarbage.Impl.Bignum.PPC64LE.PublicChecked

/-!
# A prime search's Miller–Rabin tests on PPC64LE

The pieces FFDH's and DSA's parameter generation and RSA's key generation
share, in RSA's Montgomery working space at `r31` (`Proof.Rsa.Mont.Layout`,
as the shared round takes it: a header of 32 words, then arrays of `w + 2`
words). The search's state is in header words that neither the layout (`w`
in word 6, `−N⁻¹` in word 7, the arrays' addresses in words 8–15, their
size in word 28) nor the round (words 1, 23, 26, 29 and 30) uses; words 2–5
and 16 are the caller's.

* `smallMod`: the candidate modulo a small number, bit-serially (the model
  has no division); `sieve ds`: `hBad` or'ed with a flag of a divisor in
  `ds` of the candidate (`oddPrimes256`, the odd primes below 256, RSA's
  table's first 53 entries, for FFDH and DSA).
* `montPrep`: the modulus's Montgomery constants (`−N⁻¹` by Newton's
  iteration, `R² mod N`, `R mod N`, `N − R mod N`) and Miller–Rabin's
  exponent (`expSetup`); `montPrepHi`, for a modulus whose top word is not
  zero, `R² mod N` by `64 + w` doublings and six Montgomery squares
  (`Precompute.r2Hi`) rather than `128 w` doublings (`Precompute.r2`).
* `millerRabin`: witnesses drawn from the tape, `hK` octets each cut by
  `hTop`, the round called for those in range, until one fails (`hStat :=
  2`), `hChecks` pass (`hStat := 1`) or the tape runs out (`hStat := 0`).

Every value is public: the code branches on the tape's contents.
-/

@[expose] public section

namespace VG.Impl.MillerRabin.PPC64LE.Search

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE
open VG.Impl.Bignum.PPC64LE.PublicChecked (base montOp)
open VG.Impl.Bignum.PPC64LE.Precompute (loadN copyWords)

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
/-- The mask of a witness's top word. -/
def hTop : Nat := 24
/-- Nonzero once the candidate is rejected. -/
def hBad : Nat := 25
/-- The octets of a witness, and the modulus's bits. -/
def hK : Nat := 27
def hMb : Nat := 31

/-- Header words of the layout. -/
def hW : Nat := 6
def hMinv : Nat := 7
def hStride : Nat := 28

/-- `r := ` header word `i`, and its store. -/
def ldh (r : Reg) (i : Nat) : Instr := .load .d r .r31 (8 * i)
def sth (r : Reg) (i : Nat) : Instr := .store .d r .r31 (8 * i)

/-! ## Comparisons -/

/-- `d := 1` if `a ≥ b`, else 0, through `r0`, for `b` below `2^63`: when
`a` is too, the top bit of `a − b` is its borrow; otherwise `a`'s top bit
is set. -/
def geFlag (d a b : Reg) : List Instr :=
  [.sub d a b, .lsr .d d d 63, .li .r0 1, .logic .xor d d .r0, .lsr .d .r0 a 63, .logic .or d d .r0]

/-! ## The sieve -/

/-- `r3 := ` array 0 mod `r4` (for `r4` in 2..2^62), bit-serially from the
top of its `w` words: `r3 := 2 r3 + b`, less `r4` if that is not negative.
It writes `r3`, `r5`–`r9` and `r14`. -/
def smallMod : Prog isa :=
  .seq (.block [.lsl .r5 .r11 2, .add .r5 .r10 .r5, .lsr .d .r6 .r11 1, .li .r3 0])
    (.loop (.seq (.block [.subi .r5 .r5 8, .load .d .r7 .r5 0, .li .r8 64])
        (.seq (countLoop .r8 [.lsr .d .r9 .r7 63, .lsl .r7 .r7 1, .add .r3 .r3 .r3, .add .r3 .r3 .r9,
            .sub .r9 .r3 .r4, .lsr .d .r14 .r9 63, .subi .r14 .r14 1, .logic .xor .r9 .r9 .r3,
            .logic .and .r9 .r9 .r14, .logic .xor .r3 .r3 .r9])
          (.block [.subi .r6 .r6 1])))
      (.nonzero .d .r6))

/-- `r22 |= ` (array 0 mod `d = 0`). -/
def trial (d : Nat) : Prog isa :=
  .seq (.block [.li .r4 d]) (.seq smallMod (.block [.subi .r3 .r3 1, .lsr .d .r3 .r3 63,
    .logic .or .r22 .r22 .r3]))

/-- `hBad |= ` the flag of a divisor in `ds` of array 0. -/
def sieve (ds : List Nat) : Prog isa :=
  .seq (.block [ldh .r22 hBad]) (ds.foldr (fun d c => .seq (trial d) c) (.block [sth .r22 hBad]))

/-- The odd primes below 256. -/
def oddPrimes256 : List Nat :=
  [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103,
    107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223,
    227, 229, 233, 239, 241, 251]

/-! ## Miller–Rabin -/

/-- `−N⁻¹ mod 2⁶⁴` into the header by Newton's iteration `x := x (2 − N x)`
from `x = N` (five steps from three correct bits), and its low half into
`r12` for `montOp`. -/
def minv64 : List Instr :=
  [.load .d .r0 .r10 0, .load .d .r12 .r10 0] ++
    (List.range 5).flatMap (fun _ => [.mul .r3 .r0 .r12, .li .r4 2, .sub .r3 .r4 .r3, .mul .r12 .r12 .r3]) ++
    [.li .r3 0, .sub .r3 .r3 .r12, sth .r3 hMinv, .lsl .r12 .r3 32, .lsr .d .r12 .r12 32]

/-- `r12 :=` the low half of `−N⁻¹`, from the header. -/
def minv32 : List Instr := [ldh .r12 hMinv, .lsl .r12 .r12 32, .lsr .d .r12 .r12 32]

/-- `r10`, `r11` and `r29` from the header, after the round. -/
def regsBack : List Instr :=
  [.addi .r10 .r31 hdrBytes, ldh .r11 hW, .lsl .r11 .r11 1, ldh .r29 hStride] ++ minv32

/-- `−N⁻¹`, `R² mod N` into array 1 (by `r2c`, with the bases of arrays 1–3
in `r5`, `r8` and `r9` and `−N⁻¹ mod 2³²` in `r12`), `R mod N` into array 6
(the product of `R² mod N` and 1, in array 7), `N − R mod N` into array 10,
`R mod N` copied into array 9, and the exponent. -/
def montPrepWith (r2c : Prog isa) : Prog isa :=
  .seq (.block (minv64 ++ base .r5 1 ++ base .r8 2 ++ base .r9 3)) (.seq r2c
    (.seq PublicChecked.one (.seq (montOp 6 1 7)
      (.seq (.block (base .r8 0 ++ base .r9 10 ++ base .r10 6)) (.seq subMod
        (.seq (.block ([.addi .r10 .r31 hdrBytes] ++ base .r15 6 ++ base .r14 9)) (.seq copyWords
          VG.Impl.MillerRabin.PPC64LE.expSetup)))))))

/-- `montPrepWith`, `R² mod N` by `128 w` doublings. -/
def montPrep : Prog isa := montPrepWith Precompute.r2

/-- `montPrepWith`, `R² mod N` by `Precompute.r2Hi`, for `N` above
`2^(64 (w − 1))`. -/
def montPrepHi : Prog isa := montPrepWith Precompute.r2Hi

/-- An accepted witness (array 4) in Montgomery form into array 5 (with
`−N⁻¹`'s low half from the header in `r12`), and the round called; its
result (a `u32`) zero-extended in `r3`, and `r10`, `r11`, `r29` and `r12`
from the header. -/
def roundCall (name : String) (roundCode : Prog isa) : Prog isa :=
  .seq (.block minv32) (.seq (montOp 5 4 1) (.seq (.block [.addi .r3 .r31 0, ldh .r4 hWsLen])
    (.seq (.call name roundCode) (.block ([.lsl .r3 .r3 32, .lsr .d .r3 .r3 32] ++ regsBack)))))

/-- An accepted witness's round; then `hStat := 2` if it failed, else the
passing witnesses counted and `hStat := 1` once there are `hChecks` of
them. -/
def round (name : String) (roundCode : Prog isa) : Prog isa :=
  .seq (roundCall name roundCode)
    (.ite (.zero .d .r3) (.block [.li .r3 2, sth .r3 hStat])
      (.block [ldh .r3 hIdx, ldh .r4 hChecks, .addi .r3 .r3 1, sth .r3 hIdx, .sub .r4 .r4 .r3, .subi .r4 .r4 1,
        .lsr .d .r4 .r4 63, .li .r5 3, .mul .r4 .r4 .r5, .li .r5 4, .sub .r4 .r5 .r4, sth .r4 hStat]))

/-- A draw: the next `hK` octets of `rand` into array 4 (`hUsed` advanced),
the top word and'ed with `hTop`; the round for `x ≥ 2` and `(x | 1) < N`
(the borrow of `subMod` of a copy of `x | 1`, in array 3 with its word `w`
zeroed, and N, into array 6), else nothing (`hStat` stays 4). -/
def draw (name : String) (roundCode : Prog isa) : Prog isa :=
  .seq (.block ([ldh .r12 hRand, ldh .r3 hUsed, .add .r12 .r12 .r3, ldh .r6 hK, .add .r3 .r3 .r6, sth .r3 hUsed] ++
      base .r10 4))
    (.seq loadN (.seq (.block ([.addi .r10 .r31 hdrBytes] ++ base .r5 4 ++ [.lsl .r6 .r11 2, .add .r5 .r5 .r6,
        .subi .r5 .r5 8, ldh .r4 hTop, .load .d .r6 .r5 0, .logic .and .r6 .r6 .r4, .store .d .r6 .r5 0] ++
        base .r5 4 ++ [.load .d .r24 .r5 0, .lsr .d .r24 .r24 1, .addi .r5 .r5 8, .lsr .d .r6 .r11 1, .subi .r6 .r6 1]))
      (.seq (countLoop .r6 [.load .d .r3 .r5 0, .logic .or .r24 .r24 .r3, .addi .r5 .r5 8])
        (.seq (.block (base .r14 3 ++ base .r15 4))
          (.seq copyWords (.seq (.block (base .r5 3 ++ [.load .d .r3 .r5 0, .li .r4 1, .logic .or .r3 .r3 .r4,
              .store .d .r3 .r5 0, .lsl .r6 .r11 2, .add .r5 .r5 .r6, .li .r0 0, .store .d .r0 .r5 0] ++ base .r8 3 ++
              base .r9 6)) (.seq subMod
            (.ite (.zero .d .r24) (.block [])
              (.ite (.zero .d .r20) (.block []) (round name roundCode))))))))))

/-- Witnesses while `hStat = 4`; 0 when fewer than `hK` octets of `rand`
are left (`rand_len − used`, which does not wrap). -/
def millerRabin (name : String) (roundCode : Prog isa) : Prog isa :=
  .seq (.block [.li .r3 0, sth .r3 hIdx, .li .r3 4, sth .r3 hStat])
    (.loop (.seq (.block ([ldh .r3 hRandLen, ldh .r4 hUsed, .sub .r3 .r3 .r4, ldh .r4 hK] ++ geFlag .r5 .r3 .r4))
        (.seq (.ite (.zero .d .r5) (.block [.li .r3 0, sth .r3 hStat]) (draw name roundCode))
          (.block [ldh .r3 hStat, .subi .r3 .r3 4])))
      (.zero .d .r3))

end VG.Impl.MillerRabin.PPC64LE.Search
