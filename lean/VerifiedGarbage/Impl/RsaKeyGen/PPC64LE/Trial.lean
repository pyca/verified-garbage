module

public import VerifiedGarbage.Impl.MillerRabin.PPC64LE.Search
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32

/-!
# Trial division by the shared table of small primes on PPC64LE

RSA's trial division (`Spec.RsaKeyGen.obviouslyComposite`) of the candidate
in array 0 of the Montgomery working space (`w` words at `r10`, `2 w` in
`r11`), by the first `n` entries of the table `VG_RSA_KEYGEN_TRIAL32`
(`Impl/RsaKeyGen/TrialTable32.lean`: each entry a prime `s` in its low half
and `−s⁻¹ mod 2³²` in its high half), as x86's (`Impl/RsaKeyGen/X86/Trial.lean`):

* `digits`: the candidate's `w` words of 64 bits, least significant
  first, each reduced into the accumulator `acc` by Montgomery's reduction
  by `2⁶⁴`: `X = acc + x`, `q = X (−s⁻¹) mod 2⁶⁴` and `acc := (X + q s) /
  2⁶⁴`, which keeps `acc < 2 s` and `acc 2^(64 j) ≡` the first `j` words
  `(mod s)` (`Proof/RsaKeyGen/Trial64.lean`). `X` may carry out of 64 bits:
  its carry `c` and the carry of `X mod 2⁶⁴` plus the low word of `q s`
  (which sum to a multiple of `2⁶⁴`) are added to the high word of `q s`
  (below `s`) through CA. `−s⁻¹ mod 2⁶⁴` is the table's `y = −s⁻¹ mod 2³²`
  after a step of Newton's iteration, `y (2 + s y)`.
* `entry`: one prime, its flag of `acc ∈ {0, s}` (`s` divides the candidate)
  in `r22`.
* `trial`: the entries from `r23`, `r24` of them, until one divides: `r24`
  is cleared on a hit, so the loop stops at the first divisor. The table's
  address is `adrSym`'s, which writes the link register.

The candidate is public: the loop branches on it.
-/

@[expose] public section

namespace VG.Impl.RsaKeyGen.PPC64LE.Trial

open VG VG.PPC64LE
open VG.Impl.Bignum.PPC64LE (countLoop)

/-- One word at `r5` into `acc` (`r3`), with `s` in `r8` and `−s⁻¹ mod 2⁶⁴`
in `r9`; `r5` advanced. It writes `r0`, `r3`, `r5`, `r6` and `r7`. -/
def digit : List Instr :=
  [.load .d .r0 .r5 0, .addc .r0 .r0 .r3, .mul .r6 .r0 .r9, .mul .r7 .r6 .r8, .mulhu .r6 .r6 .r8,
    .addze .r6 .r6, .addc .r7 .r7 .r0, .addze .r3 .r6, .addi .r5 .r5 8]

/-- The entry at `r23` into `s` (`r8`) and `−s⁻¹ mod 2⁶⁴` (`r9`, from the
entry's `−s⁻¹ mod 2³²`), `acc := 0`, and the words' address and count. -/
def load : List Instr :=
  [.load .d .r8 .r23 0, .lsr .d .r9 .r8 32, .lsl .r8 .r8 32, .lsr .d .r8 .r8 32, .mul .r6 .r8 .r9,
    .addi .r6 .r6 2, .mul .r9 .r6 .r9, .li .r3 0, .addi .r5 .r10 0, .lsr .d .r4 .r11 1]

/-- `r22 :=` 1 if `acc` is 0 or `s`, else 0; on to the next entry, `r24`
counted down, and cleared on a hit. -/
def finish : List Instr :=
  [.subi .r6 .r3 1, .lsr .d .r6 .r6 63, .logic .xor .r7 .r3 .r8, .subi .r7 .r7 1, .lsr .d .r7 .r7 63,
    .logic .or .r22 .r6 .r7, .addi .r23 .r23 8, .subi .r24 .r24 1, .subi .r6 .r22 1, .logic .and .r24 .r24 .r6]

/-- One entry: `r22 :=` its flag of dividing array 0. -/
def entry : Prog isa := .seq (.block load) (.seq (countLoop .r4 digit) (.block finish))

/-- The first `r24` entries (at least 1) from `r23`, until one divides
array 0: `r22 :=` 1 if one does, else 0. -/
def loop : Prog isa := .loop entry (.nonzero .d .r24)

/-- The table's address into `r23`, `r24 := ` header word `cnt`, and the
loop. -/
def trial (cnt : Nat) : Prog isa :=
  .seq (.block [.adrSym .r23 TrialTable32.symbol, MillerRabin.PPC64LE.Search.ldh .r24 cnt]) loop

end VG.Impl.RsaKeyGen.PPC64LE.Trial
