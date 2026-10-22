module

public import VerifiedGarbage.Impl.Ffdh.X86.Domain
public import VerifiedGarbage.Impl.Ffdh.X86.KeyGen
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Sieve

/-!
# FFDH on i686: one sieved safe-prime candidate

`vg_ffdh_parameter_candidate_sieved(out, out_len, used, bits, generator,
rand, rand_len, scratch, scratch_len)`, on the operations of
`Domain.lean` at the width `B = 8 ⌈L / 8⌉` of `L = out_len` octets. The
synthetic arguments are those of `Domain.lean` with the tape as the
domain (2: the tape, 3: `L`, 12: `rand_len`).

The tape is public under the contract, so every branch may depend on it;
none depends on the working space's or the frame's initial contents.

1. Fewer than `L` octets: zeros out, nothing used, 0 returned.
2. p from the first `L` octets, cut to `bits` bits, with its top and
   lowest bits set.
3. The generator's congruences: for 2, `p mod 8 = 3` and `3 | p − 2`; for
   5, `5 | p − 2` or `5 | p − 3`; each divisibility by RSA's whole-word
   Montgomery trial division (`Trial.divisor`).
4. `q = p >> 1`, odd, then RSA's small-prime sieve (`Sieve.loop`, 512
   primes up to 1024 bits, 1024 above) on p, then on q.
5. Miller–Rabin: one witness for p, `primeChecks (bits − 1)` for q, then
   `primeChecks bits − 1` more for p (`phase`). Each phase prepares the
   modulus's context once; each witness is drawn from the octets of
   `w − 1`, cut to its bits and drawn again until `1 < a < w − 1`, then
   tested (`round`): `z = a^d` by the fixed-window power, then the
   `s − 1` squarings of the round, without an early exit.
6. A rejection writes zeros and returns 2, a shortage zeros and 0 (and
   nothing used), an acceptance p and 1; `used` is the octets read.

The wide slots: p (9), q (10), the exponent d (11), `p − t` (12), the
witness (13), one (14), `w − 1` (15), `t` (16) and the output (19). The
header words, above the operations' own: below.
-/

@[expose] public section
namespace VG.Impl.Ffdh.X86.Candidate
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt
open VG.Impl.Bignum.X86.PublicRt (argAt)

/-- Wide slot `j`. -/
local notation:max "sl " j:max => Loc.slot Ctx.wide j
/-- A number of the wide context. -/
local notation "n1" => one Ctx.wide

/-! ## The header words -/

def bitsOff : Nat := 16
def genOff : Nat := 20
def usedOff : Nat := 24
def curOff : Nat := 28
def cntOff : Nat := 52
def twoOff : Nat := 56
def octOff : Nat := 60
def kOff : Nat := 64
def stOff : Nat := 68
def hitOff : Nat := 72
def jOff : Nat := 76
def okOff : Nat := 80

/-- `(out, out_len, used, bits, generator, rand, rand_len, scratch, scratch_len)`. -/
def args : Args := { out := some 0, dom := 5, dlen := 6, plen := 1, ws := 7 }

/-- `bits`, the generator and `used` into the header. -/
def entryWords : List Instr :=
  [.mov .eax (.mem (argAt 19 3)), .store (sc bitsOff) .eax, .mov .eax (.mem (argAt 19 4)), .store (sc genOff) .eax,
    .mov .eax (.mem (argAt 19 2)), .store (sc usedOff) .eax]

/-! ## Results -/

/-- `used` written: `eax` as its low word, zero as its high word. -/
def storeUsed : List Instr :=
  [.mov .ecx (.mem (sc usedOff)), .store (at_ .ecx 0) .eax, .mov .eax (.imm 0), .store (at_ .ecx 4) .eax]

/-- Zeros written to `out`. -/
def zeroOut : Prog isa :=
  .seq (.block [.mov .ecx (.imm 0), .store (sc accOff) .ecx]) (exportTo 0 1)

/-- A shortage: zeros, nothing used, 0. -/
def short : Prog isa := .seq zeroOut (.block ([.mov .eax (.imm 0)] ++ storeUsed ++ [.mov .eax (.imm 0)]))

/-- A rejection: zeros, the octets read so far used, 2. -/
def reject : Prog isa :=
  .seq zeroOut (.block ([.mov .eax (.mem (sc curOff))] ++ storeUsed ++ [.mov .eax (.imm 2)]))

/-- An acceptance: p, the octets read so far used, 1. -/
def accept : Prog isa :=
  .seq (copy (sl 9) (sl 19) n1) <|
  .seq (.block [.mov .ecx (.imm (BitVec.allOnes 32)), .store (sc accOff) .ecx]) <|
  .seq (exportTo 0 1) (.block ([.mov .eax (.mem (sc curOff))] ++ storeUsed ++ [.mov .eax (.imm 1)]))

/-! ## Words of a number -/

/-- `eax` the lowest word of the number. -/
def lowWord (x : Loc) : List Instr := ptrTo x .eax .edx ++ [.mov .eax (.mem (at_ .eax 0))]

/-- `eax := 2^r − 1` for `r` in `ecx`, `1 ≤ r ≤ 32`, by `r` doublings plus one. -/
def maskLoop : Prog isa :=
  .seq (.block [.mov .eax (.imm 0)]) (.loop (.block [.alu .add .eax (.reg .eax), .alu .add .eax (.imm 1),
    .alu .sub .ecx (.imm 1)]) .ne)

/-- The number cut to its low `k` bits (`k` in the header), its top bit set if `top`:
the word `(k − 1) / 32` and'ed with the mask of its `(k − 1) mod 32 + 1` bits. The
words above it must be zero. -/
def cut (x : Loc) (top : Bool) : Prog isa :=
  .seq (.block [.mov .ecx (.mem (sc kOff)), .alu .sub .ecx (.imm 1), .mov .edx (.reg .ecx), .shift .shr .edx 5,
    .alu .add .edx (.reg .edx), .alu .add .edx (.reg .edx), .alu .and .ecx (.imm 31), .alu .add .ecx (.imm 1)]) <|
  .seq maskLoop <|
  .block (ptrTo x .ebx .ecx ++ [.alu .add .ebx (.reg .edx), .mov .ecx (.mem (at_ .ebx 0)), .alu .and .ecx (.reg .eax)] ++
    (if top then [.mov .ebp (.reg .eax), .shift .shr .ebp 1, .alu .xor .eax (.reg .ebp), .alu .or .ecx (.reg .eax)]
      else []) ++
    [.store (at_ .ebx 0) .ecx])

/-- The number's lowest bit set. -/
def setLow (x : Loc) : List Instr :=
  ptrTo x .ebx .edx ++ [.mov .eax (.mem (at_ .ebx 0)), .alu .or .eax (.imm 1), .store (at_ .ebx 0) .eax]

/-- One word of a halving, from the top: `[esi − 4]` shifted down a bit, the carried bit
(`ebx`, 0 or 1) as its top bit, its low bit the next carry; `ecx` bytes left. -/
def halveStep : List Instr :=
  [.alu .sub .esi (.imm 4), .mov .eax (.mem (at_ .esi 0)), .mov .edx (.reg .eax), .alu .and .edx (.imm 1),
    .shift .shr .eax 1, .shift .ror .ebx 1, .alu .or .eax (.reg .ebx), .store (at_ .esi 0) .eax,
    .mov .ebx (.reg .edx), .alu .sub .ecx (.imm 4)]

/-- The number halved in place. -/
def halve (x : Loc) : Prog isa :=
  .seq (.block (ptrTo x .esi .edx ++ cntTo n1 .ecx ++ [.alu .add .esi (.reg .ecx), .mov .ebx (.imm 0)]))
    (.loop (.block halveStep) .ne)

/-! ## Trial division -/

/-- `eax` the number's address and `ecx` its end, for a frame below. -/
def bounds (x : Loc) : List Instr :=
  ptrTo x .eax .edx ++ cntTo n1 .ecx ++ [.alu .add .ecx (.reg .eax)]

/-- `eax` one if the prime `prime` (with `inv = −prime⁻¹ mod 2³²`) divides the number, else zero,
by RSA's whole-word trial division, in a frame holding the number's end. -/
def divides (x : Loc) (prime inv : Nat) : Prog isa :=
  .seq (.block (bounds x)) <|
  .seq (.frame (.alloc 20)
    (.seq (.block [.mov .edi (.reg .eax), .store (RsaKeyGen.X86.Sieve.slot 4) .ecx,
      .mov .ebx (.imm (BitVec.ofNat 32 prime)),
      .mov .esi (.imm (BitVec.ofNat 32 inv)), .mov .ebp (.imm 0)])
      (RsaKeyGen.X86.Trial.divisor 4)) (.free 20))
    (.block restoreEdi)

/-- `eax` one if a prime of RSA's table (512 primes to 1024 bits, 1024 above) divides the
number, else zero: its sieve, in a frame of its five words (the number, its end, the table's
cursor, the primes left and the hit). -/
def sieve (x : Loc) : Prog isa :=
  .seq (.block (bounds x ++ [.mov .edx (.mem (sc bitsOff)), .alu .cmp .edx (.imm 1025), .alu .sbb .edx (.reg .edx),
    .alu .and .edx (.imm 0xFFFFFE00), .alu .add .edx (.imm 1024)])) <|
  .seq (.frame (.alloc 20)
    (.seq (.block [.store (RsaKeyGen.X86.Sieve.slot 0) .eax, .store (RsaKeyGen.X86.Sieve.slot 4) .ecx,
      .store (RsaKeyGen.X86.Sieve.slot 12) .edx])
    (.seq RsaKeyGen.X86.Sieve.tableAddress
      (.seq (.block [.store (RsaKeyGen.X86.Sieve.slot 8) .eax, .mov .eax (.imm 0),
        .store (RsaKeyGen.X86.Sieve.slot 16) .eax])
        (RsaKeyGen.X86.Sieve.loop RsaKeyGen.X86.Sieve.stackSlots)))) (.free 20))
    (.block restoreEdi)

/-- `−3⁻¹` and `−5⁻¹` modulo `2³²`. -/
def inv3 : Nat := 0x55555555
def inv5 : Nat := 0x33333333

/-- `p − t` into slot 12. -/
def minus (t : Nat) : Prog isa :=
  .seq (setSmall (sl 16) n1 t) (chain .sbb (sl 12) (sl 9) (sl 16) n1)

/-- ZF set unless `eax` is zero. -/
def testEax : Prog isa := .block [.alu .test .eax (.reg .eax)]

/-! ## The candidate's shape -/

/-- `eax` one if `p mod 8 = 3` and `3 | p − 2`, else zero. -/
def gen2 : Prog isa :=
  .seq (.block (lowWord (sl 9) ++ [.alu .and .eax (.imm 7), .alu .cmp .eax (.imm 3)])) <|
  .ite .e (.seq (minus 2) (divides (sl 12) 3 inv3)) (.block [.mov .eax (.imm 0)])

/-- `eax` one if `5 | p − 2` or `5 | p − 3`, else zero. -/
def gen5 : Prog isa :=
  .seq (minus 2) <| .seq (divides (sl 12) 5 inv5) <| .seq (.block [.store (sc okOff) .eax]) <|
  .seq (minus 3) <| .seq (divides (sl 12) 5 inv5) (.block [.alu .or .eax (.mem (sc okOff))])

/-- `eax` one if p's congruences for its generator hold, else zero. -/
def congruences : Prog isa :=
  .seq (.block [.mov .eax (.mem (sc genOff)), .alu .cmp .eax (.imm 2)]) (.ite .e gen2 gen5)

/-- p from the tape's first `L` octets, cut to `bits` bits, its top and lowest bits set. -/
def shape : Prog isa :=
  .seq (load (sl 9) n1 2 3) <|
  .seq (.block [.mov .eax (.mem (argAt 0 3)), .store (sc curOff) .eax, .mov .eax (.mem (sc bitsOff)),
    .store (sc kOff) .eax]) <|
  .seq (cut (sl 9) true) (.block (setLow (sl 9)))

/-- `q = p >> 1` into slot 10. -/
def half : Prog isa := .seq (copy (sl 9) (sl 10) n1) (halve (sl 10))

/-! ## Miller–Rabin -/

/-- The context of the modulus in slot `j`, one in slot 14, `w − 1` in 15, and `d` and `s`
(slot 11, header) with `w − 1 = 2^s d`, `d` odd. -/
def prepPhase (j : Nat) : Prog isa :=
  .seq (copy (sl j) (sl 0) n1) <| .seq (prepare .wide) <|
  .seq (setSmall (sl 14) n1 1) <| .seq (chain .sbb (sl 15) (sl j) (sl 14) n1) <|
  .seq (copy (sl 15) (sl 11) n1) <| .seq (.block [.mov .eax (.imm 0), .store (sc twoOff) .eax]) <|
  .loop (.seq (halve (sl 11)) (.block ([.mov .eax (.mem (sc twoOff)), .alu .add .eax (.imm 1), .store (sc twoOff) .eax] ++
    lowWord (sl 11) ++ [.alu .and .eax (.imm 1)]))) .e

/-- One squaring of the round: `z := z² mod w` (slot 6, through `R² mod w` in slot 4), the hit
mask or'ed with `z = w − 1`; ZF when the squarings are done. -/
def squareStep : Prog isa :=
  .seq (mul .wide 6 6 6) <| .seq (mul .wide 6 6 4) <| .seq (equal (sl 6) (sl 15) n1)
    (.block [.alu .or .ecx (.mem (sc hitOff)), .store (sc hitOff) .ecx, .mov .eax (.mem (sc jOff)),
      .alu .sub .eax (.imm 1), .store (sc jOff) .eax])

/-- One round for the witness in slot 13: `z = a^d mod w`, the hit mask `z = 1 ∨ z = w − 1`,
then the `s − 1` squarings, each or'ing `z = w − 1` in; the mask in the header. -/
def round : Prog isa :=
  .seq (copy (sl 13) (sl 5) n1) <| .seq (copy (sl 11) (sl 8) n1) <| .seq (windowPower .wide) <|
  .seq (equal (sl 6) (sl 3) n1) <| .seq (.block [.store (sc hitOff) .ecx]) <|
  .seq (equal (sl 6) (sl 15) n1) <|
  .seq (.block [.alu .or .ecx (.mem (sc hitOff)), .store (sc hitOff) .ecx, .mov .eax (.mem (sc twoOff)),
    .alu .sub .eax (.imm 1), .store (sc jOff) .eax]) <|
  .ite .e (.block []) (.loop squareStep .ne)

/-- A witness passed: one fewer to go, and the status 1 when none is left. -/
def passed : List Instr :=
  [.mov .eax (.mem (sc cntOff)), .alu .sub .eax (.imm 1), .store (sc cntOff) .eax, .alu .cmp .eax (.imm 1),
    .mov .eax (.imm 0), .alu .adc .eax (.imm 0), .store (sc stOff) .eax]

/-- The witness from its octets at the cursor into slot 13, as `load` does, and the cursor past them. -/
def drawLoad : Prog isa :=
  .seq (zero (sl 13) n1) <|
  .seq (.block (ptrTo (sl 13) .ebx .edx ++ [.mov .esi (.mem (argAt 0 2)), .alu .add .esi (.mem (sc curOff)),
    .mov .ecx (.mem (sc octOff)), .alu .add .esi (.reg .ecx), .alu .sub .esi (.imm 1)])) <|
  .seq reverseBytes (.block [.mov .eax (.mem (sc octOff)), .alu .add .eax (.mem (sc curOff)), .store (sc curOff) .eax])

/-- One draw: the status 3 if too few octets are left; else the witness drawn and cut, and if
`1 < a < w − 1` its round: the status 2 if it fails, else `passed`. ZF while the status is 0. -/
def draw : Prog isa :=
  .seq (.block [.mov .eax (.mem (argAt 0 12)), .alu .sub .eax (.mem (sc curOff)), .alu .cmp .eax (.mem (sc octOff))]) <|
  .seq (.ite .b (.block [.mov .eax (.imm 3), .store (sc stOff) .eax]) <|
    .seq drawLoad <| .seq (cut (sl 13) false) <|
    .seq (rangeMask 13) <| .seq testMask <|
    .ite .e (.block []) <|
    .seq round <| .seq (.block [.mov .ecx (.mem (sc hitOff)), .alu .test .ecx (.reg .ecx)]) <|
    .ite .e (.block [.mov .eax (.imm 2), .store (sc stOff) .eax]) (.block passed))
  (.block [.mov .eax (.mem (sc stOff)), .alu .cmp .eax (.imm 0)])

/-- A phase: the modulus in slot `j` prepared, then witnesses drawn until `cnt` pass, one
fails or the tape runs out; the status (1, 2 or 3) in `eax`. -/
def phase (j : Nat) : Prog isa :=
  .seq (prepPhase j) <| .seq (.block [.mov .eax (.imm 0), .store (sc stOff) .eax]) <|
  .seq (.loop draw .e) (.block [.mov .eax (.mem (sc stOff))])

/-- `cnt := primeChecks (bits − δ) − ε`, the octets and the bits of `w − 1` for the modulus
of `bits − δ` bits. -/
def phaseWords (δ ε : Nat) : List Instr :=
  [.mov .eax (.mem (sc bitsOff)), .alu .sub .eax (.imm (BitVec.ofNat 32 δ)), .store (sc kOff) .eax,
    .alu .add .eax (.imm 7), .shift .shr .eax 3, .store (sc octOff) .eax,
    .mov .eax (.mem (sc kOff)), .alu .cmp .eax (.imm 2049), .alu .sbb .ecx (.reg .ecx), .alu .and .ecx (.imm 0xFFFFFFC0),
    .alu .add .ecx (.imm (BitVec.ofNat 32 (128 - ε))), .store (sc cntOff) .ecx]

/-- A phase's status: on to `rest` for 1, a rejection for 2, a shortage for 3. -/
def onPass (rest : Prog isa) : Prog isa :=
  .seq (.block [.alu .cmp .eax (.imm 1)]) (.ite .e rest (.seq (.block [.alu .cmp .eax (.imm 2)]) (.ite .e reject short)))

/-- The screened tests: one witness for p, all of q's, the rest of p's. -/
def tests : Prog isa :=
  .seq (.block (phaseWords 0 0 ++ [.mov .eax (.imm 1), .store (sc cntOff) .eax])) <| .seq (phase 9) <| onPass <|
  .seq (.block (phaseWords 1 0)) <| .seq (phase 10) <| onPass <|
  .seq (.block (phaseWords 0 1)) <| .seq (phase 9) (onPass accept)

/-- p's checks and tests. -/
def main : Prog isa :=
  .seq shape <| .seq congruences <| .seq testEax <| .ite .e reject <|
  .seq half <| .seq (.block (lowWord (sl 10) ++ [.alu .and .eax (.imm 1)])) <| .ite .e reject <|
  .seq (sieve (sl 9)) <| .seq testEax <| .ite .ne reject <|
  .seq (sieve (sl 10)) <| .seq testEax <| .ite .ne reject tests

def body : Prog isa :=
  .seq (.block (entryWords ++ [.mov .eax (.mem (argAt 0 12)), .alu .cmp .eax (.mem (argAt 0 3))])) (.ite .b short main)

def code : Prog isa := wrap args body

end VG.Impl.Ffdh.X86.Candidate
