module

public import VerifiedGarbage.Impl.MillerRabin.PPC64LE.Blinded
public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Trial
public import VerifiedGarbage.Spec.Dsa.ProbablePrime

/-!
# DSA's probable-prime test on PPC64LE

`vg_dsa_probable_prime_{bits}(ws = r3, ws_len = r4, rand = r5, rand_len = r6,
used = r7)`, for `bits` in 160, 256, 1024, 2048 and 3072. The candidate is
the `bits / 8` big-endian bytes at byte 0 of `ws`. From byte `saveOff`,
`ws` holds our caller's `r14`–`r31` and return address; from byte `keyOff`,
the Montgomery working space of RSA's functions (a header of 32 words, then
arrays of `w + 2` words, `Spec.Rsa.Mont.Layout`), as the shared
Miller–Rabin round takes it (`Spec.MillerRabin.compact`, whose arrays reach
27), with the prime search's state in its header (`Impl/MillerRabin/PPC64LE/
Search.lean`). Those are the only bytes of `ws` the test changes.

1. The registers saved; the working space's header: its length in words,
   `w` (the candidate's words, at least 4), the arrays' size and addresses,
   the tape, the octets read (0), and the search's parameters, which are
   the only way the rest of the code depends on `bits`: the octets of a
   witness (`D = 8 ⌈bits / 64⌉`, `hK`), the mask cutting its top word to
   `bits` bits and that word's offset (`hTop`, `hTopOff`), the uniform
   witnesses needed (`primeChecks bits`, `hChecks`) and the table's entries
   for trial division (RSA's: 512 through 1024 bits, 1024 above, `hCnt`).
2. The candidate `c` into array 0.
3. Trial division (`Impl/RsaKeyGen/PPC64LE/Trial.lean`): 2 if a prime
   divides `c`.
4. Montgomery arithmetic modulo `c` and Miller–Rabin's exponent
   (`Search.montPrep`), and the blinded Miller–Rabin loop
   (`Impl/MillerRabin/PPC64LE/Blinded.lean`): 0, 1 or 2.
5. `used := ` the octets read, unless the tape ran out; the registers back.
-/

@[expose] public section

namespace VG.Impl.Dsa.PPC64LE.ProbablePrime

open VG VG.PPC64LE VG.Impl.Bignum
open VG.Impl.MillerRabin.PPC64LE.Search
open VG.Impl.MillerRabin.PPC64LE.Blinded (hUni hTopOff)

/-! ## Widths -/

/-- The bytes of the candidate. -/
def len (bits : Nat) : Nat := bits / 8

/-- The 64-bit words of the arithmetic: the candidate's, at least 4 (the
round's least width). -/
def words (bits : Nat) : Nat := max 4 ((bits + 63) / 64)

/-- The octets a witness draws: whole 64-bit words, as many as the candidate
has (`Spec.RsaKeyGen.witnessBytes`). -/
def draw (bits : Nat) : Nat := 8 * ((bits + 63) / 64)

/-- The uniform witnesses needed: DSA's `primeChecks`. -/
def checks (bits : Nat) : Nat := if bits ≤ 2048 then 64 else 128

/-- The table's entries trial division takes: RSA's `trialPrimes`. -/
def count (bits : Nat) : Nat := if bits ≤ 1024 then 512 else 1024

/-- The byte offset of a witness's top word, and the bits of that word
below `bits`. -/
def topOff (bits : Nat) : Nat := 8 * ((bits - 1) / 64)
def topBits (bits : Nat) : Nat := bits - 64 * ((bits - 1) / 64)

/-- The saved registers' byte offset in `ws`, above every candidate. -/
def saveOff : Nat := 384

/-- The working space's byte offset in `ws`, above the saved registers. -/
def keyOff : Nat := 544

/-- The working space's 64-bit words: the header's 32 words and the round's
28 arrays of `w + 2` words. -/
def keyWords (bits : Nat) : Nat := 32 + 28 * (words bits + 2)

/-- The candidate at byte 0 of `ws`, and the saved registers and the
working space the only bytes the test changes. -/
def layout (bits : Nat) : Spec.Dsa.ProbablePrime.Layout where
  bits := bits
  candidate := 0
  scratch := [(saveOff, keyOff - saveOff + 8 * keyWords bits)]
  size := keyOff + 8 * keyWords bits

/-! ## Header words -/

/-- `ws`, `used` and the table's entries: header words the search leaves to
its caller. -/
def hWs : Nat := 2
def hUsedP : Nat := 3
def hCnt : Nat := 5

/-! ## Entry and exit -/

/-- `mr d, n` (`or d, n, n`). -/
def mov (d n : Reg) : Instr := .logic .or d n n

/-- Our caller's registers, saved after the return address. -/
def saved (i : Nat) : Reg :=
  [.r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30,
    .r31].getD i .r14

/-- The return address and the registers into `ws` (`r3`) from `saveOff`. -/
def save : List Instr :=
  [.mflr .r0, .store .d .r0 .r3 saveOff] ++
    (List.range 18).flatMap fun i => [.store .d (saved i) .r3 (saveOff + 8 + 8 * i)]

/-- The return address and the registers back, from `ws` in `r9`. -/
def restore : List Instr :=
  [.load .d .r0 .r9 saveOff, .mtlr .r0] ++
    (List.range 18).flatMap fun i => [.load .d (saved i) .r9 (saveOff + 8 + 8 * i)]

/-- `r8 := 2^b − 1`. -/
def maskBits (b : Nat) : List Instr := [.li .r8 0, .subi .r8 .r8 1, .lsr .d .r8 .r8 (64 - b)]

/-- The working space at `r31`, its header, `r10`, `r11` and `r29`. -/
def setup (bits : Nat) : List Instr :=
  let w := words bits
  let S := 8 * (w + 2)
  [.addi .r31 .r3 keyOff, .li .r0 (keyWords bits), sth .r0 hWsLen, sth .r3 hWs, sth .r7 hUsedP,
    sth .r5 hRand, sth .r6 hRandLen, .li .r0 0, sth .r0 hUsed, .li .r0 w, sth .r0 hW, .li .r29 S,
    sth .r29 hStride] ++
    (List.range 8).flatMap (fun j => [.addi .r0 .r31 (hdrBytes + j * S), sth .r0 (8 + j)]) ++
    [.li .r0 (draw bits), sth .r0 hK] ++ maskBits (topBits bits) ++
    [sth .r8 hTop, .li .r0 (topOff bits), sth .r0 hTopOff, .li .r0 (checks bits), sth .r0 hChecks,
      .li .r0 (count bits), sth .r0 hCnt, .addi .r10 .r31 hdrBytes, .li .r11 (2 * w)]

/-- The candidate's bytes (at `ws`) into array 0. -/
def loadC (bits : Nat) : Prog isa :=
  .seq (.block [.addi .r12 .r3 0, .li .r6 (len bits)]) Bignum.PPC64LE.Precompute.loadN

/-- `used := hUsed` unless `hStat` is 0, the status into `r3`, and the
registers back. -/
def exit : Prog isa :=
  .seq (.block [ldh .r3 hStat])
    (.seq (.ite (.zero .d .r3) (.block []) (.block [ldh .r4 hUsedP, ldh .r5 hUsed, .store .d .r5 .r4 0]))
      (.block (ldh .r9 hWs :: restore)))

/-- Trial division, then 2 if a prime divides `c`, else the Miller–Rabin
tests. -/
def body (name : String) (roundCode : Prog isa) : Prog isa :=
  .seq (RsaKeyGen.PPC64LE.Trial.trial hCnt)
    (.ite (.zero .d .r22) (.seq montPrep (MillerRabin.PPC64LE.Blinded.millerRabin name roundCode))
      (.block [.li .r3 2, sth .r3 hStat]))

/-- `vg_dsa_probable_prime_{bits}`, calling the round `name`. -/
def code (bits : Nat) (name : String) (roundCode : Prog isa) : Prog isa :=
  .seq (.block (save ++ setup bits)) (.seq (loadC bits) (.seq (body name roundCode) exit))

end VG.Impl.Dsa.PPC64LE.ProbablePrime
