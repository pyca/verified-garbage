module

public import VerifiedGarbage.Impl.MillerRabin.PPC64LE.Blinded
public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Trial
public import VerifiedGarbage.Impl.Dsa.HelperLayout

/-!
# DSA's probable-prime test on PPC64LE

`vg_dsa_probable_prime_{bits}(ws = r3, ws_len = r4, rand = r5, rand_len = r6,
used = r7)`, for `bits` in 160, 256, 1024, 2048 and 3072. The candidate is
the `bits / 8` big-endian bytes at byte 0 of `ws`. From byte `saveOff`,
`ws` holds our caller's return address, `r14`–`r31`, `used` and `r2`
(which the round's loop does not track); from byte `keyOff`,
the Montgomery working space of RSA's functions (a header of 32 words, then
arrays of `w + 2` words, `Proof.Rsa.Mont.Layout`), as the shared
Miller–Rabin round takes it (`Proof.MillerRabin.Round.compact`, whose arrays reach
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
5. The registers back (`ws` is `r31 − keyOff`), and `used := ` the octets
   read, unless the tape ran out.
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
def keyOff : Nat := 552

/-- The working space's 64-bit words: the header's 32 words and the round's
28 arrays of `w + 2` words. -/
def keyWords (bits : Nat) : Nat := 32 + 28 * (words bits + 2)

/-- The candidate at byte 0 of `ws`, and the saved registers and the
working space the only bytes the test changes. -/
def layout (bits : Nat) : Impl.Dsa.ProbablePrime.Layout where
  bits := bits
  candidate := 0
  scratch := [(saveOff, keyOff - saveOff + 8 * keyWords bits)]
  size := keyOff + 8 * keyWords bits

/-! ## Header words -/

/-- The table's entries: a header word the search leaves to its caller. -/
def hCnt : Nat := 5

/-! ## Entry and exit -/

/-- `mr d, n` (`or d, n, n`). -/
def mov (d n : Reg) : Instr := .logic .or d n n

/-- The return address (in `r0`), our caller's registers, `used` and `r2`,
and their offsets in `ws`. -/
def savedSlots : List (Reg × Nat) :=
  (.r0, saveOff) :: [.r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28,
    .r29, .r30, .r31, .r7, .r2].zipIdx.map fun (r, i) => (r, saveOff + 8 + 8 * i)

/-- The return address and the registers into `ws` (`r3`) from `saveOff`. -/
def save : List Instr := .mflr .r0 :: savedSlots.map fun (r, d) => .store .d r .r3 d

/-- The registers and `used` back, from `ws` in `r9`, and the return
address. -/
def restore : List Instr :=
  [.load .d .r0 .r9 saveOff, .mtlr .r0] ++ savedSlots.tail.map fun (r, d) => .load .d r .r9 d

/-- The registers that hold the arrays' addresses `0`–`7`. -/
def arrReg (j : Nat) : Reg := [.r22, .r23, .r24, .r25, .r26, .r27, .r28, .r30].getD j .r22

/-- The header's values into registers: the working space's length, 0, `w`,
the arrays' size and addresses, the octets of a witness, the mask of its top
word (`2^b − 1`) and that word's offset, the uniform witnesses needed and the
table's entries; and the working space at `r31`, array 0 at `r10` and `2 w`
in `r11`. -/
def values (bits : Nat) : List Instr :=
  let w := words bits
  let S := 8 * (w + 2)
  [.addi .r31 .r3 keyOff, .li .r14 (keyWords bits), .li .r15 0, .li .r16 w, .li .r29 S] ++
    (List.range 8).map (fun j => .addi (arrReg j) .r31 (hdrBytes + j * S)) ++
    [.li .r17 (draw bits), .li .r18 0, .subi .r18 .r18 1, .lsr .d .r18 .r18 (64 - topBits bits),
      .li .r19 (topOff bits), .li .r20 (checks bits), .li .r21 (count bits), .addi .r10 .r31 hdrBytes,
      .li .r11 (2 * w)]

/-- The header's words and the registers that hold them. -/
def hdrSlots : List (Reg × Nat) :=
  [(.r14, 8 * hWsLen), (.r21, 8 * hCnt), (.r16, 8 * hW)] ++
    (List.range 8).map (fun j => (arrReg j, 8 * (8 + j))) ++
    [(.r19, 8 * hTopOff), (.r5, 8 * hRand), (.r6, 8 * hRandLen), (.r15, 8 * hUsed), (.r20, 8 * hChecks),
      (.r18, 8 * hTop), (.r17, 8 * hK), (.r29, 8 * hStride)]

/-- The working space at `r31`, its header, `r10`, `r11` and `r29`. -/
def setup (bits : Nat) : List Instr := values bits ++ hdrSlots.map fun (r, d) => .store .d r .r31 d

/-- The candidate's bytes (at `ws`) into array 0. -/
def loadC (bits : Nat) : Prog isa :=
  .seq (.block [.addi .r12 .r3 0, .li .r6 (len bits)]) Bignum.PPC64LE.Precompute.loadN

/-- The status into `r3`, `hUsed` into `r5`, the registers back (`ws` is
`r31 − keyOff`), and `used := hUsed` unless the status is 0. -/
def exit : Prog isa :=
  .seq (.block ([ldh .r3 hStat, ldh .r5 hUsed, .subi .r9 .r31 keyOff] ++ restore))
    (.ite (.zero .d .r3) (.block []) (.block [.store .d .r5 .r7 0]))

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
