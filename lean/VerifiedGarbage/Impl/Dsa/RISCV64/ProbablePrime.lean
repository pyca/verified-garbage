module

public import VerifiedGarbage.Impl.MillerRabin.RISCV64.Blinded
public import VerifiedGarbage.Impl.RsaKeyGen.RISCV64.Trial
public import VerifiedGarbage.Impl.RsaKeyGen.RISCV64.Candidate
public import VerifiedGarbage.Impl.Dsa.HelperLayout

/-!
# DSA's probable-prime test on RISC-V

`vg_dsa_probable_prime_{bits}(ws = a0, ws_len = a1, rand = a2, rand_len = a3,
used = a4)`, for `bits` in 160, 256, 1024, 2048 and 3072, as on PPC64LE
(`Impl/Dsa/PPC64LE/ProbablePrime.lean`). The candidate is the `bits / 8`
big-endian bytes at byte 0 of `ws`. From byte `saveOff`, `ws` holds our
caller's `s0`–`s11`, return address and `used`; from byte `keyOff`, the
Montgomery working space of RSA's functions (a header of 32 words, then
arrays of `w + 2` words, `Proof.Rsa.Mont.Layout`), as the shared
Miller–Rabin round takes it (28 arrays), with the prime search's state in
its header (`Impl/MillerRabin/RISCV64/Search.lean`), at `s6`. Those are the
only bytes of `ws` the test changes.

1. The registers saved; the round's registers (`s6` the working space, `a7`
   array 0, `t0` `w`, `s5` the arrays' size) and the header's words: its
   length in words, `w`, the arrays' size and the addresses of arrays 0–7,
   the tape, the octets read (0), and the search's parameters, which are the
   only way the rest of the code depends on `bits`: the octets of a witness
   (`D = 8 ⌈bits / 64⌉`, `hK`), the mask cutting its top word to `bits` bits
   (`hTop`), the uniform witnesses needed (`primeChecks bits`, `hChecks`)
   and the table's entries for trial division (RSA's: 512 through 1024
   bits, 1024 above), in the word `Candidate.hTrial` RSA's trial division
   reads it from.
2. The candidate `c` into array 0.
3. Trial division (`Impl/RsaKeyGen/RISCV64/Trial.lean`): 2 if a prime
   divides `c`.
4. Otherwise the offset of a witness's top word (`hTopOff`, the word trial
   division read its count from), Montgomery arithmetic modulo `c` and
   Miller–Rabin's exponent (`Search.montPrep`), and the blinded Miller–Rabin
   loop (`Impl/MillerRabin/RISCV64/Blinded.lean`): 0, 1 or 2.
5. The status into `a0`, the registers back (`ws` is `s6 − keyOff`), and
   `used := ` the octets read, unless the tape ran out.
-/

@[expose] public section

namespace VG.Impl.Dsa.RISCV64.ProbablePrime

open VG VG.RISCV64 VG.Impl.Bignum
open VG.Impl.MillerRabin.RISCV64.Search
open VG.Impl.MillerRabin.RISCV64.Blinded (hTopOff)
open VG.Impl.RsaKeyGen.RISCV64.Candidate (hTrial)

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
def keyOff : Nat := 512

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

/-! ## Entry and exit -/

/-- Our caller's `s0`–`s11`, return address and `used`, and their offsets
in `ws`. -/
def savedSlots : List (Reg × Nat) :=
  [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11, .ra, .a4].zipIdx.map
    fun (r, i) => (r, saveOff + 8 * i)

/-- The registers into `ws` (`a0`) from `saveOff`. -/
def save : List Instr := savedSlots.map fun (r, d) => .store .d r .a0 d

/-- The registers and `used` back, from `ws` in `t3`. -/
def restore : List Instr := savedSlots.map fun (r, d) => .load .d r .t3 d

/-- The round's registers and the header's values: its length in words, the
octets read (0), the uniform witnesses needed, the table's entries, the
octets of a witness and the mask of its top word (`2^b − 1`). -/
def values (bits : Nat) : List Instr :=
  [.addi .s6 .a0 keyOff, .addi .a7 .s6 hdrBytes, .li .t0 (words bits), .li .s5 ((8 * (words bits + 2) : Nat) : Int),
    .li .t1 (keyWords bits), .li .t2 0, .li .t3 (checks bits), .li .t4 (count bits), .li .t5 (draw bits),
    .li .t6 0, .addi .t6 .t6 (-1), .shift .srl .d .t6 .t6 (64 - topBits bits)]

/-- The header's words and the registers that hold them. -/
def hdrSlots : List (Reg × Nat) :=
  [(.t1, 8 * hWsLen), (.t0, 8 * hW), (.t4, 8 * hTrial), (.a2, 8 * hRand), (.a3, 8 * hRandLen),
    (.t2, 8 * hUsed), (.t3, 8 * hChecks), (.t6, 8 * hTop), (.t5, 8 * hK), (.s5, 8 * hStride)]

/-- The addresses of arrays 0–7 into header words 8–15, as RSA's candidate
writes them. -/
def arrs : List Instr :=
  (List.range 8).flatMap (fun j => Bignum.RISCV64.PublicChecked.base .t2 j ++ [sth .t2 (8 + j)])

/-- The registers saved, the round's registers and the header. -/
def setup (bits : Nat) : List Instr :=
  save ++ values bits ++ hdrSlots.map (fun (r, d) => .store .d r .s6 d) ++ arrs

/-- The candidate's bytes (at `ws`) into array 0. -/
def loadC (bits : Nat) : Prog isa :=
  .seq (.block [.addi .s7 .a0 0, .li .s8 (len bits)]) Bignum.RISCV64.Precompute.loadN

/-- The status into `a0`, `hUsed` into `t2`, the registers back (`ws` is
`s6 − keyOff`), and `used := hUsed` unless the status is 0. -/
def exit : Prog isa :=
  .seq (.block ([ldh .a0 hStat, ldh .t2 hUsed, .addi .t3 .s6 (-(keyOff : Int))] ++ restore))
    (.ite (.zero .a0) (.block []) (.block [.store .d .t2 .a4 0]))

/-- Trial division, then 2 if a prime divides `c`, else the offset of a
witness's top word and the Miller–Rabin tests. -/
def body (bits : Nat) (name : String) (roundCode : Prog isa) : Prog isa :=
  .seq (RsaKeyGen.RISCV64.Trial.trial hTrial)
    (.ite (.zero .a4)
      (.seq (.block [.li .t2 (topOff bits), sth .t2 hTopOff])
        (.seq montPrep (MillerRabin.RISCV64.Blinded.millerRabin name roundCode)))
      (.block [.li .t2 2, sth .t2 hStat]))

/-- `vg_dsa_probable_prime_{bits}`, calling the round `name`. -/
def code (bits : Nat) (name : String) (roundCode : Prog isa) : Prog isa :=
  .seq (.block (setup bits)) (.seq (loadC bits) (.seq (body bits name roundCode) exit))

end VG.Impl.Dsa.RISCV64.ProbablePrime
