module

public import VerifiedGarbage.Impl.Dsa.Generation.Layout
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Arguments
public import VerifiedGarbage.Impl.Dsa.HelperLayout

/-! # DSA's probable-prime test as a function of its own (AArch64)

`vg_dsa_probable_prime_{bits}` runs parameter generation's test
(`checkPrime`: trial division, then the blinded Miller–Rabin loop calling
the shared round) on the candidate at its offset of the generation's scratch
space, so that every hash backend's generator calls one copy of it. Its
working space is that scratch space: the candidate, the witness buffer and
the arithmetic workspace sit at the offsets `Generation.Layout` gives them.

The 272-byte frame holds the generation's frame words: the test reads its
arguments (the working space, the tape and `used`) from the slots where the
generation keeps them, so that the test is the generation's own code. The
test keeps every callee-saved register (it calls the round with the link
register kept in a vector register), so the frame saves none.
-/

@[expose] public section
namespace VG.Impl.Dsa.AArch64.ProbablePrime
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Impl.Dsa.AArch64.Generation
open VG.Impl.RsaKeyGen.AArch64.Candidate

/-- The candidate's bytes. -/
def len (bits : Nat) : Nat := bits / 8

/-- The 64-bit words of the arithmetic: four for q, `bits / 64` for p. -/
def words (bits : Nat) : Nat := if bits ≤ 256 then 4 else bits / 64

/-- The bytes of each witness drawn from the tape. -/
def draw (bits : Nat) : Nat := if bits = 160 then 24 else bits / 8

/-- The uniform witnesses Miller–Rabin requires. -/
def checks (bits : Nat) : Nat := if bits ≤ 2048 then 64 else 128

/-- The candidate's offset: q's or p's buffer. -/
def candidate (bits : Nat) : Nat :=
  if bits ≤ 256 then Generation.Layout.q else Generation.Layout.p

/-- The test's place in the generation's scratch space. -/
def layout (bits : Nat) : Impl.Dsa.ProbablePrime.Layout where
  bits := bits
  candidate := candidate bits
  scratch := [(Generation.Layout.witness, len bits), (Generation.Layout.arithmetic, Generation.Layout.arithmeticBytes)]
  size := Generation.Layout.domainCheck

/-- The frame slot of the pointer `used`. -/
def usedSlot : Nat := 136

/-- The arguments in the generation's frame slots (the working space, the
tape, its length and no octets read yet), `used` in a slot of its own, and
the arithmetic workspace selected. -/
def entry : List Instr :=
  [.strSp .x0 40, .strSp .x2 112, .strSp .x3 120, .strSp .x4 usedSlot, movi .x3 0, .strSp .x3 128] ++
    workspaceBase

/-- Write the octets read to `used`, and return the status, with the test's
3 for a composite as 2. -/
def exit : List Instr :=
  [ldh .x3 kUsed, .ldrSp .x4 usedSlot, .str .x .x3 .x4 0, ldh .x0 kStat, .lsr .x .x3 .x0 1,
   .sub .x .x0 .x0 .x3]

def test (bits : Nat) (mul : Nat → Nat → Nat → Prog isa) (roundCode : List (Prog isa)) : Prog isa :=
  checkPrime mul roundCode (words bits) (candidate bits) (len bits) (draw bits) (checks bits)

def code (bits : Nat) (mul : Nat → Nat → Nat → Prog isa) (roundCode : List (Prog isa)) : Prog isa :=
  .frame (.alloc 272) (seqs [.block entry, test bits mul roundCode, .block exit]) (.free 272)

end VG.Impl.Dsa.AArch64.ProbablePrime
