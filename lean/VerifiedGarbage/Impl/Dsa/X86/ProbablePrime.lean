module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateLoad
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateSave
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateSieve
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateTest
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateFinish
public import VerifiedGarbage.Impl.Mont.X86.Compact
public import VerifiedGarbage.Impl.Dsa.HelperLayout
public import VerifiedGarbage.Spec.Dsa

/-! # DSA's probable-prime test on baseline i686

RSA's candidate machinery on a given candidate: the candidate's big-endian
octets are imported into the first array of a `w`-word Montgomery workspace
(`w` at least four), sieved by the first `trialPrimes` primes, and tested
by the blinded Miller–Rabin loop with witnesses cut to the candidate's
width, read from the start of the tape. The workspace's header and arrays
precede the candidate, which the test never changes.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86.ProbablePrime
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Bignum.X86.PublicContext
open VG.Impl.RsaKeyGen.X86

/-- The candidate's width in 64-bit words. -/
def width (bits : Nat) : Nat := max 4 ((bits + 63) / 64)

/-- The bytes of the header and the arrays; the candidate follows them. -/
def scratchBytes (w : Nat) : Nat := slot w 28

def layout (bits : Nat) : Impl.Dsa.ProbablePrime.Layout where
  bits := bits
  candidate := scratchBytes (width bits)
  scratch := [(0, scratchBytes (width bits))]
  size := scratchBytes (width bits) + bits / 8

/-- Argument `i` into header byte `d`. -/
def copy (i d : Nat) : List Instr := [.mov .eax (.mem (Compact.arg i)), .store (sc d) .eax]

/-- Keep the working space in EDI, and the tape, its length, the capacity of
the working space in 64-bit words and the `used` pointer where the candidate
code keeps them; no octet is read yet. -/
def enter : List Instr :=
  [.mov .edi (.mem (Compact.arg 0))] ++ copy 2 28 ++ copy 3 32 ++ copy 1 40 ++ copy 4 44 ++
    [.mov .eax (.imm 0), .store (sc 152) .eax]

/-- The candidate's `k` native words into array 0, zero above them, and the
candidate minus one into array 5. -/
def load (k w : Nat) : Prog isa :=
  .seq (.block [.mov .esi (.reg .edi), .alu .add .esi (.imm (BitVec.ofNat 32 (scratchBytes w)))])
    (.seq (Import.load k (slot w 0))
      (.seq (.block (WitnessLoad.zeroTail k w (slot w 0))) (CandidateSave.save (2 * w) (slot w 0) (slot w 5))))

/-- The loop's result: 1 for a probable prime, 0 if the tape ran out, 3 for
a composite, returned as 2. -/
def finish : Prog isa :=
  .seq (.block [.mov .eax (.mem (sc 168)), .alu .cmp .eax (.imm 1)])
    (.ite .e (CandidateFinish.used 1)
      (.seq (.block [.alu .cmp .eax (.imm 0)]) (.ite .e CandidateFinish.none (CandidateFinish.used 2))))

def test (bits : Nat) (montName : String) (montCode : Prog isa) (roundName : String) (roundCode : Prog isa) :
    Prog isa :=
  .seq (CandidateTest.codeWith (bits - 1) (Spec.Dsa.primeChecks bits) (8 * ((bits + 63) / 64)) (bits / 32)
    (width bits) montName montCode roundName roundCode) finish

def sieved (bits : Nat) (montName : String) (montCode : Prog isa) (roundName : String) (roundCode : Prog isa) :
    Prog isa :=
  .seq (CandidateSieve.code (width bits)) (.seq (.block [.alu .cmp .eax (.imm 0)])
    (.ite .ne (CandidateFinish.used 2) (test bits montName montCode roundName roundCode)))

def body (bits : Nat) (montName : String) (montCode : Prog isa) (roundName : String) (roundCode : Prog isa) :
    Prog isa :=
  .seq (.block enter) (.seq (load (bits / 32) (width bits))
    (sieved bits montName montCode roundName roundCode))

def code (bits : Nat) (montName : String) (montCode : Prog isa) (roundName : String) (roundCode : Prog isa) :
    Prog isa :=
  .frame (.push [.ebx, .ebp, .esi, .edi])
    (.seq (body bits montName montCode roundName roundCode) (.block Compact.restoreRegs)) (.pop .ebx 4)

end VG.Impl.Dsa.X86.ProbablePrime
