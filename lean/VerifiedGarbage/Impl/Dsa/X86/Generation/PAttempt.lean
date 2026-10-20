module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PHashes
public import VerifiedGarbage.Impl.Dsa.X86.Generation.CandidateArguments
public import VerifiedGarbage.Impl.Dsa.X86.Generation.CandidateWidth
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PrimeArguments
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Search

/-! # One bounded p-search attempt, followed by the persistent control handoff -/
@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Pbkdf2.Stream.X86

def pAttemptOffset : List Instr := [.mov .eax (.mem (sc 4)), .store (frameSlot 2) .eax]

def pConstruct (H : Hash) (plen qlen : Nat) : Prog isa :=
  .seq (pHashesShape H qlen ((8 * plen - 1) / (8 * qlen)) plen)
    (.seq (candidateComputeFromFrame plen qlen (plen / 8)) (candidateStores plen))

def pCandidateTest (plen : Nat) : Prog isa :=
  .seq (.block (candidatePointer VG.Impl.Dsa.Generation.Layout.p ++ [.mov .esi (.mem (frameSlot 22))] ++ candidateWidth))
    (.ite .b (.block (frameStatus 3)) (checkPrime plen))

def pAttemptReturn : List Instr :=
  controlBase ++ [.mov .eax (.mem (frameSlot 19)), .store (sc 8) .eax]

def pAttempt (H : Hash) (plen qlen : Nat) : Prog isa :=
  .seq (.block pAttemptOffset)
    (.seq (pConstruct H plen qlen) (.seq (pCandidateTest plen) (.block pAttemptReturn)))

/-- The last attempt already leaves the seed outcome in the persistent status slot. -/
def nativePSearch (H : Hash) (plen qlen : Nat) : Prog isa :=
  .seq (.block controlBase)
    (pSearch (pAttempt H plen qlen) (32 * plen) ((8 * plen - 1) / (8 * qlen) + 1))
end VG.Impl.Dsa.X86.Generation
