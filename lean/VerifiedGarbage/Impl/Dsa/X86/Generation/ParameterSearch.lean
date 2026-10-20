module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.QBuild
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PAttempt
public import VerifiedGarbage.Impl.Dsa.X86.Generation.GeneratorSearch

/-! # Seed search with independent h candidates and a continuously threaded witness tape -/
@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Pbkdf2.Stream.X86

def qPhase (H : Hash) (qlen : Nat) : Prog isa :=
  .seq (qBuild H qlen)
    (.seq (.block (candidatePointer VG.Impl.Dsa.Generation.Layout.q)) (checkPrime qlen))

/-- `finish` packs and checks the accepted domain, setting frame status 1 or 3. -/
def parameterBody (H : Hash) (plen qlen : Nat) (finish : Prog isa) : Prog isa :=
  .seq (qPhase H qlen)
    (onSuccess (.seq (nativePSearch H plen qlen)
      (onSuccess (.seq (nativeGenerator plen) (onSuccess finish)))))

def parameterSearch (H : Hash) (plen qlen : Nat) (finish : Prog isa) : Prog isa :=
  tapeLoop seedTape qlen (parameterBody H plen qlen finish)
end VG.Impl.Dsa.X86.Generation
