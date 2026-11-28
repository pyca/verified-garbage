module

-- separate module: the literals of key generation over a stub, which only the cleanup's check evaluates

public import VerifiedGarbage.Impl.SlhDsa.X86_64.Shake
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.SlhDsa.X86_64.Shake
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# SLH-DSA (SHAKE) on x86-64: key generation over a stub, as literals

Key generation of each SHAKE parameter set over the stub `stubFns`, whose
`thash4` is empty, as literals (`materialize_code`), which the check of
what its cleanup needs (`stubSide`) reads.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.KeyGen

open VG.X86_64
open VG.Spec.SlhDsa

/-- The functions key generation calls, with an empty `thash4`, by names of the stub's own. -/
def stubFns : Impl.SlhDsa.X86_64.Shake.Fns := ⟨"t", .block [], "w", "l", "x", "f"⟩

def stub128s : Prog isa := Impl.SlhDsa.X86_64.Shake.keyGen shake_128s stubFns
def stub128f : Prog isa := Impl.SlhDsa.X86_64.Shake.keyGen shake_128f stubFns
def stub192s : Prog isa := Impl.SlhDsa.X86_64.Shake.keyGen shake_192s stubFns
def stub192f : Prog isa := Impl.SlhDsa.X86_64.Shake.keyGen shake_192f stubFns
def stub256s : Prog isa := Impl.SlhDsa.X86_64.Shake.keyGen shake_256s stubFns
def stub256f : Prog isa := Impl.SlhDsa.X86_64.Shake.keyGen shake_256f stubFns

materialize_code stub128s
materialize_code stub128f
materialize_code stub192s
materialize_code stub192f
materialize_code stub256s
materialize_code stub256f

end VG.Proof.SlhDsa.X86_64.KeyGen
