module

-- separate module: the literals of signing over a stub, which only the cleanup's check evaluates

public import VerifiedGarbage.Proof.SlhDsa.X86_64.ScrubKeyGenLit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.SlhDsa.X86_64.ScrubKeyGenLit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# SLH-DSA (SHAKE) on x86-64: signing over a stub, as literals

Signing of each SHAKE parameter set over the stub `KeyGen.stubFns`, whose
`thash4` is empty, as literals (`materialize_code`), which the check of
what its cleanup needs (`stubSide`) reads.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.SignTop

open VG.X86_64
open VG.Spec.SlhDsa
open VG.Proof.SlhDsa.X86_64.KeyGen (stubFns)

def stubS128s : Prog isa := Impl.SlhDsa.X86_64.Shake.sign shake_128s stubFns
def stubS128f : Prog isa := Impl.SlhDsa.X86_64.Shake.sign shake_128f stubFns
def stubS192s : Prog isa := Impl.SlhDsa.X86_64.Shake.sign shake_192s stubFns
def stubS192f : Prog isa := Impl.SlhDsa.X86_64.Shake.sign shake_192f stubFns
def stubS256s : Prog isa := Impl.SlhDsa.X86_64.Shake.sign shake_256s stubFns
def stubS256f : Prog isa := Impl.SlhDsa.X86_64.Shake.sign shake_256f stubFns

materialize_code stubS128s
materialize_code stubS128f
materialize_code stubS192s
materialize_code stubS192f
materialize_code stubS256s
materialize_code stubS256f

end VG.Proof.SlhDsa.X86_64.SignTop
