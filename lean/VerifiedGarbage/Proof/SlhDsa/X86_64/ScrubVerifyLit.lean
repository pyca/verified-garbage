module

-- separate module: the literals of verification over a stub, which only the cleanup's check evaluates

public import VerifiedGarbage.Proof.SlhDsa.X86_64.ScrubKeyGenLit
public import VerifiedGarbage.Impl.SlhDsa.X86_64.Verify
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.SlhDsa.X86_64.ScrubKeyGenLit
meta import VerifiedGarbage.Impl.SlhDsa.X86_64.Verify
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# SLH-DSA (SHAKE) on x86-64: verification over a stub, as literals

Verification of each SHAKE parameter set over the stub `KeyGen.stubFns`,
whose `thash4` is empty, as literals (`materialize_code`), which the check of
what its cleanup needs (`stubSide`) reads.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.VerifyTop

open VG.X86_64
open VG.Spec.SlhDsa
open VG.Proof.SlhDsa.X86_64.KeyGen (stubFns)

/-- The names of the stub's own functions. -/
def stubV : Impl.SlhDsa.X86_64.Verify.VFns := ⟨"fp", "xp"⟩

def stubV128s : Prog isa := Impl.SlhDsa.X86_64.Verify.verify shake_128s stubFns stubV
def stubV128f : Prog isa := Impl.SlhDsa.X86_64.Verify.verify shake_128f stubFns stubV
def stubV192s : Prog isa := Impl.SlhDsa.X86_64.Verify.verify shake_192s stubFns stubV
def stubV192f : Prog isa := Impl.SlhDsa.X86_64.Verify.verify shake_192f stubFns stubV
def stubV256s : Prog isa := Impl.SlhDsa.X86_64.Verify.verify shake_256s stubFns stubV
def stubV256f : Prog isa := Impl.SlhDsa.X86_64.Verify.verify shake_256f stubFns stubV

materialize_code stubV128s
materialize_code stubV128f
materialize_code stubV192s
materialize_code stubV192f
materialize_code stubV256s
materialize_code stubV256f

end VG.Proof.SlhDsa.X86_64.VerifyTop
