module

public import VerifiedGarbage.Proof.Variants.FfdhExp.X86_64.Base
public import VerifiedGarbage.Proof.Variants.FfdhExp.X86_64.Ifma

/-! # The implementations of `FfdhExp` on x86-64 -/

@[expose] public section

namespace VG.Proof.Variants.FfdhExp.X86_64

def base : Proof.Ffdh.X86_64.ExpImpl := Proof.Variants.FfdhExp.X86_64.Base.variant

def ifma : Proof.Ffdh.X86_64.ExpImpl := Proof.Variants.FfdhExp.X86_64.Ifma.variant

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this). -/
def variants := [ifma, base]

end VG.Proof.Variants.FfdhExp.X86_64
