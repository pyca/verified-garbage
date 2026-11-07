module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ExpImpl

/-! # FFDH's baseline exponentiation on x86-64: `Crt.expLoop` -/

@[expose] public section

namespace VG.Proof.Variants.Ffdh.X86_64.Base

def variant : VG.Proof.Ffdh.X86_64.ExpImpl := VG.Proof.Ffdh.X86_64.ExpImpl.base

end VG.Proof.Variants.Ffdh.X86_64.Base
