module

public import VerifiedGarbage.Proof.Scrypt.X86_64.Whole.Calls

/-! # The implementations of scryptROMix on x86-64 -/

@[expose] public section

namespace VG.Proof.Variants.ScryptRoMix.X86_64

/-- With the SSE2 BlockMix, never chosen on Zen 5 (`Whole.RMImpl.sse2`). -/
def sse2 : Proof.Scrypt.X86_64.Whole.RMImpl := Proof.Scrypt.X86_64.Whole.RMImpl.sse2

/-- With the scalar BlockMix. -/
def scalar : Proof.Scrypt.X86_64.Whole.RMImpl := Proof.Scrypt.X86_64.Whole.RMImpl.scalar

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [sse2, scalar]

end VG.Proof.Variants.ScryptRoMix.X86_64
