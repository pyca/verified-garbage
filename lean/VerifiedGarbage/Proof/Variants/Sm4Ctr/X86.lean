module

public import VerifiedGarbage.Proof.Sm4.X86.Scrub

/-! # The implementations of `Sm4Ctr` on x86 (32-bit) -/

@[expose] public section

namespace VG.Proof.Variants.Sm4Ctr.X86

def scalar : Proof.Sm4.X86.CtrFinal.CtrImpl := .scalar

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [scalar]

end VG.Proof.Variants.Sm4Ctr.X86
