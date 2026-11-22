module

public import VerifiedGarbage.Proof.Camellia.X86.Scrub

/-! # The implementations of `CamelliaCtr` on x86 (32-bit) -/

@[expose] public section

namespace VG.Proof.Variants.CamelliaCtr.X86

def scalar : Proof.Camellia.X86.CtrFinal.CtrImpl := .scalar

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [scalar]

end VG.Proof.Variants.CamelliaCtr.X86
