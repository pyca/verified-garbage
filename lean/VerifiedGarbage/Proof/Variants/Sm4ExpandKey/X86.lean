module

public import VerifiedGarbage.Proof.Sm4Gcm.X86.CtrCall

/-! # The implementations of `Sm4ExpandKey` on x86 (32-bit) -/

@[expose] public section

namespace VG.Proof.Variants.Sm4ExpandKey.X86

def scalar : Proof.Sm4Gcm.X86.KeyImpl := .scalar

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [scalar]

end VG.Proof.Variants.Sm4ExpandKey.X86
