module

public import VerifiedGarbage.Proof.Sm4Gcm.X86.CtrCall
public import VerifiedGarbage.Proof.Variants.Sm4ExpandKey.X86.AesNi

/-! # The implementations of `Sm4ExpandKey` on x86 (32-bit) -/

@[expose] public section

namespace VG.Proof.Variants.Sm4ExpandKey.X86

def aesni : Proof.Sm4Gcm.X86.KeyImpl := Proof.Variants.Sm4ExpandKey.X86.AesNi.variant

def scalar : Proof.Sm4Gcm.X86.KeyImpl := .scalar

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [aesni, scalar]

end VG.Proof.Variants.Sm4ExpandKey.X86
