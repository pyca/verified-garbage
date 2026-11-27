module

public import VerifiedGarbage.Proof.Sm4.X86.Scrub
public import VerifiedGarbage.Proof.Variants.Sm4Ctr.X86.AesNi

/-! # The implementations of `Sm4Ctr` on x86 (32-bit) -/

@[expose] public section

namespace VG.Proof.Variants.Sm4Ctr.X86

def aesni : Proof.Sm4.X86.CtrFinal.CtrImpl := Proof.Variants.Sm4Ctr.X86.AesNi.variant

def scalar : Proof.Sm4.X86.CtrFinal.CtrImpl := .scalar

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [aesni, scalar]

end VG.Proof.Variants.Sm4Ctr.X86
