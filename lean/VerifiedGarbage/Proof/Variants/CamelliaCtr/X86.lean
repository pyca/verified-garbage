module

public import VerifiedGarbage.Proof.Variants.CamelliaCtr.X86.AesNi
public import VerifiedGarbage.Proof.Variants.CamelliaCtr.X86.Sse2

/-! # The implementations of `CamelliaCtr` on x86 (32-bit) -/

@[expose] public section

namespace VG.Proof.Variants.CamelliaCtr.X86

def aesni : Proof.Camellia.X86.CtrFinal.CtrImpl := Proof.Variants.CamelliaCtr.X86.AesNi.variant

def sse2 : Proof.Camellia.X86.CtrFinal.CtrImpl := Proof.Variants.CamelliaCtr.X86.Sse2.variant

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [aesni, sse2]

end VG.Proof.Variants.CamelliaCtr.X86
