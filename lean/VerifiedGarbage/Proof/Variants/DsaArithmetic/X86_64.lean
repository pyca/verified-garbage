module

public import VerifiedGarbage.Proof.Variants.DsaArithmetic.X86_64.Adx
public import VerifiedGarbage.Proof.Variants.DsaArithmetic.X86_64.Base

/-! # The implementations of `DsaArithmetic` on x86-64 -/

@[expose] public section

namespace VG.Proof.Variants.DsaArithmetic.X86_64

def adx : Proof.Dsa.X86_64.Slots.SlotBackend := Proof.Variants.DsaArithmetic.X86_64.Adx.slotVariant

def base : Proof.Dsa.X86_64.Slots.SlotBackend := Proof.Variants.DsaArithmetic.X86_64.Base.slotVariant

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [adx, base]

end VG.Proof.Variants.DsaArithmetic.X86_64
