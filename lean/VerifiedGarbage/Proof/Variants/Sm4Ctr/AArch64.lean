module

public import VerifiedGarbage.Proof.Sm4.AArch64.CtrFinal

/-! # The implementations of `Sm4Ctr` on AArch64 -/

@[expose] public section

namespace VG.Proof.Variants.Sm4Ctr.AArch64

def sm4 : Proof.Sm4.AArch64.CtrFinal.CtrImpl := .sm4

def scalar : Proof.Sm4.AArch64.CtrFinal.CtrImpl := .scalar

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [sm4, scalar]

end VG.Proof.Variants.Sm4Ctr.AArch64
