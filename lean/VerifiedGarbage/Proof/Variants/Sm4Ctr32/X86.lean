module

public import VerifiedGarbage.Proof.Sm4Gcm.X86.CtrCall
public import VerifiedGarbage.Proof.Variants.Sm4ExpandKey.X86

/-! # The implementations of `Sm4Ctr32` on x86 (32-bit)

And the pairs of an implementation of the key schedule and one of them that
SM4-GCM's `init` is emitted for (`withExpandKey`). -/

@[expose] public section

namespace VG.Proof.Variants.Sm4Ctr32.X86

open VG.Proof.Sm4Gcm.X86 (KeyImpl CtrImpl)

def scalar : CtrImpl := .scalar

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [scalar]

/-- The pairs of an implementation of the key schedule and one of
`vg_sm4_ctr32` that SM4-GCM's `init` is emitted for, in the order of the
key schedule's: each with the best of `variants` that needs no CPU feature
it does not (`CtrImpl.forKey`), so that `init` has one instance for each
implementation of the key schedule, with its features and its suffix. -/
def withExpandKey : List (KeyImpl × CtrImpl) :=
  Proof.Variants.Sm4ExpandKey.X86.variants.map fun k => (k, CtrImpl.forKey variants k)

end VG.Proof.Variants.Sm4Ctr32.X86
