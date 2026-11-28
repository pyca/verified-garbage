module

public import VerifiedGarbage.Proof.SlhDsa.AArch64.Thash4Impls
public import VerifiedGarbage.Proof.Variants.KeccakX2.AArch64

/-! # The implementations of `SlhDsaThash4` on AArch64 -/

@[expose] public section

namespace VG.Proof.Variants.SlhDsaThash4.AArch64

open VG.Proof.SlhDsa.AArch64

/-- Every implementation for outputs of 16 bytes, best first: each function
generic over them is emitted with each (the registration files that import
this), and its dispatcher tries them in this order. -/
def variants16 : List (Thash4Impl 16) :=
  [Thash4Impl.ofX2 16 (.inl rfl) Proof.Variants.KeccakX2.AArch64.sha3,
    Thash4Impl.ofX2 16 (.inl rfl) Proof.Variants.KeccakX2.AArch64.scalar]

/-- For outputs of 24 bytes, best first. -/
def variants24 : List (Thash4Impl 24) :=
  [Thash4Impl.ofX2 24 (.inr (.inl rfl)) Proof.Variants.KeccakX2.AArch64.sha3,
    Thash4Impl.ofX2 24 (.inr (.inl rfl)) Proof.Variants.KeccakX2.AArch64.scalar]

/-- For outputs of 32 bytes, best first. -/
def variants32 : List (Thash4Impl 32) :=
  [Thash4Impl.ofX2 32 (.inr (.inr rfl)) Proof.Variants.KeccakX2.AArch64.sha3,
    Thash4Impl.ofX2 32 (.inr (.inr rfl)) Proof.Variants.KeccakX2.AArch64.scalar]

end VG.Proof.Variants.SlhDsaThash4.AArch64
