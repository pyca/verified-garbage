module

public import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Backend

/-! # The implementations of `Blake2b` on AArch64 -/

@[expose] public section

namespace VG.Proof.Variants.Blake2b.AArch64

def scalar : Proof.Argon2.AArch64.HPrime.Backend := Proof.Argon2.AArch64.HPrime.scalar

/-- Every implementation, which each function generic over them is emitted
with (the registration files that import this). -/
def variants := [scalar]

end VG.Proof.Variants.Blake2b.AArch64
