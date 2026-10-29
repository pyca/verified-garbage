module

public import VerifiedGarbage.Impl.Secp256k1.GTable9

/-!
# secp256k1: the shape of the verifier's table of generator multiples

`secp256k1G9` has one table of 256 points: what `tcombWords_length` needs to count
its words in memory.
-/

@[expose] public section

namespace VG.Proof.Secp256k1

theorem secp256k1G9_length : Impl.Secp256k1.secp256k1G9.length = 1 := rfl

/-- Its one table has 256 points. -/
theorem secp256k1G9_rows : ∀ j < 1, (Impl.Secp256k1.secp256k1G9.getD j []).length = 256 := by
  intro j hj
  rw [show j = 0 by omega]
  decide +kernel

end VG.Proof.Secp256k1
