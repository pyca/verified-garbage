module

public import VerifiedGarbage.Impl.P256.GTable9

/-!
# P-256: the shape of the verifier's table of generator multiples

`p256G9` has one table of 256 points: what `tcombWords_length` needs to count
its words in memory.
-/

@[expose] public section

namespace VG.Proof.P256

theorem p256G9_length : Impl.P256.p256G9.length = 1 := rfl

/-- Its one table has 256 points. -/
theorem p256G9_rows : ∀ j < 1, (Impl.P256.p256G9.getD j []).length = 256 := by
  intro j hj
  rw [show j = 0 by omega]
  decide +kernel

end VG.Proof.P256
