module

public import VerifiedGarbage.Impl.P384.GTable9

/-!
# P-384: the shape of the verifier's table of generator multiples

`p384G9` has one table of 256 points: what `tcombWords_length` needs to count
its words in memory.
-/

@[expose] public section

namespace VG.Proof.P384

theorem p384G9_length : Impl.P384.p384G9.length = 1 := rfl

/-- Its one table has 256 points. -/
theorem p384G9_rows : ∀ j < 1, (Impl.P384.p384G9.getD j []).length = 256 := by
  intro j hj
  rw [show j = 0 by omega]
  decide +kernel

end VG.Proof.P384
