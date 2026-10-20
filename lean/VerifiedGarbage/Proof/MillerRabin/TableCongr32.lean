module

public import VerifiedGarbage.Proof.MillerRabin.Word32

/-! # A window run reads only the sixteen represented table powers -/

@[expose] public section
namespace VG.Proof.MillerRabin.Word32

theorem mwin_table_congr {T U : Nat → Nat} (table : ∀ d < 16, T d = U d)
    (c w M d : Nat) (digit : d < 16) (s : Nat × Bool) : mwin c w M T d s = mwin c w M U d s := by
  unfold mwin
  rw [table d digit, table 0 (by decide)]

theorem mrun_table_congr {T U : Nat → Nat} (table : ∀ d < 16, T d = U d)
    (c w M E W j : Nat) : mrun c w M T E W j = mrun c w M U E W j := by
  induction j with
  | zero => rw [mrun, mrun, table 0 (by decide)]
  | succ j ih =>
    rw [mrun, mrun, ih]
    exact mwin_table_congr table c w M _ (Nat.mod_lt _ (by decide)) _

end VG.Proof.MillerRabin.Word32
