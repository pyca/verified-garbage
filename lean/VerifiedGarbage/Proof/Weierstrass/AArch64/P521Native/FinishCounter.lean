module

-- separate module: literal counter aliases connect the reused nonfinal loop to the separately checked final-window sequence

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowCounter
public import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.Code
import VerifiedGarbage.Proof.Framework.Lit

/-! Final digit zero uses the same five doublings and public packed counter
as every preceding window; the low word becomes exactly zero. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Ed25519.AArch64
open VG.Impl.Weierstrass.AArch64.P521Native

theorem finish_counter_sources :
    outerBlock144=outerBlock137 ∧ outerBlock145=outerBlock138 ∧
    outerBlock146=outerBlock139 ∧ outerBlock147=outerBlock140 ∧ outerBlock148=outerBlock141 := by lit_decide

theorem finish_counter_enter (s : State) :
    WP isa (.block outerBlock144) s fun t =>
      t.gpr .x19=s.gpr .x19-1#64+8589934592#64 ∧
      t.gpr .x2=8589934592#64 ∧ Keeps [.x19,.x2] s t ∧ t.v=s.v := by
  rw [finish_counter_sources.1]
  exact window_counter_enter s

theorem finish_counter_pair (s : State) :
    WP isa (.block outerBlock147) s fun t =>
      t.gpr .x19=s.gpr .x19-4294967296#64 ∧
      t.gpr .x2=(s.gpr .x19-4294967296#64)>>>32 ∧
      Keeps [.x19,.x2] s t ∧ t.v=s.v := by
  rw [finish_counter_sources.2.2.2.1]
  exact window_counter_pair s

theorem finish_counter_zero : 1#64-1#64+8589934592#64=windowPacked 0 2 :=
  window_counter_enter_value 0

/-- The final pair loop is literally the already-used public double-pair loop. -/
theorem finish_doubling_loop_source : loop25=loop24 := by
  simp only [loop25,loop24,finish_counter_sources.2.1,finish_counter_sources.2.2.1,
    finish_counter_sources.2.2.2.1]

end VG.Proof.Weierstrass.AArch64.P521Native
