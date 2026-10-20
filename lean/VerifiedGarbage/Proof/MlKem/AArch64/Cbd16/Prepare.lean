module

public import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Lanes
public import VerifiedGarbage.Impl.MlKem.AArch64.Cbd16
meta import VerifiedGarbage.Proof.Rc4.AArch64.Vec
public import VerifiedGarbage.Proof.Framework.Semantics

/-! # The CBD2 byte arithmetic instruction block -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Cbd16
open VG VG.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.Rc4.AArch64
open VG.Impl.MlKem.AArch64.Cbd16 (prepare)

theorem prepare_ok (s : State)
    (h18 : s.v .v18 = broadcast 0x55) (h19 : s.v .v19 = broadcast 0x33)
    (h20 : s.v .v20 = broadcast 0x22) (h21 : s.v .v21 = broadcast 15) :
    WP isa (.block prepare) s fun t =>
      t.v .v2 = diffBytes (s.v .v0) &&& broadcast 15 ∧
      t.v .v3 = shiftBytes 4 (diffBytes (s.v .v0)) ∧
      t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      (∀ r, r ≠ .v0 → r ≠ .v1 → r ≠ .v2 → r ≠ .v3 → t.v r = s.v r) := by
  unfold prepare
  rrun [h18,h19,h20,h21,VShiftOp.eval,shiftBytes,diffBytes,sumBytes,RegUpd.sp_setV]
  refine ⟨by rfl, by rfl, ?_⟩
  intro r h0 h1 h2 h3
  simp only [h0,h1,h2,h3,ite_false]

end VG.Proof.MlKem.AArch64.Cbd16
