module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtWorkspaceState
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulusCT
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge

/-! # A completed factor power independent of the currently selected workspace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt wordAt)

structure CrtPoweredState (base : BitVec 32) (len w M value : Nat) (mem : Mem) : Prop where
  layout : CrtLayoutState base len w mem
  positive : 1 < M
  modulus : numAt mem (State.addr base) w 0 = M
  result : numAt mem (State.addr base) w 6 = value

theorem CrtPoweredState.congr {m m' : Mem} {base : BitVec 32} {len w M value : Nat}
    (h : CrtPoweredState base len w M value m) (eq : WorkspaceEq (State.addr base) (8 * len) m m') :
    CrtPoweredState base len w M value m' := by
  have fit : arrAt w 8 ≤ 8 * len := h.layout.width ▸ h.layout.layout.2.2.1
  exact ⟨h.layout.congr eq, h.positive, (eq.number fit (by decide)).trans h.modulus,
    (eq.number fit (by decide)).trans h.result⟩

end VG.Proof.Bignum.Arm
