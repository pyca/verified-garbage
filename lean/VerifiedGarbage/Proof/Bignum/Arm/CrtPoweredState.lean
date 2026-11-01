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
  inverse : ((word mem (State.addr base) (arrAt w 0)).toNat *
    (wordAt mem (State.addr base) Proof.Rsa.Mont.minvWord).toNat + 1) % 2 ^ 64 = 0
  positive : 1 < M
  modulus : numAt mem (State.addr base) w 0 = M
  result : numAt mem (State.addr base) w 6 = value
  r2 : numAt mem (State.addr base) w 4 = 2 ^ (128 * w) % M
  one : numAt mem (State.addr base) w 7 = 1

theorem CrtPoweredState.of_ready {s : State} {base : BitVec 32} {len w M value : Nat}
    (h : ArithmeticReady base len w s) (modulus : numAt s.mem (State.addr base) w 0 = M)
    (result : numAt s.mem (State.addr base) w 6 = value)
    (r2 : numAt s.mem (State.addr base) w 4 = 2 ^ (128 * w) % M)
    (one : numAt s.mem (State.addr base) w 7 = 1) : CrtPoweredState base len w M value s.mem :=
  ⟨⟨h.layout, h.width⟩, h.inverse, modulus ▸ h.modulus, modulus, result, r2, one⟩

theorem CrtPoweredState.congr {m m' : Mem} {base : BitVec 32} {len w M value : Nat}
    (h : CrtPoweredState base len w M value m) (eq : WorkspaceEq (State.addr base) (8 * len) m m') :
    CrtPoweredState base len w M value m' := by
  have fit : arrAt w 8 ≤ 8 * len := h.layout.width ▸ h.layout.layout.2.2.1
  have fit0 := Nat.le_trans (array_end_le (w := w) (by decide : 0 < 8)) fit
  have size := h.layout.size
  refine ⟨h.layout.congr eq, ?_, h.positive,
    (eq.number fit (by decide)).trans h.modulus, (eq.number fit (by decide)).trans h.result,
    (eq.number fit (by decide)).trans h.r2, (eq.number fit (by decide)).trans h.one⟩
  change ((m'.readW (off (State.addr base) (arrAt w 0)) 64).toNat *
    (m'.readW (off (State.addr base) 56) 64).toNat + 1) % 2 ^ 64 = 0
  rw [eq.word (d := arrAt w 0) (bits := 64) (by omega), eq.word (d := 56) (bits := 64) (by omega)]
  exact h.inverse

theorem CrtPoweredState.ready {s : State} {base : BitVec 32} {len w M value : Nat}
    (h : CrtPoweredState base len w M value s.mem) (selected : LayoutFrameReady base len w s) :
    ArithmeticReady base len w s :=
  ⟨selected.workspace, h.layout.layout, h.layout.width, selected.ptr, h.inverse,
    h.modulus.symm ▸ h.positive, selected.stackRead, selected.stackSep, selected.saved⟩

end VG.Proof.Bignum.Arm
