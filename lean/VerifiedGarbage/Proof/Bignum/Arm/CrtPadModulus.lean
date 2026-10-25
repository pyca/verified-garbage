module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtPadModulusState
public import VerifiedGarbage.Impl.Bignum.Arm.CrtPadModulus
import VerifiedGarbage.Proof.Bignum.Arm.CrtPadModulusArgs
import VerifiedGarbage.Proof.Bignum.Arm.ExportPadded
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block

/-! # Exact full-width modulus padding for CRT validation -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Spec.Rsa.Mont (numAt arrAt)
open VG.Proof.X25519.Arm (Rest)

theorem crt_padModulus_ok (s : State) {base : BitVec 32} {size len w d : Nat}
    (h : CrtPadInput base size len w d s) (operand : Fin 8 := 0) :
    WP isa (padModulus operand) s fun t =>
      val32 t.mem (State.addr base) d (4 * w + 2) = numAt s.mem (State.addr base) w operand.val ∧
      Outside (State.addr base) d (4 * (4 * w + 2)) s.mem t.mem ∧
      t.gpr .r0 = base ∧ Rest roundClobbers s t := by
  have nowrap := h.workspace.nowrap
  have separate := h.separate
  have fits := h.fits
  have small := h.layout.size
  rw [padModulus, WP.seq_iff]
  refine WP.mono (crt_padClear_ready s h) ?_
  rintro u ⟨hu, zeroU, outsideU, restU⟩
  have eq := WorkspaceEq.of_outside (by omega : 8 * len < 2 ^ 64) separate outsideU
  have arrFit : arrAt w 8 ≤ 8 * len := h.layout.width ▸ h.layout.layout.2.2.1
  have numberU := eq.number arrFit operand.isLt
  rw [WP.seq_iff]
  refine WP.mono (crt_padModulusArgs_ok u hu.workspace (by omega) hu.ptr hu.link operand) ?_
  rintro v ⟨outV, indexV, memV, restV⟩
  have write : InRegions v.wr (off (State.addr base) d) (8 * w) := by
    rw [restV.wr]
    exact ⟨_, hu.workspace.writable, Offset.contains_base _ (by omega) (by omega)⟩
  have sep : Region.Disjoint ⟨State.addr base, 8 * len⟩ ⟨off (State.addr base) d, 8 * w⟩ :=
    Offset.base_disjoint _ separate (by omega)
  refine WP.mono (exportPadded_ok v (hu.main.congr restV.wr)
    (by rw [memV]; exact hu.layout.layout) (w := w) (by rw [memV]; exact hu.layout.width)
    operand.isLt (k := 2 * w + 2) (by omega) write sep (by rw [memV]; exact zeroU)
    ((restV.gpr .r0 (by decide)).trans hu.ptr) indexV outV) ?_
  rintro t ⟨value, outside, ptrT, restT⟩
  rw [memV, numberU] at value
  rw [memV] at outside
  exact ⟨by simpa only [show 2 * w + (2 * w + 2) = 4 * w + 2 by omega] using value,
    outsideU.trans (outside.mono (Nat.le_refl _) (by omega)), ptrT,
    restU.trans ((restV.mono (by decide)).trans restT)⟩

end VG.Proof.Bignum.Arm
