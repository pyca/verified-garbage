module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtPadModulusState
public import VerifiedGarbage.Impl.Bignum.Arm.CrtPadModulus

import VerifiedGarbage.Proof.Bignum.Arm.CrtPadModulusArgs
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Impl.Bignum.Arm.ExportArray
import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Rsa.MontContract
import VerifiedGarbage.Proof.Bignum.Arm.ExportArray
import VerifiedGarbage.Proof.Bignum.Arm.ArrayFrame
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
/-! # Exact full-width modulus padding for CRT validation -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/ExportPadded.lean`, which only this module imported.
section

/-! # Export a modulus into a zero-padded full-product buffer -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt wOf Layout numAt)
open VG.Proof.X25519.Arm (Rest)

theorem exportPadded_ok (s : State) {base : BitVec 32} {len w o d k : Nat}
    (ws : Workspace s base (8 * len)) (layout : Layout s.mem (State.addr base) len)
    (width : wOf s.mem (State.addr base) = w) (ho : o < 8)
    (fit : base.toNat + d + 4 * (2 * w + k) ≤ 2 ^ 32)
    (write : InRegions s.wr (off (State.addr base) d) (8 * w))
    (sep : Region.Disjoint ⟨State.addr base, 8 * len⟩ ⟨off (State.addr base) d, 8 * w⟩)
    (zero : val32 s.mem (State.addr base) (d + 8 * w) k = 0)
    (ptr : s.gpr .r0 = base) (index : s.gpr .r2 = BitVec.ofNat 32 o)
    (output : s.gpr .r4 = base + BitVec.ofNat 32 d) :
    WP isa exportArray s fun t =>
      val32 t.mem (State.addr base) d (2 * w + k) = numAt s.mem (State.addr base) w o ∧
      Outside (State.addr base) d (8 * w) s.mem t.mem ∧
      t.gpr .r0 = base ∧ Rest roundClobbers s t := by
  have hw : 2 ≤ w := width ▸ layout.1
  have dstAddr : State.addr (base + BitVec.ofNat 32 d) = off (State.addr base) d := addr_add (by omega)
  have dstNat : (base + BitVec.ofNat 32 d).toNat = base.toNat + d := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : d < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : base.toNat + d < 2 ^ 32)]
  refine WP.mono (exportArray_ok s ws layout width ho (by rw [dstNat]; omega)
    (by rw [dstAddr]; exact write) (by rw [dstAddr]; exact sep) ptr index output) ?_
  rintro t ⟨value, frame, ptrT, _, rest⟩
  rw [dstAddr] at value frame
  have outside := frame_array_outside (by omega : d + 8 * w < 2 ^ 64) frame
  have high := outside.val32 (d := d + 8 * w) (k := k) (by omega) (by omega)
  have low : val32 t.mem (State.addr base) d (2 * w) = numAt s.mem (State.addr base) w o := by
    rw [← read_eq_val32, show 4 * (2 * w) = 8 * w by omega, value]
    rfl
  refine ⟨?_, outside, ptrT, rest⟩
  rw [val32_append, show d + 4 * (2 * w) = d + 8 * w by omega, high, zero,
    Nat.mul_zero, Nat.add_zero, low]

end VG.Proof.Bignum.Arm
end

end

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt)
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
