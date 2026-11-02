module
public import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulusCT
public import VerifiedGarbage.Impl.Bignum.Arm.ImportArray
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState

import VerifiedGarbage.Proof.Bignum.Arm.ImportArray
import VerifiedGarbage.Proof.Bignum.Arm.LayoutFrameReady
import VerifiedGarbage.Proof.Bignum.Arm.ArrayFrame
import VerifiedGarbage.Proof.Bignum.Arm.ClearArrayWide
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge

/-! # Import a packed precomputation while preserving workspace layout -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Keeps)
open VG.Proof.X25519.Arm (Rest)

theorem importArrayLayout_ok (s : State) {base src : BitVec 32} {len w o : Nat}
    (h : LayoutFrameReady base len w s) (ho : o < 8)
    (sourceFit : src.toNat + 8 * w ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (State.addr src) (8 * w))
    (sep : Region.Disjoint ⟨State.addr base, 8 * len⟩ ⟨State.addr src, 8 * w⟩)
    (index : s.gpr .r2 = BitVec.ofNat 32 o) (source : s.gpr .r4 = src) :
    WP isa importArray s fun t => LayoutFrameReady base len w t ∧
      numAt t.mem (State.addr base) w o = (s.mem.read (State.addr src) (8 * w)).toNat ∧
      Keeps (State.addr base) len w o s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t ∧ t.gpr .r4 = src := by
  have nowrap := h.workspace.nowrap
  have arraysFit : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have bound := Nat.le_trans (array_end_le ho) arraysFit
  refine WP.mono (importArray_ok s h.workspace h.layout h.width ho sourceFit read sep h.ptr index source) ?_
  rintro t ⟨value, frameT, ptr, sourceT, rest⟩
  have outside := frame_array_outside (by omega : arrAt w o + 8 * w < 2 ^ 64) frameT
  have frame := outside_workspace outside (size := 8 * len) (by omega)
  have keeps := outside_array_prefix_keeps outside (by omega : 8 * len < 2 ^ 64) (by omega : 8 * w ≤ 8 * (w + 2))
  exact ⟨h.after_array keeps frame rest ptr, congrArg BitVec.toNat value, keeps, frame, rest, sourceT⟩

end VG.Proof.Bignum.Arm
