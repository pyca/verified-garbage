module

import VerifiedGarbage.Proof.Bignum.Arm.TransferArrayArgs
import VerifiedGarbage.Proof.Bignum.Arm.ExportArray
import VerifiedGarbage.Proof.Bignum.Arm.LayoutFrameReady
import VerifiedGarbage.Proof.Bignum.Arm.ArrayFrame
import VerifiedGarbage.Proof.Bignum.Arm.ClearArrayWide
public import VerifiedGarbage.Proof.Bignum.Arm.CrtWorkspaceState
public import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulusCT
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Impl.Bignum.Arm.TransferArray
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! # Exact transfer of a secret residue between disjoint RSA workspaces -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Keeps)
open VG.Proof.X25519.Arm (Rest)

structure TransferArrayInput (base src : BitVec 32) (len slen w : Nat) (s : State) : Prop where
  destination : LayoutFrameReady base len w s
  source : Workspace s src (8 * slen)
  layout : CrtLayoutState src slen w s.mem
  ptr : s.gpr .r1 = src
  separate : Region.Disjoint ⟨State.addr src, 8 * slen⟩ ⟨State.addr base, 8 * len⟩

theorem transferArray_ok (s : State) {base src : BitVec 32} {len slen w o a : Nat}
    (h : TransferArrayInput base src len slen w s) (ho : o < 8) (ha : a < 8) :
    WP isa (transferArray o a) s fun t => LayoutFrameReady base len w t ∧
      numAt t.mem (State.addr base) w o = numAt s.mem (State.addr src) w a ∧
      Keeps (State.addr base) len w o s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have dst := h.destination
  have nowrap := dst.workspace.nowrap
  have arraysFit : arrAt w 8 ≤ 8 * len := dst.width ▸ dst.layout.2.2.1
  have bound := Nat.le_trans (array_end_le ho) arraysFit
  have small : 128 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at arraysFit; omega
  let output := base + BitVec.ofNat 32 (arrAt w o)
  have outAddr : State.addr output = off (State.addr base) (arrAt w o) := addr_add (by omega)
  have outNat : output.toNat = base.toNat + arrAt w o := by
    simp only [output, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : arrAt w o < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : base.toNat + arrAt w o < 2 ^ 32)]
  have header := nativeHeader_of_layout s.mem base nowrap (Nat.le_refl _) dst.layout
  rw [dst.width] at header
  rw [transferArray, WP.seq_iff]
  refine WP.mono (transferArrayArgs_ok s dst.workspace small ho ha dst.ptr h.ptr (header.array o ho)) ?_
  rintro u ⟨ptrU, outputU, indexU, memU, restU⟩
  have write : InRegions u.wr (State.addr output) (8 * w) := by
    rw [restU.wr, outAddr]
    exact ⟨_, dst.workspace.writable, Offset.contains_base _ (by omega) (by omega)⟩
  have sep : Region.Disjoint ⟨State.addr src, 8 * slen⟩ ⟨State.addr output, 8 * w⟩ := by
    apply h.separate.sub_right
    rw [outAddr]
    exact Offset.sub_base _ (by omega)
  rw [WP.seq_iff]
  refine WP.mono (exportArray_ok u (h.source.congr restU.wr)
    (by rw [memU]; exact h.layout.layout) (w := w) (by rw [memU]; exact h.layout.width)
    ha (by rw [outNat]; omega) write sep ptrU indexU outputU) ?_
  rintro v ⟨value, frameV, _, _, restV⟩
  rw [memU, outAddr] at value frameV
  have outside := frame_array_outside (by omega : arrAt w o + 8 * w < 2 ^ 64) frameV
  have frame := outside_workspace outside (size := 8 * len) (by omega)
  have keeps := outside_array_prefix_keeps outside (by omega : 8 * len < 2 ^ 64) (by omega : 8 * w ≤ 8 * (w + 2))
  have rest : Rest roundClobbers s v := (restU.mono (by decide)).trans restV
  refine WP.mono (restoreBase_ok v (by rw [rest.rd, rest.wr, rest.sp]; exact dst.stackRead)
    (saved_base_kept frame dst.stackSep dst.saved rest.sp)) ?_
  rintro t ⟨ptrT, memT, restT⟩
  have keepsT : Keeps (State.addr base) len w o s.mem t.mem := by rw [memT]; exact keeps
  have frameT : Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem := by rw [memT]; exact frame
  have restAll := rest.trans (restT.mono (by decide))
  exact ⟨dst.after_array keepsT frameT restAll ptrT, by unfold numAt; rw [memT, value],
    keepsT, frameT, restAll⟩

end VG.Proof.Bignum.Arm
