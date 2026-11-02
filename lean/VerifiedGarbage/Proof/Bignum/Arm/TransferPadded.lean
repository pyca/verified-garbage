module
public import VerifiedGarbage.Impl.Bignum.Arm.TransferArray
public import VerifiedGarbage.Proof.Bignum.Arm.CrtWorkspaceState
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulusCT

import VerifiedGarbage.Proof.Bignum.Arm.TransferArrayArgs
import VerifiedGarbage.Proof.Bignum.Arm.ClearArrayWide
import VerifiedGarbage.Proof.Bignum.Arm.LayoutFrameReady
import VerifiedGarbage.Proof.Bignum.Arm.ExportArray
import VerifiedGarbage.Proof.Bignum.Arm.ArrayFrame
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Arm.ByteWords

/-! # Transfer a residue from a narrower workspace into a cleared array

The source workspace's width gives the bytes copied; the destination array's
remaining words were cleared, so it holds the same number at its own width.
-/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Keeps)
open VG.Proof.X25519.Arm (Rest)

structure TransferPaddedCtx (base src : BitVec 32) (len slen w v : Nat) (s : State) : Prop where
  destination : LayoutFrameReady base len w s
  source : Workspace s src (8 * slen)
  layout : CrtLayoutState src slen v s.mem
  ptr : s.gpr .r1 = src
  separate : Region.Disjoint ⟨State.addr src, 8 * slen⟩ ⟨State.addr base, 8 * len⟩
  narrower : v ≤ w

structure TransferPaddedInput (base src : BitVec 32) (len slen w v o : Nat) (s : State) : Prop
    extends TransferPaddedCtx base src len slen w v s where
  cleared : val32 s.mem (State.addr base) (arrAt w o) (2 * w + 2) = 0

theorem val32_zero_split {m : Mem} {base : Addr} {d j k : Nat} (h : val32 m base d (j + k) = 0) :
    val32 m base d j = 0 ∧ val32 m base (d + 4 * j) k = 0 := by
  rw [val32_append] at h
  have positive : 0 < 2 ^ (32 * j) := Nat.two_pow_pos _
  refine ⟨by omega, ?_⟩
  rcases Nat.eq_zero_or_pos (val32 m base (d + 4 * j) k) with zero | pos
  · exact zero
  · have := Nat.mul_le_mul_left (2 ^ (32 * j)) pos
    omega

theorem transferPadded_ok (s : State) {base src : BitVec 32} {len slen w v o a : Nat}
    (h : TransferPaddedInput base src len slen w v o s) (ho : o < 8) (ha : a < 8) :
    WP isa (transferArray o a) s fun t => LayoutFrameReady base len w t ∧
      numAt t.mem (State.addr base) w o = numAt s.mem (State.addr src) v a ∧
      Keeps (State.addr base) len w o s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have dst := h.destination
  have nowrap := dst.workspace.nowrap
  have narrower := h.narrower
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
  have write : InRegions u.wr (State.addr output) (8 * v) := by
    rw [restU.wr, outAddr]
    exact ⟨_, dst.workspace.writable, Offset.contains_base _ (by omega) (by omega)⟩
  have sep : Region.Disjoint ⟨State.addr src, 8 * slen⟩ ⟨State.addr output, 8 * v⟩ := by
    apply h.separate.sub_right
    rw [outAddr]
    exact Offset.sub_base _ (by omega)
  rw [WP.seq_iff]
  refine WP.mono (exportArray_ok u (h.source.congr restU.wr)
    (by rw [memU]; exact h.layout.layout) (w := v) (by rw [memU]; exact h.layout.width)
    ha (by rw [outNat]; omega) write sep ptrU indexU outputU) ?_
  rintro z ⟨value, frameZ, _, _, restZ⟩
  rw [memU, outAddr] at value frameZ
  have outside := frame_array_outside (by omega : arrAt w o + 8 * v < 2 ^ 64) frameZ
  have frame := outside_workspace outside (size := 8 * len) (by omega)
  have keeps := outside_array_prefix_keeps outside (by omega : 8 * len < 2 ^ 64) (by omega : 8 * v ≤ 8 * (w + 2))
  have rest : Rest roundClobbers s z := (restU.mono (by decide)).trans restZ
  refine WP.mono (restoreBase_ok z (by rw [rest.rd, rest.wr, rest.sp]; exact dst.stackRead)
    (saved_base_kept frame dst.stackSep dst.saved rest.sp)) ?_
  rintro t ⟨ptrT, memT, restT⟩
  have keepsT : Keeps (State.addr base) len w o s.mem t.mem := by rw [memT]; exact keeps
  have frameT : Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem := by rw [memT]; exact frame
  have restAll := rest.trans (restT.mono (by decide))
  refine ⟨dst.after_array keepsT frameT restAll ptrT, ?_, keepsT, frameT, restAll⟩
  have zero := h.cleared
  rw [show 2 * w + 2 = 2 * v + ((2 * w - 2 * v) + 2) by omega] at zero
  have high := (val32_zero_split (val32_zero_split zero).2).1
  rw [numAt_native, memT, show 2 * w = 2 * v + (2 * w - 2 * v) by omega, val32_append,
    outside.val32 (d := arrAt w o + 4 * (2 * v)) (Or.inr (by omega)) (by omega), high,
    Nat.mul_zero, Nat.add_zero, ← read_eq_val32, show 4 * (2 * v) = 8 * v by omega, value]
  rfl

end VG.Proof.Bignum.Arm
