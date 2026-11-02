module
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Impl.Bignum.Arm.PrecomputeOut
public import VerifiedGarbage.Proof.Rsa.MontContract

import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeOutArgs
import VerifiedGarbage.Proof.Bignum.Arm.ExportArray
import VerifiedGarbage.Proof.Bignum.Arm.LayoutPreserved
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Bignum.ExportEncoding
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Serialize both RSA precomputation arrays in the shared word format -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt wOf numAt Layout)
open VG.Proof.X25519.Arm (Rest wp_mov op2_imm)

theorem precomputeOut_ok (s : State) {base dst : BitVec 32} {len w : Nat}
    (ws : Workspace s base (8 * len)) (layout : Layout s.mem (State.addr base) len)
    (width : wOf s.mem (State.addr base) = w)
    (dstFit : dst.toNat + 16 * w ≤ 2 ^ 32) (write : InRegions s.wr (State.addr dst) (16 * w))
    (sep : Region.Disjoint ⟨State.addr base, 8 * len⟩ ⟨State.addr dst, 16 * w⟩)
    (ptr : s.gpr .r0 = base) (output : s.gpr .r4 = dst) :
    WP isa precomputeOut s fun t =>
      t.gpr .r0 = 1 ∧ Spec.Rsa.wordsAt t.mem (State.addr dst) (2 * w) =
        Spec.Rsa.toWords (numAt s.mem (State.addr base) w 0) w ++
        Spec.Rsa.toWords (numAt s.mem (State.addr base) w 4) w ∧
      Frame [⟨State.addr dst, 16 * w⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have nowrap := ws.nowrap
  have hw : 2 ≤ w := width ▸ layout.1
  have fits : arrAt w 8 ≤ 8 * len := width ▸ layout.2.2.1
  have size : 128 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  have firstWrite : InRegions s.wr (State.addr dst) (8 * w) := by
    simpa only [BitVec.add_zero] using CallLay.inRegions_sub (off := 0) write (by omega) (by omega)
  have firstSep := sep.sub_right (Region.sub_prefix (show 8 * w ≤ 16 * w by omega))
  let dst2 := dst + BitVec.ofNat 32 (8 * w)
  have dst2Addr : State.addr dst2 = off (State.addr dst) (8 * w) := addr_add (by omega)
  have dst2Nat : dst2.toNat = dst.toNat + 8 * w := by
    simp only [dst2, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 8 * w < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : dst.toNat + 8 * w < 2 ^ 32)]
  have secondWrite : InRegions s.wr (State.addr dst2) (8 * w) := by
    rw [dst2Addr]; exact CallLay.inRegions_sub write (by omega) (by omega)
  have secondSub : Region.Sub ⟨State.addr dst2, 8 * w⟩ ⟨State.addr dst, 16 * w⟩ := by
    rw [dst2Addr]; exact Offset.sub_base _ (by omega)
  have secondSep := sep.sub_right secondSub
  have halves : Region.Disjoint ⟨State.addr dst, 8 * w⟩ ⟨State.addr dst2, 8 * w⟩ := by
    rw [dst2Addr]; exact (Offset.disjoint_base _ (by omega) (by omega)).symm
  rw [precomputeOut, WP.seq_iff]
  refine wp_mov (op2_imm (by decide)) fun u moved => WP.block_nil ?_
  rw [WP.seq_iff]
  refine WP.mono (exportArray_ok u (ws.congr moved.wr) (by rw [moved.mem]; exact layout)
    (by rw [moved.mem]; exact width) (o := 0) (by decide) (by omega)
    (by rw [moved.wr]; exact firstWrite) firstSep ((moved.other .r0 (by decide)).trans ptr)
    moved.gpr ((moved.other .r4 (by decide)).trans output)) ?_
  rintro v ⟨firstValue, firstFrame, baseV, dstV, restV⟩
  rw [moved.mem] at firstValue firstFrame
  have rv : Rest roundClobbers s v := (moved.rest (by decide)).trans restV
  have unchanged : WorkspaceEq (State.addr base) (8 * len) s.mem v.mem :=
    WorkspaceEq.of_frame (by omega) firstFrame (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact firstSep)
  have layoutV := unchanged.layout layout
  have widthV := (unchanged.width (by omega)).trans width
  have header := nativeHeader_of_layout v.mem base nowrap (Nat.le_refl _) layoutV
  rw [widthV] at header
  rw [WP.seq_iff]
  refine WP.mono (precomputeOutAdvance_ok v (ws.congr rv.wr) (by omega) baseV header.count) ?_
  rintro z ⟨dstZ, indexZ, memZ, restZ⟩
  have rz : Rest roundClobbers s z := rv.trans (restZ.mono (by decide))
  rw [WP.seq_iff]
  refine WP.mono (exportArray_ok z (ws.congr rz.wr) (by rw [memZ]; exact layoutV)
    (by rw [memZ]; exact widthV) (o := 4) (by decide) (by rw [dst2Nat]; omega)
    (by rw [rz.wr]; exact secondWrite) secondSep
    ((restZ.gpr .r0 (by decide)).trans baseV) indexZ (by rw [dstZ, dstV])) ?_
  rintro a ⟨secondValue, secondFrame, _, _, restA⟩
  have ra := rz.trans restA
  rw [dst2Addr, memZ] at secondValue
  have arr4fit := Nat.le_trans (array_end_le (w := w) (j := 4) (k := 8) (by decide)) fits
  rw [unchanged.read (arrAt w 4) (8 * w) (by omega)] at secondValue
  have firstKept := secondFrame.read (r := ⟨State.addr dst, 8 * w⟩) (Region.contains_self _ _)
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact halves) (by omega)
  rw [memZ, firstValue] at firstKept
  have firstWhole := firstFrame.sub (rs' := [⟨State.addr dst, 16 * w⟩]) (by
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    exact ⟨⟨State.addr dst, 16 * w⟩, by simp, Region.sub_prefix (by omega)⟩)
  have secondWhole := secondFrame.sub (rs' := [⟨State.addr dst, 16 * w⟩]) (by
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    exact ⟨⟨State.addr dst, 16 * w⟩, by simp, secondSub⟩)
  rw [memZ] at secondWhole
  refine wp_mov (op2_imm (by decide)) fun t result => WP.block_nil ?_
  refine ⟨result.gpr, ?_, ?_, ra.trans (result.rest (by decide))⟩
  · rw [result.mem]
    apply wordsAt_two_reads
    · exact congrArg BitVec.toNat firstKept
    · exact congrArg BitVec.toNat secondValue
  · rw [result.mem]; exact firstWhole.trans secondWhole

end VG.Proof.Bignum.Arm
