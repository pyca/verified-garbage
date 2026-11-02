module

import VerifiedGarbage.Proof.Bignum.Arm.ExportArrayArgs
import VerifiedGarbage.Proof.Bignum.Arm.ImportArraySwap
import VerifiedGarbage.Proof.Bignum.Arm.CopyBuffer
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Rsa.MontContract
public import VerifiedGarbage.Impl.Bignum.Arm.ImportArray
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! # Exact packed-word import into a shared RSA array -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt wOf Layout)
open VG.Proof.X25519.Arm (Rest wp_mov op2_reg)

theorem importArray_ok (s : State) {base src : BitVec 32} {len w o : Nat}
    (ws : Workspace s base (8 * len)) (layout : Layout s.mem (State.addr base) len)
    (width : wOf s.mem (State.addr base) = w) (ho : o < 8)
    (srcFit : src.toNat + 8 * w ≤ 2 ^ 32) (read : InRegions (s.rd ++ s.wr) (State.addr src) (8 * w))
    (sep : Region.Disjoint ⟨State.addr base, 8 * len⟩ ⟨State.addr src, 8 * w⟩)
    (ptr : s.gpr .r0 = base) (index : s.gpr .r2 = BitVec.ofNat 32 o) (source : s.gpr .r4 = src) :
    WP isa importArray s fun t =>
      t.mem.read (off (State.addr base) (arrAt w o)) (8 * w) = s.mem.read (State.addr src) (8 * w) ∧
      Frame [⟨off (State.addr base) (arrAt w o), 8 * w⟩] s.mem t.mem ∧
      t.gpr .r0 = base ∧ t.gpr .r4 = src ∧ Rest roundClobbers s t := by
  have nowrap := ws.nowrap
  have hw : 2 ≤ w := width ▸ layout.1
  have fits : arrAt w 8 ≤ 8 * len := width ▸ layout.2.2.1
  have bound := Nat.le_trans (array_end_le ho) fits
  have size : 128 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  let dst := base + BitVec.ofNat 32 (arrAt w o)
  have dstAddr : State.addr dst = off (State.addr base) (arrAt w o) := addr_add (by omega)
  have dstNat : dst.toNat = base.toNat + arrAt w o := by
    simp only [dst, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : arrAt w o < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : base.toNat + arrAt w o < 2 ^ 32)]
  have header := nativeHeader_of_layout s.mem base nowrap (Nat.le_refl _) layout
  rw [width] at header
  rw [importArray, WP.seq_iff]
  refine WP.mono (exportArrayArgs_ok s ws size header ho ptr index) ?_
  rintro u ⟨p0, p1, count, saved, mem, rest⟩
  have write : InRegions u.wr (State.addr dst) (8 * w) := by
    rw [rest.wr, dstAddr]
    exact ⟨_, ws.writable, Offset.contains_base _ (by omega) (by omega)⟩
  have sepDst : Region.Disjoint ⟨State.addr src, 8 * w⟩ ⟨State.addr dst, 8 * w⟩ := by
    apply sep.symm.sub_right
    rw [dstAddr]
    exact Offset.sub_base _ (by omega)
  rw [WP.seq_iff]
  refine WP.mono (importArraySwap_ok u) ?_
  rintro z ⟨destZ, sourceZ, memZ, restZ⟩
  rw [WP.seq_iff]
  refine WP.mono (copyBuffer_ok z (by omega) srcFit (by rw [dstNat]; omega) (by omega)
    (by rw [restZ.rd, restZ.wr, rest.rd, rest.wr]; exact read)
    (by rw [restZ.wr]; exact write) sepDst (destZ.trans p1) (sourceZ.trans (p0.trans source))
    ((restZ.gpr .lr (by decide)).trans count)) ?_
  rintro v ⟨value, frame, _, keep⟩
  refine wp_mov (op2_reg _ _) fun t moved => WP.block_nil ?_
  rw [dstAddr, memZ, mem] at value
  rw [dstAddr, memZ, mem] at frame
  refine ⟨by rw [moved.mem]; exact value, by rw [moved.mem]; exact frame, ?_, ?_, ?_⟩
  · rw [moved.gpr, keep.gpr .r5 (by decide), restZ.gpr .r5 (by decide), saved]
  · rw [moved.other .r4 (by decide), keep.gpr .r4 (by decide), restZ.gpr .r4 (by decide), rest.gpr .r4 (by decide), source]
  · exact ((rest.mono (by decide)).trans (restZ.mono (by decide))).trans
      ((keep.mono (by decide)).trans (moved.rest (by decide)))

end VG.Proof.Bignum.Arm
