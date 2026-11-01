module
public import VerifiedGarbage.Impl.Bignum.Arm.ExportBE
public import VerifiedGarbage.Proof.Rsa.MontContract
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
public import VerifiedGarbage.Spec.Rsa.Contract

import VerifiedGarbage.Proof.Bignum.Arm.ExportBEArgs
import VerifiedGarbage.Proof.Bignum.Arm.ReverseBuffer
import VerifiedGarbage.Proof.Bignum.ReadPrefix
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Fixed-width I2OSP export from a shared RSA array -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt wOf numAt Layout)
open VG.Proof.X25519.Arm (Rest wp_mov op2_reg)

theorem exportBE_truncated_ok (s : State) {base dst : BitVec 32} {len w o k : Nat}
    (ws : Workspace s base (8 * len)) (layout : Layout s.mem (State.addr base) len)
    (width : wOf s.mem (State.addr base) = w) (ho : o < 8) (hk : 0 < k) (hk' : k ≤ 8 * w)
    (dstFit : dst.toNat + k ≤ 2 ^ 32) (write : InRegions s.wr (State.addr dst) k)
    (sep : Region.Disjoint ⟨State.addr base, 8 * len⟩ ⟨State.addr dst, k⟩)
    (ptr : s.gpr .r0 = base) (index : s.gpr .r2 = BitVec.ofNat 32 o) (output : s.gpr .r4 = dst) (countReg : s.gpr .r6 = BitVec.ofNat 32 k) :
    WP isa exportBE s fun t =>
      Spec.Rsa.bytesAt t.mem (State.addr dst) k = Spec.Rsa.i2osp (numAt s.mem (State.addr base) w o % 2 ^ (8 * k)) k ∧
      Frame [⟨State.addr dst, k⟩] s.mem t.mem ∧
      t.gpr .r0 = base ∧ t.gpr .r4 = dst ∧ Rest [.r0, .r1, .r2, .r5, .lr] s t := by
  have nowrap := ws.nowrap
  have hw : 2 ≤ w := width ▸ layout.1
  have fits : arrAt w 8 ≤ 8 * len := width ▸ layout.2.2.1
  have bound := Nat.le_trans (array_end_le ho) fits
  have size : 128 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  let src := base + BitVec.ofNat 32 (arrAt w o)
  have srcAddr : State.addr src = off (State.addr base) (arrAt w o) := addr_add (by omega)
  have srcNat : src.toNat = base.toNat + arrAt w o := by
    simp only [src, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : arrAt w o < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : base.toNat + arrAt w o < 2 ^ 32)]
  have header := nativeHeader_of_layout s.mem base nowrap (Nat.le_refl _) layout
  rw [width] at header
  rw [exportBE, WP.seq_iff]
  refine WP.mono (exportBEArgs_ok s ws size header ho hk ptr index countReg) ?_
  rintro u ⟨p0, p1, count, saved, mem, rest⟩
  have read : InRegions (u.rd ++ u.wr) (State.addr src) k := by
    rw [rest.rd, rest.wr, srcAddr]
    exact ⟨_, List.mem_append_right _ ws.writable, Offset.contains_base _ (by omega) (by omega)⟩
  have sepSrc : Region.Disjoint ⟨State.addr src, k⟩ ⟨State.addr dst, k⟩ := by
    apply sep.sub_left
    intro a ha
    rw [srcAddr] at ha
    change (a - off (State.addr base) (arrAt w o)).toNat + 1 ≤ k at ha
    have hi : (a - off (State.addr base) (arrAt w o)).toNat < k := by omega
    rw [Offset.lt_iff a (State.addr base) (by omega)] at hi
    change (a - State.addr base).toNat + 1 ≤ 8 * len
    omega
  rw [WP.seq_iff]
  refine WP.mono (reverseBuffer_ok u hk (by rw [srcNat]; omega) dstFit (by omega)
    read (by rw [rest.wr]; exact write) sepSrc (p0.trans output) p1 count) ?_
  rintro v ⟨value, frame, _, keep⟩
  refine wp_mov (op2_reg _ _) fun t moved => WP.block_nil ?_
  rw [srcAddr, mem] at value
  rw [read_prefix s.mem _ hk', BitVec.toNat_setWidth] at value
  rw [mem] at frame
  refine ⟨by rw [moved.mem]; exact value, by rw [moved.mem]; exact frame, ?_, ?_, ?_⟩
  · rw [moved.gpr, keep.gpr .r5 (by decide), saved]
  · rw [moved.other .r4 (by decide), keep.gpr .r4 (by decide), rest.gpr .r4 (by decide), output]
  · exact (rest.mono (by decide)).trans
      ((keep.mono (by decide)).trans (moved.rest (by decide)))

theorem exportBE_ok (s : State) {base dst : BitVec 32} {len w o k : Nat}
    (ws : Workspace s base (8 * len)) (layout : Layout s.mem (State.addr base) len)
    (width : wOf s.mem (State.addr base) = w) (ho : o < 8) (hk : 0 < k) (hk' : k ≤ 8 * w)
    (valueFit : numAt s.mem (State.addr base) w o < 2 ^ (8 * k))
    (dstFit : dst.toNat + k ≤ 2 ^ 32) (write : InRegions s.wr (State.addr dst) k)
    (sep : Region.Disjoint ⟨State.addr base, 8 * len⟩ ⟨State.addr dst, k⟩)
    (ptr : s.gpr .r0 = base) (index : s.gpr .r2 = BitVec.ofNat 32 o) (output : s.gpr .r4 = dst) (countReg : s.gpr .r6 = BitVec.ofNat 32 k) :
    WP isa exportBE s fun t =>
      Spec.Rsa.bytesAt t.mem (State.addr dst) k = Spec.Rsa.i2osp (numAt s.mem (State.addr base) w o) k ∧
      Frame [⟨State.addr dst, k⟩] s.mem t.mem ∧
      t.gpr .r0 = base ∧ t.gpr .r4 = dst ∧ Rest [.r0, .r1, .r2, .r5, .lr] s t := by
  refine WP.mono (exportBE_truncated_ok s ws layout width ho hk hk' dstFit write sep ptr index output countReg) ?_
  intro t h
  rw [Nat.mod_eq_of_lt valueFit] at h
  exact h

end VG.Proof.Bignum.Arm
