module
public import VerifiedGarbage.Impl.Bignum.Arm.LoadBEFn
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Rsa.MontContract
public import VerifiedGarbage.Spec.Rsa.Contract

import VerifiedGarbage.Proof.Bignum.Arm.LoadBEFnArgs
import VerifiedGarbage.Proof.Bignum.Arm.LoadBE
import VerifiedGarbage.Proof.Bignum.Arm.ArrayFrame
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! # Zero-extended import into an RSA workspace array -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt wOf Layout)
open VG.Proof.X25519.Arm (Rest)

theorem loadBEFnBody_ok (s : State) {base src : BitVec 32} {len w o k : Nat}
    (ws : Workspace s base (8 * len)) (layout : Layout s.mem (State.addr base) len)
    (width : wOf s.mem (State.addr base) = w) (ho : o < 8)
    (hk : 0 < k) (fit : k ≤ 8 * w) (srcFit : src.toNat + k ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (State.addr src) k)
    (sep : Region.Disjoint ⟨State.addr src, k⟩ ⟨State.addr base, 8 * len⟩)
    (ptr : s.gpr .r0 = base) (index : s.gpr .r2 = BitVec.ofNat 32 o)
    (source : s.gpr .r4 = src) (count : s.gpr .r6 = BitVec.ofNat 32 k) :
    WP isa loadBEFnBody s fun t =>
      numAt t.mem (State.addr base) w o = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) ∧
      Outside (State.addr base) (arrAt w o) (8 * w) s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
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
  rw [loadBEFnBody, WP.seq_iff]
  refine WP.mono (loadBEFnArgs_ok s ws size header ho ptr index) ?_
  rintro u ⟨p0, p5, limbs, zero, mem, rest⟩
  have write : InRegions u.wr (State.addr dst) (4 * (2 * w)) := by
    rw [rest.wr, dstAddr]
    exact ⟨_, ws.writable, Offset.contains_base _ (by omega) (by omega)⟩
  have readU : InRegions (u.rd ++ u.wr) (State.addr src) k := by rw [rest.rd, rest.wr]; exact read
  have sepDst : Region.Disjoint ⟨State.addr src, k⟩ ⟨State.addr dst, 4 * (2 * w)⟩ := by
    apply sep.sub_right
    intro a ha
    rw [dstAddr] at ha
    change (a - off (State.addr base) (arrAt w o)).toNat + 1 ≤ 4 * (2 * w) at ha
    have hi : (a - off (State.addr base) (arrAt w o)).toNat < 4 * (2 * w) := by omega
    rw [Offset.lt_iff a (State.addr base) (by omega)] at hi
    change (a - State.addr base).toNat + 1 ≤ 8 * len
    omega
  refine WP.mono (loadBE_ok u hk (by omega) (by omega) srcFit (by rw [dstNat]; omega)
    readU write sepDst p0 ((rest.gpr .r4 (by decide)).trans source) p5
    ((rest.gpr .r6 (by decide)).trans count) limbs zero) ?_
  rintro t ⟨value, frame, keep⟩
  rw [native_array_num t.mem (by omega), mem] at value
  rw [dstAddr, mem, show 4 * (2 * w) = 8 * w by omega] at frame
  have outside := frame_array_outside (by omega) frame
  exact ⟨value, outside, outside_workspace outside (by omega),
    (rest.mono (by decide)).trans (keep.mono (by decide))⟩

theorem loadBEFn_ok (s : State) {base src : BitVec 32} {len w o k : Nat}
    (ws : Workspace s base (8 * len)) (layout : Layout s.mem (State.addr base) len)
    (width : wOf s.mem (State.addr base) = w) (ho : o < 8)
    (hk : 0 < k) (fit : k ≤ 8 * w) (srcFit : src.toNat + k ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (State.addr src) k)
    (sep : Region.Disjoint ⟨State.addr src, k⟩ ⟨State.addr base, 8 * len⟩)
    (ptr : s.gpr .r0 = base) (index : s.gpr .r2 = BitVec.ofNat 32 o)
    (source : s.gpr .r4 = src) (count : s.gpr .r6 = BitVec.ofNat 32 k)
    (stackRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 4⟩ ⟨State.addr base, 8 * len⟩)
    (saved : s.mem.readW (State.addr s.sp) 32 = base) :
    WP isa loadBEFn s fun t =>
      numAt t.mem (State.addr base) w o = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) ∧
      Outside (State.addr base) (arrAt w o) (8 * w) s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t ∧ t.gpr .r0 = base := by
  rw [loadBEFn, WP.seq_iff]
  refine WP.mono (loadBEFnBody_ok s ws layout width ho hk fit srcFit read sep ptr index source count) ?_
  rintro u ⟨value, outside, frame, rest⟩
  refine WP.mono (restoreBase_ok u
    (by rw [rest.rd, rest.wr, rest.sp]; exact stackRead)
    (saved_base_kept frame stackSep saved rest.sp)) ?_
  rintro t ⟨out, mem, keep⟩
  rw [← mem] at value outside frame
  exact ⟨value, outside, frame, rest.trans (keep.mono (by decide)), out⟩

end VG.Proof.Bignum.Arm
