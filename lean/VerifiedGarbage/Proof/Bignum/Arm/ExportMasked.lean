module

public import VerifiedGarbage.Impl.Bignum.Arm.ExportMasked
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Rsa.MontContract
import VerifiedGarbage.Proof.Bignum.Arm.ExportBE
import VerifiedGarbage.Proof.Bignum.Arm.MaskOutput
import VerifiedGarbage.Proof.Bignum.Arm.LayoutPreserved
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # The serialized result and return status implement secret input acceptance -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt wOf Layout)
open VG.Proof.X25519.Arm (Rest)

theorem exportMasked_truncated_ok (s : State) {base dst : BitVec 32} {len w o k : Nat} {accepted : Bool}
    (ws : Workspace s base (8 * len)) (layout : Layout s.mem (State.addr base) len)
    (width : wOf s.mem (State.addr base) = w) (ho : o < 8) (hk : 0 < k) (hk' : k ≤ 8 * w)
    (dstFit : dst.toNat + k ≤ 2 ^ 32) (write : InRegions s.wr (State.addr dst) k)
    (sep : Region.Disjoint ⟨State.addr base, 8 * len⟩ ⟨State.addr dst, k⟩)
    (ptr : s.gpr .r0 = base) (index : s.gpr .r2 = BitVec.ofNat 32 o)
    (output : s.gpr .r4 = dst) (count : s.gpr .r6 = BitVec.ofNat 32 k)
    (stackFit : s.sp.toNat + 52 ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 48) 4)
    (stackSep : Region.Disjoint ⟨off (State.addr s.sp) 48, 4⟩ ⟨State.addr dst, k⟩)
    (flag : s.mem.readW (off (State.addr s.sp) 48) 32 = BitVec.ofNat 32 accepted.toNat) :
    WP isa exportMasked s fun t =>
      Spec.Rsa.bytesAt t.mem (State.addr dst) k =
        (if accepted then Spec.Rsa.i2osp (numAt s.mem (State.addr base) w o % 2 ^ (8 * k)) k else List.replicate k 0) ∧
      t.gpr .r0 = BitVec.ofNat 32 accepted.toNat ∧
      Frame [⟨State.addr dst, k⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have countFits : k < 2 ^ 32 := by
    have fit := layout.2.2.1
    rw [width] at fit
    simp only [Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes] at fit
    have := ws.nowrap
    omega
  rw [exportMasked, WP.seq_iff]
  refine WP.mono (exportBE_truncated_ok s ws layout width ho hk hk' dstFit write sep ptr index output count) ?_
  rintro u ⟨bytes, frameU, _, outputU, restU⟩
  have eq := WorkspaceEq.of_frame (by decide : 4 < 2 ^ 64) frameU
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact stackSep)
  have flagU : u.mem.readW (off (State.addr u.sp) 48) 32 = BitVec.ofNat 32 accepted.toNat := by
    rw [restU.sp]
    have keep := eq.word (d := 0) (bits := 32) (by decide)
    simp only [off, BitVec.add_zero] at keep
    exact keep.trans flag
  refine WP.mono (maskOutput_ok u hk countFits dstFit
    (by rw [restU.wr]; exact write) (by rw [restU.sp]; exact stackFit)
    (by rw [restU.rd, restU.wr, restU.sp]; exact read) flagU outputU
    ((restU.gpr .r6 (by decide)).trans count)) ?_
  rintro t ⟨value, status, frameT, restT⟩
  rw [bytes] at value
  exact ⟨value, status, frameU.trans frameT,
    (restU.mono (by decide)).trans (restT.mono (by decide))⟩

theorem exportMasked_ok (s : State) {base dst : BitVec 32} {len w o k : Nat} {accepted : Bool}
    (ws : Workspace s base (8 * len)) (layout : Layout s.mem (State.addr base) len)
    (width : wOf s.mem (State.addr base) = w) (ho : o < 8) (hk : 0 < k) (hk' : k ≤ 8 * w)
    (valueFit : numAt s.mem (State.addr base) w o < 2 ^ (8 * k))
    (dstFit : dst.toNat + k ≤ 2 ^ 32) (write : InRegions s.wr (State.addr dst) k)
    (sep : Region.Disjoint ⟨State.addr base, 8 * len⟩ ⟨State.addr dst, k⟩)
    (ptr : s.gpr .r0 = base) (index : s.gpr .r2 = BitVec.ofNat 32 o)
    (output : s.gpr .r4 = dst) (count : s.gpr .r6 = BitVec.ofNat 32 k)
    (stackFit : s.sp.toNat + 52 ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 48) 4)
    (stackSep : Region.Disjoint ⟨off (State.addr s.sp) 48, 4⟩ ⟨State.addr dst, k⟩)
    (flag : s.mem.readW (off (State.addr s.sp) 48) 32 = BitVec.ofNat 32 accepted.toNat) :
    WP isa exportMasked s fun t =>
      Spec.Rsa.bytesAt t.mem (State.addr dst) k =
        (if accepted then Spec.Rsa.i2osp (numAt s.mem (State.addr base) w o) k else List.replicate k 0) ∧
      t.gpr .r0 = BitVec.ofNat 32 accepted.toNat ∧
      Frame [⟨State.addr dst, k⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (exportMasked_truncated_ok s ws layout width ho hk hk' dstFit write sep ptr index output count stackFit read stackSep flag) ?_
  intro t h
  rw [Nat.mod_eq_of_lt valueFit] at h
  exact h

end VG.Proof.Bignum.Arm
