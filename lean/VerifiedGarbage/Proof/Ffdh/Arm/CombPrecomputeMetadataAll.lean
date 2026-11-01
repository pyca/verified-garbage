module

import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeMetadata
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeBitsSave
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeRows
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeHeader
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
public import VerifiedGarbage.Proof.Ffdh.Arm.Locals
public import VerifiedGarbage.Proof.Ffdh.Arm.Output
public import VerifiedGarbage.Proof.Ffdh.ScalarWidth
public import VerifiedGarbage.Spec.Rsa.FixedBaseComb
import VerifiedGarbage.Proof.Ffdh.ScalarWidth

/-! The policy width becomes a canonical immutable three-word context header. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Impl.Ffdh.Arm.CombPrecompute
open VG.Proof.X25519.Arm (Rest)

def combMetadataWrites (s : State) (ctx : BitVec 32) : List Region :=
  [⟨off (State.addr s.sp) 16,4⟩,⟨off (State.addr s.sp) 44,4⟩,⟨State.addr ctx,24⟩]

def combMetadataClobbers : List Reg := [.r1,.r2,.r3,.r4,.r6,.r7,.r12]

theorem combMetadata_ok (s : State) {base ctx : BitVec 32} {len N : Nat}
    (locals : Locals base len s) (ws : OutputBuffer ctx 24 s)
    (separate : Region.Disjoint ⟨State.addr s.sp,72⟩ ⟨State.addr ctx,24⟩)
    (positive : 0<N) (bound : N≤8192)
    (savedCtx : s.mem.readW (off (State.addr s.sp) 4) 32=ctx)
    (savedWidth : s.mem.readW (off (State.addr s.sp) 20) 32=
      BitVec.ofNat 32 (VG.Proof.Ffdh.ScalarWidth.width N))
    (savedMask : s.mem.readW (off (State.addr s.sp) 68) 32=
      (VG.Proof.Ffdh.ScalarWidth.mask N).setWidth 32) :
    WP isa metadata s fun t =>
      let w := VG.Proof.Ffdh.ScalarWidth.width N
      let d := VG.Spec.Rsa.FixedBaseComb.rows N
      let m := (s.mem.writeW (off (State.addr s.sp) 16) (BitVec.ofNat 32 N)).writeW
        (off (State.addr s.sp) 44) (BitVec.ofNat 32 d)
      t.mem=((m.writeW (off (State.addr ctx) 0) (BitVec.ofNat 64 N)).writeW
        (off (State.addr ctx) 8) (BitVec.ofNat 64 w)).writeW
        (off (State.addr ctx) 16) (BitVec.ofNat 64 d) ∧
      Frame (combMetadataWrites s ctx) s.mem t.mem ∧ Rest combMetadataClobbers s t := by
  let h := VG.Proof.Ffdh.ScalarWidth.headBits N
  have headPositive : 0<h := by
    dsimp [h]
    unfold VG.Proof.Ffdh.ScalarWidth.headBits VG.Proof.Ffdh.ScalarWidth.width
    omega
  have headBound : h≤8 := (VG.Proof.Ffdh.ScalarWidth.headBits_parts N).1
  have maskValue : (VG.Proof.Ffdh.ScalarWidth.mask N).setWidth 32=combLowMask h := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth,VG.Proof.Ffdh.ScalarWidth.mask_toNat,combLowMask,BitVec.toNat_ofNat]
    rfl
  have widthPositive := VG.Proof.Ffdh.ScalarWidth.width_pos N
  have widthBound : VG.Proof.Ffdh.ScalarWidth.width N≤1024 := by
    unfold VG.Proof.Ffdh.ScalarWidth.width
    omega
  have rowsBound : VG.Spec.Rsa.FixedBaseComb.rows N≤1639 := by
    unfold VG.Spec.Rsa.FixedBaseComb.rows VG.Spec.Rsa.FixedBaseComb.teeth
    omega
  rw [metadata,WP.seq_iff]
  refine WP.mono (combBitCount_ok s locals headPositive headBound (savedMask.trans maskValue)) ?_
  rintro u ⟨countU,_zeroU,memU,restU⟩
  rw [WP.seq_iff]
  refine WP.mono (combBitsSave_ok u (locals.after restU) widthPositive
    (by rw [restU.sp,memU]; exact savedWidth) countU) ?_
  rintro v ⟨countV,memV,frameV,restV⟩
  have parts := (VG.Proof.Ffdh.ScalarWidth.headBits_parts N).2
  change 8*(VG.Proof.Ffdh.ScalarWidth.width N-1)+h=N at parts
  rw [parts] at countV memV
  have rV : Rest combMetadataClobbers s v :=
    (restU.mono (by simp [combMetadataClobbers])).trans (restV.mono (by simp [combMetadataClobbers]))
  rw [restU.sp,memU] at memV frameV
  rw [WP.seq_iff]
  refine WP.mono (combRowsCount_ok v (locals.after rV) positive (by omega) countV) ?_
  rintro w ⟨_countW,memW,frameW,restW⟩
  have rW : Rest combMetadataClobbers s w := rV.trans (restW.mono (by simp [combMetadataClobbers]))
  rw [rV.sp] at memW frameW
  have localsFrame : Frame [⟨off (State.addr s.sp) 16,4⟩,⟨off (State.addr s.sp) 44,4⟩] s.mem w.mem :=
    (frameV.mono (by simp)).trans (frameW.mono (by simp))
  have localRead (slot : Nat) (sep16 : slot+4≤16 ∨ 20≤slot) (sep44 : slot+4≤44 ∨ 48≤slot)
      (fit : slot+4≤72) :
      w.mem.readW (off (State.addr w.sp) slot) 32=s.mem.readW (off (State.addr s.sp) slot) 32 := by
    rw [rW.sp]
    apply localsFrame.readW (r := ⟨off (State.addr s.sp) slot,4⟩) (Region.contains_self _ _) _ (by decide)
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact Offset.disjoint _ sep16 (by omega) (by decide)
    · exact Offset.disjoint _ sep44 (by omega) (by decide)
  have nSaved : w.mem.readW (off (State.addr w.sp) 16) 32=BitVec.ofNat 32 N := by
    rw [rW.sp]
    rw [frameW.readW (r := ⟨off (State.addr s.sp) 16,4⟩) (Region.contains_self _ _)
      (by intro r hr; rw [List.mem_singleton] at hr; subst r
          exact Offset.disjoint _ (by decide) (by decide) (by decide)) (by decide)]
    rw [memV,Mem.readW_writeW_self32]
  have dSaved : w.mem.readW (off (State.addr w.sp) 44) 32=BitVec.ofNat 32 (VG.Spec.Rsa.FixedBaseComb.rows N) := by
    rw [rW.sp,memW,Mem.readW_writeW_self32]
  refine WP.mono (combHeader_ok w (locals.after rW) (ws.after rW) (by rw [rW.sp]; exact separate)
    (by omega) (by omega) (by omega)
    ((localRead 4 (by decide) (by decide) (by decide)).trans savedCtx) nSaved
    ((localRead 20 (by decide) (by decide) (by decide)).trans savedWidth) dSaved) ?_
  rintro t ⟨memT,frameT,restT⟩
  rw [memW,memV] at memT
  refine ⟨memT,?_,rW.trans (restT.mono (by simp [combMetadataClobbers]))⟩
  exact (localsFrame.mono (by simp [combMetadataWrites])).trans (frameT.mono (by simp [combMetadataWrites]))

end VG.Proof.Ffdh.Arm
