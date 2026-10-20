module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Tape
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Bounds
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Geometry
import VerifiedGarbage.Proof.Framework.Arm.CallF

/-! The nested attempt's buffers and private stack satisfy its shared signature. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
open VG VG.Arm VG.Proof.Mont VG.Spec.Ffdh

abbrev rCallArgs (p : KeyPublic) : Region := ⟨State.addr (callSp p), 28⟩

structure CallFacts (p : KeyPublic) (used : Nat) : Prop where
  stackFits : 128 ≤ (callSp p).toNat
  argsFit : (callSp p).toNat + 28 ≤ 2 ^ 32
  xy : (rX p).Disjoint (rY p)
  xd : (rX p).Disjoint (rDomain p)
  xr : (rX p).Disjoint (rTape p used)
  xs : (rX p).Disjoint (rScratch p)
  xa : (rX p).Disjoint (rCallArgs p)
  yd : (rY p).Disjoint (rDomain p)
  yr : (rY p).Disjoint (rTape p used)
  ys : (rY p).Disjoint (rScratch p)
  ya : (rY p).Disjoint (rCallArgs p)
  ds : (rDomain p).Disjoint (rScratch p)
  rs : (rTape p used).Disjoint (rScratch p)
  sa : (rScratch p).Disjoint (rCallArgs p)
  stack : ∀ r ∈ [rX p, rY p, rDomain p, rTape p used, rScratch p, rCallArgs p],
    (rCallStack p).Disjoint r
  xFit : p.xp.toNat + p.len ≤ 2 ^ 32
  yFit : p.yp.toNat + p.len ≤ 2 ^ 32
  domainFit : p.dp.toNat + p.dlen ≤ 2 ^ 32
  tapeFit : (p.rp + BitVec.ofNat 32 used).toNat + p.len ≤ 2 ^ 32
  scratchFit : p.scratch.toNat + p.capacity * 8 ≤ 2 ^ 32
  length : pLenValid p.len
  domainLength : domainLenValid p.len p.dlen
  scratch : Spec.Rsa.scratchWords p.len ≤ p.capacity
  lenFits : p.len < 2 ^ 32
  domainLenFits : p.dlen < 2 ^ 32
  capacityFits : p.capacity < 2 ^ 32

theorem KeyInput.callFacts {p : KeyPublic} {original : State} {used : Nat}
    (h : KeyInput p original) (room : used + p.len ≤ p.randLen) : CallFacts p used := by
  have fit : 184 ≤ p.sp.toNat := h.bounds.stackFits
  have callNat : (callSp p).toNat = p.sp.toNat - 56 :=
    FrameStack.sub_toNat' (by omega : 56 ≤ p.sp.toNat)
  have rootWrite (r : Region) (hr : r ∈ [rX p, rY p, rScratch p]) : r ∈ original.wr := by
    rw [h.write_regions]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl <;> simp
  have rootRead (r : Region) (hr : r ∈ [rDomain p, rRandom p]) : r ∈ original.rd := by
    rw [h.read_regions]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl <;> simp
  have cross (w : Region) (hw : w ∈ [rX p, rY p, rScratch p])
      (r : Region) (hr : r ∈ [rDomain p, rRandom p]) : w.Disjoint r :=
    h.layout.separate w (by rw [← h.layout.wr]; exact rootWrite w hw)
      r (by rw [← h.layout.rd]; exact rootRead r hr)
  have tape := h.tape_sub room
  have argsSub : (rCallArgs p).Sub (FrameStack.belowA p.sp stackUse) :=
    fun a ha => (arguments_sub h.bounds.stackFits) a (Region.sub_prefix (by decide : 28 ≤ 32) a ha)
  have stackSub := callStack_sub h.bounds.stackFits
  have stackWrite (r : Region) (hr : r ∈ [rX p, rY p, rScratch p]) :
      (FrameStack.belowA p.sp stackUse).Disjoint r :=
    h.stack_separate (List.mem_append_left _ (rootWrite r hr))
  have stackRead (r : Region) (hr : r ∈ [rDomain p, rRandom p]) :
      (FrameStack.belowA p.sp stackUse).Disjoint r :=
    h.stack_separate (List.mem_append_right _ (rootRead r hr))
  have geometry := h.output_regions_disjoint
  refine ⟨by rw [callNat]; omega, by rw [callNat]; have := p.sp.isLt; omega,
    geometry.1, cross _ (by simp) _ (by simp), (cross _ (by simp) _ (by simp)).sub_right tape,
    geometry.2.1, (stackWrite _ (by simp)).symm.sub_right argsSub,
    cross _ (by simp) _ (by simp), (cross _ (by simp) _ (by simp)).sub_right tape,
    geometry.2.2.1, (stackWrite _ (by simp)).symm.sub_right argsSub,
    (cross _ (by simp) _ (by simp)).symm, ((cross _ (by simp) _ (by simp)).sub_right tape).symm,
    (stackWrite _ (by simp)).symm.sub_right argsSub, ?_, h.bounds.xFit, h.bounds.yFit,
    h.bounds.domainFit, h.tape_fits room, by simpa only [Nat.mul_comm] using h.bounds.scratchFit,
    ⟨h.bounds.minLength, h.bounds.maxLength⟩, h.bounds.domainLength, h.bounds.scratchSpace,
    by have := h.bounds.maxLength; omega, ?_, h.bounds.capacityFits⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (stackWrite _ (by simp)).sub_left stackSub
    · exact (stackWrite _ (by simp)).sub_left stackSub
    · exact (stackRead _ (by simp)).sub_left stackSub
    · exact ((stackRead _ (by simp)).sub_left stackSub).sub_right tape
    · exact (stackWrite _ (by simp)).sub_left stackSub
    · have enough : 128 ≤ (callSp p).toNat := by rw [callNat]; omega
      rw [rCallStack, FrameStack.belowA, FrameStack.addr_sub' enough]
      exact (Offset.base_disjoint_below _ (by decide : 128 + 28 ≤ 2 ^ 64)).symm
  · have lengths := h.bounds.domainLength
    have maxLength := h.bounds.maxLength
    unfold domainLenValid at lengths
    rcases lengths with eq | eq <;> omega

end VG.Proof.Ffdh.Arm.KeySearch
