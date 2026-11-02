module

public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeState
public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeOut
import VerifiedGarbage.Proof.Ffdh.Arm.IncomingWord
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Serialize the existing RSA modulus/R-squared prefix into the comb context. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Rsa.Mont (numAt)

theorem montgomeryOutArgs_ok (s : State) {p : Inputs} {sp : BitVec 32} (h : Memory p sp s) :
    WP isa (.block [.ldrSp .r4 4,.dp .add .r4 .r4 (.imm 24)]) s fun t =>
      (t.gpr .r4 = p.output + BitVec.ofNat 32 24 ∧ t.gpr .r0 = p.base ∧ t.mem = s.mem) ∧ Rest roundClobbers s t := by
  have addr : State.addr (s.sp+BitVec.ofNat 32 4) = off (State.addr s.sp) 4 := addr_add (by have := h.context.locals.space.nowrap; omega)
  have read := h.context.locals.read (d:=4) (by decide)
  have saved := h.context.saved 4 (by simp [slots])
  change s.mem.readW (off (State.addr s.sp) 4) 32 = p.output at saved
  have ptr := h.context.ptr
  apply withAllRest
  ffrun [addr,read,saved,ptr]
  rfl

theorem montgomeryOut_ok (s : State) {p : Inputs} {sp : BitVec 32} (h : Memory p sp s) :
    WP isa VG.Impl.Ffdh.Arm.CombPrecompute.montgomeryOut s fun t =>
      Memory p sp t ∧ WorkspaceEq (State.addr p.base) (8*p.len) s.mem t.mem ∧
      Spec.Rsa.wordsAt t.mem (off (State.addr p.output) 24) (2*p.w) =
        Spec.Rsa.toWords (numAt s.mem (State.addr p.base) p.w 0) p.w ++
        Spec.Rsa.toWords (numAt s.mem (State.addr p.base) p.w 4) p.w ∧
      Frame [⟨off (State.addr p.output) 24,16*p.w⟩] s.mem t.mem ∧
      WorkspaceEq (State.addr p.output) 24 s.mem t.mem ∧ Rest roundClobbers s t := by
  have size : 24+16*p.w ≤ bytes p := by
    simp only [bytes,Spec.Ffdh.generationPrecomputedWords,Spec.Rsa.FixedBaseComb.precomputedWords,
      Spec.Rsa.precomputedWords,Spec.Rsa.FixedBaseComb.entries]
    change 24+16*p.w ≤ 8*(3+(2*p.w+32*p.w))
    omega
  have pos := p.width.1
  have bounded : 24+16*p.w ≤ 2^32 := by have := h.output.fits; omega
  have dstAddr : State.addr (p.output+BitVec.ofNat 32 24) = off (State.addr p.output) 24 :=
    addr_add (by have := h.output.fits; omega)
  have dstNat : (p.output+BitVec.ofNat 32 24).toNat = p.output.toNat+24 := by
    rw [BitVec.toNat_add]
    change (p.output.toNat+24) % 2^32 = _
    exact Nat.mod_eq_of_lt (by have := h.output.fits; omega)
  have prefixSub : (⟨off (State.addr p.output) 24,16*p.w⟩ : Region).Sub ⟨State.addr p.output,bytes p⟩ := Offset.sub_base _ size
  rw [VG.Impl.Ffdh.Arm.CombPrecompute.montgomeryOut,WP.seq_iff]
  refine WP.mono (montgomeryOutArgs_ok s h) ?_
  rintro u ⟨⟨dst,ptr,memU⟩,restU⟩
  rw [WP.seq_iff]
  refine WP.mono (precomputeOut_ok (w:=p.w) u (h.context.workspace.congr restU.wr)
    (by rw [memU]; exact h.ready.layout) (by simpa only [memU] using h.ready.width)
    (by rw [dstNat]; have := h.output.fits; omega)
    (by rw [restU.wr,dstAddr]; exact CallLay.inRegions_sub h.output.writable (by omega) (by have := h.output.fits; omega))
    (by rw [dstAddr]; exact h.workspaceSeparate.sub_right prefixSub) ptr dst) ?_
  rintro v ⟨_,value,frameV,restV⟩
  rw [memU,dstAddr] at value frameV
  have restSV := restU.trans restV
  have whole : Frame [⟨State.addr p.output,bytes p⟩] s.mem v.mem := frameV.sub (by
    intro r hr
    have eq := List.mem_singleton.mp hr
    subst r
    exact ⟨_,List.mem_cons_self,prefixSub⟩)
  have localSeparate : (⟨State.addr s.sp,72⟩ : Region).Disjoint ⟨off (State.addr p.output) 24,16*p.w⟩ := by
    rw [h.fixed]
    exact h.localSeparate.sub_right prefixSub
  have saved0 := h.context.saved 0 (by simp [slots])
  change s.mem.readW (off (State.addr s.sp) 0) 32 = p.base at saved0
  have incoming : IncomingWord p.base 0 v := by
    refine ⟨?_,?_,?_⟩
    · rw [restSV.sp]; have := h.context.locals.space.nowrap; omega
    · rw [restSV.sp,restSV.rd,restSV.wr]; exact h.context.locals.read (by decide)
    · rw [restSV.sp,frameV.readW (r:=⟨off (State.addr s.sp) 0,4⟩) (Region.contains_self _ _) (by
        intro r hr
        have eq := List.mem_singleton.mp hr
        subst r
        exact localSeparate.sub_left (Offset.sub_base _ (d:=0) (n:=4) (k:=72) (by decide))) (by decide)]
      exact saved0
  refine wp_load_incoming .r0 incoming (by decide) fun t ptrT memT restT => WP.block_nil ?_
  have rest := restSV.trans (restT.mono (by simp [roundClobbers]))
  have frame : Frame [⟨off (State.addr p.output) 24,16*p.w⟩] s.mem t.mem := by rw [memT]; exact frameV
  have wholeT : Frame [⟨State.addr p.output,bytes p⟩] s.mem t.mem := by rw [memT]; exact whole
  have next := h.after_external wholeT rest ptrT
  refine ⟨next.1,next.2,by rw [memT]; exact value,frame,?_,rest⟩
  apply WorkspaceEq.of_frame (by decide) frame
  intro r hr
  have eq := List.mem_singleton.mp hr
  subst r
  exact (Offset.disjoint_base _ (by decide) (by omega : 24+16*p.w ≤ 2^64)).symm

end VG.Proof.Ffdh.Arm.CombBuilder
