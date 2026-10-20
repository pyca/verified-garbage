module

public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
import VerifiedGarbage.Proof.Ffdh.Arm.EntryStore
public import VerifiedGarbage.Proof.Ffdh.Arm.IncomingWord
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Ffdh.Arm.DomainPointers
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Proof.Ffdh.Arm.Context

/-! Retain the public precomputation ABI arguments in the existing FFDH frame. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure CombEntryRegs (p : Inputs) (s : State) : Prop where
  output : s.gpr .r0 = p.output
  domain : s.gpr .r2 = p.domain
  domainLength : s.gpr .r3 = BitVec.ofNat 32 p.dom.length
  stackBase : s.gpr .r12 = s.sp

theorem CombEntryRegs.after {p : Inputs} {s t : State}
    (h : CombEntryRegs p s) (rest : Rest [] s t) : CombEntryRegs p t :=
  ⟨(rest.gpr .r0 (by simp)).trans h.output,(rest.gpr .r2 (by simp)).trans h.domain,
    (rest.gpr .r3 (by simp)).trans h.domainLength,
    (rest.gpr .r12 (by simp)).trans (h.stackBase.trans rest.sp.symm)⟩

theorem combEntryArgs_ok (s : State) {p : Inputs}
    (h : ArgumentMemory p [] s)
    (incomingCount : IncomingWord (BitVec.ofNat 32 p.k) 128 s)
    (incomingBase : IncomingWord p.base 132 s)
    (output : s.gpr .r0 = p.output) (domain : s.gpr .r2 = p.domain)
    (domainLength : s.gpr .r3 = BitVec.ofNat 32 p.dom.length) :
    WP isa (.block VG.Impl.Ffdh.Arm.CombPrecompute.entryArgs) s fun t =>
      Context p [0,32,28,24,4] t ∧ Frame [⟨State.addr s.sp,72⟩] s.mem t.mem := by
  unfold VG.Impl.Ffdh.Arm.CombPrecompute.entryArgs VG.Impl.Ffdh.Arm.Domain.st
  refine wp_stackAddr (by decide) fun u moved => ?_
  have restU : Rest [.r12] s u := moved.rest (by simp)
  have argsU := h.of_mem moved.mem restU
  have frameU : Frame [⟨State.addr s.sp,72⟩] s.mem u.mem := by rw [moved.mem]; exact Frame.refl _ _
  have countU := incomingCount.after (by decide) frameU restU
  have baseU := incomingBase.after (by decide) frameU restU
  have regsU : CombEntryRegs p u :=
    ⟨(moved.other .r0 (by decide)).trans output,(moved.other .r2 (by decide)).trans domain,
      (moved.other .r3 (by decide)).trans domainLength,by rw [moved.gpr,moved.sp,BitVec.add_zero]⟩
  refine wp_store_arg .r0 4 argsU (by decide) (by decide) (by decide) regsU.output regsU.stackBase fun v argsV frameV restV => ?_
  have regsV := regsU.after restV
  have countV := countU.after (by decide) frameV restV
  have baseV := baseU.after (by decide) frameV restV
  rw [restU.sp] at frameV
  have fullV := frameU.trans frameV
  refine wp_store_arg .r2 24 argsV (by decide) (by decide) (by decide) regsV.domain regsV.stackBase fun w argsW frameW restW => ?_
  have regsW := regsV.after restW
  have countW := countV.after (by decide) frameW restW
  have baseW := baseV.after (by decide) frameW restW
  rw [restV.sp,restU.sp] at frameW
  have fullW := fullV.trans frameW
  refine wp_store_arg .r3 28 argsW (by decide) (by decide) (by decide) regsW.domainLength regsW.stackBase fun x argsX frameX restX => ?_
  have regsX := regsW.after restX
  have countX := countW.after (by decide) frameX restX
  have baseX := baseW.after (by decide) frameX restX
  rw [restW.sp,restV.sp,restU.sp] at frameX
  have fullX := fullW.trans frameX
  refine wp_retain_incoming .r3 (by decide) argsX (by decide) countX (by decide) (by decide) (by decide)
    regsX.stackBase fun y argsY frameY restY _ stackY => ?_
  have baseY := baseX.after (by decide) frameY restY
  rw [restX.sp,restW.sp,restV.sp,restU.sp] at frameY
  have fullY := fullX.trans frameY
  refine wp_retain_incoming .r0 (by decide) argsY (by decide) baseY (by decide) (by decide) (by decide)
    stackY fun t argsT frameT restT ptr _ => WP.block_nil ?_
  refine ⟨⟨argsT,ptr⟩,?_⟩
  rw [restY.sp,restX.sp,restW.sp,restV.sp,restU.sp] at frameT
  exact fullY.trans frameT

theorem combEntry_ok (s : State) {p : Inputs}
    (h : ArgumentMemory p [] s)
    (incomingCount : IncomingWord (BitVec.ofNat 32 p.k) 128 s)
    (incomingBase : IncomingWord p.base 132 s)
    (output : s.gpr .r0 = p.output) (domain : s.gpr .r2 = p.domain)
    (domainLength : s.gpr .r3 = BitVec.ofNat 32 p.dom.length) :
    WP isa (.block VG.Impl.Ffdh.Arm.CombPrecompute.entry) s fun t =>
      Context p [60,56,0,32,28,24,4] t ∧ Frame [⟨State.addr s.sp,72⟩] s.mem t.mem := by
  rw [VG.Impl.Ffdh.Arm.CombPrecompute.entry, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (withAllRest (combEntryArgs_ok s h incomingCount incomingBase output domain domainLength)) ?_
  rintro u ⟨⟨contextU,frameU⟩,restU⟩
  refine WP.mono (prepareArgs_ok u 24 contextU (by decide) (by decide) (by decide) (by decide)) ?_
  rintro v ⟨contextV,_,source,count,stack,frameV,restV⟩
  have narrowV : Frame [⟨State.addr s.sp,72⟩] u.mem v.mem := by
    apply frameV.sub
    intro r hr
    simp only [prepareWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    refine ⟨⟨State.addr s.sp,72⟩,by simp,?_⟩
    rcases hr with rfl | rfl
    · rw [restU.sp]; exact Offset.sub_base (State.addr s.sp) (d := 8) (n := 4) (k := 72) (by decide)
    · rw [restU.sp]; exact Offset.sub_base (State.addr s.sp) (d := 12) (n := 4) (k := 72) (by decide)
  have stackV : v.gpr .r12 = v.sp := stack.trans restV.sp.symm
  refine WP.mono (domainPointers_ok v contextV (by decide) source count stackV) ?_
  rintro t ⟨contextT,frameT,restT⟩
  refine ⟨contextT,frameU.trans (narrowV.trans ?_)⟩
  apply frameT.sub
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  refine ⟨⟨State.addr s.sp,72⟩,by simp,?_⟩
  rcases hr with rfl | rfl
  · rw [restV.sp,restU.sp]; exact Offset.sub_base (State.addr s.sp) (d := 56) (n := 4) (k := 72) (by decide)
  · rw [restV.sp,restU.sp]; exact Offset.sub_base (State.addr s.sp) (d := 60) (n := 4) (k := 72) (by decide)

end VG.Proof.Ffdh.Arm
