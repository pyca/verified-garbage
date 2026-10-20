module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeyMask
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyMemory
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyOutputs
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset

/-! Finish a generated key with status 1 or 3 and mask both outputs without
branching on the secret result flag. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem keyMaskAll (b : Byte) : b &&& (255#8) = b := BitVec.and_allOnes

theorem keyFinishStatus_ok (s : State) {p : Inputs} {slots : List Nat} (accepted : Bool)
    (h : ArgumentMemory p slots s)
    (result : s.mem.readW (off (State.addr s.sp) 64) 32 = if accepted then 1 else 0) :
    WP isa (.block [.ldrSp .r3 64, .mov .r0 (.imm 3), .dp .sub .r0 .r0 (.shifted .r3 .lsl 1)]) s fun t =>
      (t.gpr .r0 = (if accepted then 1 else 3) ∧ t.mem = s.mem) ∧ Rest [.r0, .r3] s t := by
  have addr : State.addr (s.sp + BitVec.ofNat 32 64) = off (State.addr s.sp) 64 :=
    VG.Arm.addr_add (by have := h.locals.space.nowrap; omega)
  refine withRest [.r0, .r3] ?_ (by
    intro r hr i hi
    have checked : (instrs (.block [.ldrSp .r3 64, .mov .r0 (.imm 3),
      .dp .sub .r0 .r0 (.shifted .r3 .lsl 1)] : Prog isa)).all (fun i => !(clobbers i r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have f := List.all_eq_true.mp checked i hi
    cases hc : clobbers i r <;> simp_all) (by rfl)
  cases accepted <;> ffrun [addr, h.locals.read (d := 64) (by decide), result]

theorem keyFinish_ok (s : State) {p : Inputs} {slots : List Nat} (accepted : Bool)
    (h : ArgumentMemory p slots s) (saved : ∀ d ∈ slots, d + 4 ≤ 72)
    (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (outputs : KeyOutputs p s)
    (result : s.mem.readW (off (State.addr s.sp) 64) 32 = if accepted then 1 else 0) :
    WP isa VG.Impl.Ffdh.Arm.Domain.GenerateKey.finish s fun t =>
      t.gpr .r0 = (if accepted then 1 else 3) ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.privateValue) p.k =
        (if accepted then Spec.Rsa.bytesAt s.mem (State.addr p.privateValue) p.k else List.replicate p.k 0) ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.publicValue) p.k =
        (if accepted then Spec.Rsa.bytesAt s.mem (State.addr p.publicValue) p.k else List.replicate p.k 0) ∧
      Frame [⟨State.addr p.privateValue, p.k⟩, ⟨State.addr p.publicValue, p.k⟩] s.mem t.mem ∧
      Rest [.r0, .r1, .r2, .r3, .lr] s t := by
  rw [VG.Impl.Ffdh.Arm.Domain.GenerateKey.finish, WP.seq_iff]
  refine WP.mono (keyMask_ok s 40 h (by decide) h40 h32 result outputs.privateBuffer) ?_
  rintro u ⟨privateU, frameU, restU⟩
  change Frame [⟨State.addr p.privateValue, p.k⟩] s.mem u.mem at frameU
  have contextU := h.after_output frameU restU outputs.privateDomain outputs.privateStack saved
  have resultU : u.mem.readW (off (State.addr u.sp) 64) 32 = if accepted then 1 else 0 := by
    rw [restU.sp, frameU.readW (r := ⟨off (State.addr s.sp) 64, 4⟩) (Region.contains_self _ _)
      (by simpa using outputs.privateStack.sub_left (Offset.sub_base _ (by decide : 64 + 4 ≤ 72))) (by decide)]
    exact result
  rw [WP.seq_iff]
  refine WP.mono (keyMask_ok u 36 contextU (by decide) h36 h32 resultU (outputs.publicBuffer.after restU)) ?_
  rintro v ⟨publicV, frameV, restV⟩
  change Frame [⟨State.addr p.publicValue, p.k⟩] u.mem v.mem at frameV
  have contextV := contextU.after_output frameV restV outputs.publicDomain
    (by rw [restU.sp]; exact outputs.publicStack) saved
  have resultV : v.mem.readW (off (State.addr v.sp) 64) 32 = if accepted then 1 else 0 := by
    rw [restV.sp, frameV.readW (r := ⟨off (State.addr u.sp) 64, 4⟩) (Region.contains_self _ _)
      (by simpa only [restU.sp, List.mem_singleton, forall_eq] using
        outputs.publicStack.sub_left (Offset.sub_base _ (by decide : 64 + 4 ≤ 72))) (by decide)]
    exact resultU
  refine WP.mono (keyFinishStatus_ok v accepted contextV resultV) ?_
  rintro t ⟨⟨status, memT⟩, restT⟩
  have privateT := VG.Proof.Bignum.Arm.rsa_bytes_frame (k := p.k) frameV (by have := p.maxLength; omega)
    (by simpa using outputs.separate)
  have publicU := VG.Proof.Bignum.Arm.rsa_bytes_frame (k := p.k) frameU (by have := p.maxLength; omega)
    (by simpa using outputs.separate.symm)
  change Spec.Rsa.bytesAt u.mem (State.addr p.privateValue) p.k = _ at privateU
  change Spec.Rsa.bytesAt v.mem (State.addr p.publicValue) p.k = _ at publicV
  simp only [Inputs.slotValue] at privateU publicV
  rw [publicU] at publicV
  refine ⟨status, ?_, ?_, ?_, (restU.trans restV).trans (restT.mono (by simp))⟩
  · rw [memT, privateT, privateU]
    cases accepted <;> simp [Spec.Rsa.bytesAt, List.map_map, Function.comp_def, List.map_const', keyMaskAll]
  · rw [memT, publicV]
    cases accepted <;> simp [Spec.Rsa.bytesAt, List.map_map, Function.comp_def, List.map_const', keyMaskAll]
  · rw [memT]
    exact (frameU.mono (by simp)).trans (frameV.mono (by simp))

end VG.Proof.Ffdh.Arm
