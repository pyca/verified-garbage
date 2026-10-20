module
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckCall
import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawMemory
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ValidateLayout
import VerifiedGarbage.Proof.Dsa.X86.Generation.ValidatePre

/-! # Invoke the existing verified domain checker from its isolated argument frame -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout

def validateWrites (G : GenerationGeometry) : List Region := [G.part domainCheck (128 * G.pLen), below G.frame 60]
def validateResult (G : GenerationGeometry) (mem : Mem) : Bool :=
  Spec.Dsa.checkParametersBytes G.pLen G.qLen (Spec.Rsa.bytesAt mem (off G.base packed) (2 * G.pLen + G.qLen))

theorem validateEntry_bytes {G : GenerationGeometry} {s : State} (sp : s.gpr .esp = G.frame - 24#32) :
    Spec.Rsa.bytesAt s.callEntry.mem (off G.base packed) (2 * G.pLen + G.qLen) =
      Spec.Rsa.bytesAt s.mem (off G.base packed) (2 * G.pLen + G.qLen) := by
  have O : Frame [⟨(s.gpr .esp - 4).setWidth 64, 4⟩] s.mem s.callEntry.mem := by
    rw [State.callEntry_mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 4)
  have address : (s.gpr .esp - 4).setWidth 64 = (G.frame - 28#32).setWidth 64 := by rw [sp]; congr 1; bv_omega
  rw [address] at O
  exact drawFrame_bytes O (by
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact G.stack_slice_apart (by decide : 4 ≤ 28) (by decide : 28 ≤ 128) (validate_packed_room G))
    (by have := G.width; have := G.qWidth; omega)

theorem validateCall_ok (F : KeyRandom.CheckCall.CheckFn) {G : GenerationGeometry} {s : State}
    (sp : s.gpr .esp = G.frame - 24#32) (slots : ValidateSlots G s)
    (read : Covers (validateRd G ++ validateWr G) (s.rd ++ s.wr)) (write : Covers (validateWr G) s.wr) :
    WP isa (.call F.name F.code) s fun t =>
      t.gpr .eax = (if validateResult G s.mem then 1 else 0) ∧
      Frame (validateWrites G) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx] s t := by
  have stack := G.stackSize
  have bound := G.frame.isLt
  have sn : (s.gpr .esp).toNat = G.frame.toNat - 24 := by rw [sp]; exact sub_toNat (by omega)
  have depth := F.depth
  have pw := G.width
  have qw := G.qWidth
  refine WP.call F.verified.1 F.noSp (by omega) (validate_pre sp slots) read write
    fun t rd wr saved O _ ⟨s₂, _, regs, post⟩ => ?_
  have K : Keeps [.eax, .ecx, .edx] s t := ⟨by
    intro r hr
    apply saved r
    cases r <;> first | decide | exact False.elim (hr (by decide)), rd, wr⟩
  have frame : Frame (validateWrites G) s.mem t.mem := O.sub (by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · simp only [validateWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨below G.frame 60, by simp [validateWrites],
          below_sub (by decide : 24 ≤ 60) (by omega)⟩
    · obtain rfl := List.mem_singleton.mp hr
      rw [sp]
      exact ⟨below G.frame 60, by simp [validateWrites], below_inner (by omega) (by omega)⟩)
  refine ⟨?_, frame, K⟩
  sig_post [Spec.Dsa.checkParametersContract, Spec.Dsa.checkParametersSig, abi, argSlots, argVal, argBytes, stackBelow] at post
  simp only [validate_arg sp slots (validateRd G) (validateWr G) (show 0 < 6 by decide),
    validate_arg sp slots (validateRd G) (validateWr G) (show 1 < 6 by decide),
    validate_arg sp slots (validateRd G) (validateWr G) (show 2 < 6 by decide),
    validate_arg sp slots (validateRd G) (validateWr G) (show 3 < 6 by decide), validateValue,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : G.pLen < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : G.qLen < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : 2 * G.pLen + G.qLen < 2 ^ 32)] at post
  have entryBytes := validateEntry_bytes sp
  rw [State.callEntry_mem] at entryBytes
  rw [G.pointer_addr (by unfold packed usedBytes domainCheck; omega), entryBytes,
    BitVec.setWidth_append_eq_right, regs .eax (by decide)] at post
  apply BitVec.eq_of_toNat_eq
  change (t.gpr .eax).toNat = _
  rw [post]
  change (if validateResult G s.mem then 1 else 0) = _
  cases validateResult G s.mem <;> rfl
end VG.Proof.Dsa.X86.Generation
