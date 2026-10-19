module

public import VerifiedGarbage.Proof.Rsa.X86.PrivFnInput

/-! # The wrapper preserves its caller's return address -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked VG.Proof.Bignum.X86

theorem popped_four_value (s : State) :
    (popped .ebx 4 s).gpr .ebx = s.mem.readW ((s.gpr .esp + 12).setWidth 64) 32 := by
  change s.mem.readW ((((s.gpr .esp + 4) + 4) + 4).setWidth 64) 32 = _
  simp only [BitVec.add_assoc]
  rfl

theorem PrivFnInput.returnWord {g : PrivGeometry} {bs : Fin 8 → List Byte} {s t : State}
    (h : PrivFnInput g bs s) (frame : Frame (bodyWrites g) (entered s).mem t.mem) :
    t.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32 := by
  have low : 16 ≤ (s.gpr .esp).toNat := by have := h.stackFit; unfold stackBytes at this; omega
  have savedFrame := pushed_frame (rs := savedRegisters) (s := s) (by decide) low
  have contains : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Contains ((s.gpr .esp).setWidth 64) (32 / 8) :=
    Region.contains_self _ _
  have savedSeparate : ∀ r ∈ [below (s.gpr .esp) 16],
      (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint r := by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    unfold below
    rw [Taint.sub_setWidth low]
    have eq : (s.gpr .esp).setWidth 64 =
        (s.gpr .esp).setWidth 64 - 16 + BitVec.ofNat 64 16 := (BitVec.sub_add_cancel _ _).symm
    have sep := Offset.disjoint_base ((s.gpr .esp).setWidth 64 - 16)
      (by decide : 16 ≤ 16) (by decide : 16 + 4 ≤ 2 ^ 64)
    rw [← eq] at sep
    exact sep
  exact (frame.readW contains h.returnSeparate (by decide)).trans
    (savedFrame.readW contains savedSeparate (by decide))
end VG.Proof.Rsa.X86.PrivChecked
