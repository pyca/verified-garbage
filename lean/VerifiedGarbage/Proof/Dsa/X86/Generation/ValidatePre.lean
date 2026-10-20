module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ValidateLayout
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Spec.Dsa.Derive
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryBuffers

/-! # The isolated outgoing frame satisfies the registered domain checker's ABI -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout

theorem validate_arg {G : GenerationGeometry} {s : State}
    (sp : s.gpr .esp = G.frame - 24#32) (slots : ValidateSlots G s) (rd wr : List Region) {i : Nat} (hi : i < 6) :
    X86.arg (s.callEntry.withRegions rd wr) i = validateValue G i := by
  have stack := G.stackSize
  have bound := G.frame.isLt
  have sn : (s.gpr .esp).toNat = G.frame.toNat - 24 := by rw [sp]; exact sub_toNat (by omega)
  rw [arg_withRegions, arg_callEntry (by omega) (by omega)]
  have address : (s.gpr .esp + BitVec.ofNat 32 (4 * i)).setWidth 64 = off (validateArgsBase G) (4 * i) := by
    rw [show (s.gpr .esp + BitVec.ofNat 32 (4 * i)).setWidth 64 = off ((s.gpr .esp).setWidth 64) (4 * i)
      from addr_eq (by omega), sp]
    rfl
  rw [address]
  exact slots i hi

theorem validate_pre {G : GenerationGeometry} {s : State}
    (sp : s.gpr .esp = G.frame - 24#32) (slots : ValidateSlots G s) :
    (Spec.Dsa.checkParametersContract abi 32).pre (s.callEntry.withRegions (validateRd G) (validateWr G)) := by
  have pw := G.width
  have qw := G.qWidth
  have stack := G.stackSize
  have bound := G.frame.isLt
  have sn : (s.gpr .esp).toNat = G.frame.toNat - 24 := by rw [sp]; exact sub_toNat (by omega)
  have pl : G.pLen < 2 ^ 32 := by omega
  have ql : G.qLen < 2 ^ 32 := by omega
  have total : 2 * G.pLen + G.qLen < 2 ^ 32 := by omega
  have scratch : 16 * G.pLen < 2 ^ 32 := by omega
  have packedStart : packed < usedBytes G.pLen := by unfold packed usedBytes domainCheck; omega
  have scratchStart : domainCheck < usedBytes G.pLen := by unfold usedBytes; omega
  have ha : argAddr (s.callEntry.withRegions (validateRd G) (validateWr G)) 0 = validateArgsBase G := by
    rw [argAddr_withRegions, argAddr_callEntry, sp]
    simp only [Nat.mul_zero, BitVec.add_zero, validateArgsBase]
  have hs : (s.gpr .esp - 4).setWidth 64 = (G.frame - 28#32).setWidth 64 := by rw [sp]; congr 1; bv_omega
  have hl : (G.frame - 28#32).setWidth 64 - 32#64 = (G.frame - 60#32).setWidth 64 := by
    rw [Taint.sub_setWidth (by omega : 28 ≤ G.frame.toNat), Taint.sub_setWidth (by omega : 60 ≤ G.frame.toNat)]
    bv_omega
  have wlo : 32 ≤ (s.gpr .esp - 4).toNat := by
    have eq : (s.gpr .esp - 4).toNat = (s.gpr .esp).toNat - 4 := sub_toNat (k := 4) (by omega)
    rw [eq]; omega
  have whi : (s.gpr .esp - 4).toNat + 4 + 24 ≤ 2 ^ 32 := by
    have eq : (s.gpr .esp - 4).toNat = (s.gpr .esp).toNat - 4 := sub_toNat (k := 4) (by omega)
    rw [eq]; omega
  have pr := validate_packed_room G
  have sr := validate_scratch_room G
  have pa := G.stack_slice_apart (depth := 24) (len := 24) (Nat.le_refl _) (by decide) pr
  have sa := G.stack_slice_apart (depth := 24) (len := 24) (Nat.le_refl _) (by decide) sr
  have pret := G.stack_slice_apart (depth := 28) (len := 4) (by decide) (by decide) pr
  have sret := G.stack_slice_apart (depth := 28) (len := 4) (by decide) (by decide) sr
  have plow := G.stack_slice_apart (depth := 60) (len := 32) (by decide) (by decide) pr
  have slow := G.stack_slice_apart (depth := 60) (len := 32) (by decide) (by decide) sr
  have ps := G.parts_disjoint pr sr (.inl (by unfold packed domainCheck; omega))
  have retarg : (⟨(G.frame - 28#32).setWidth 64, 4⟩ : Region).Disjoint ⟨validateArgsBase G, 24⟩ := by
    apply Offset.disjoint_of_le
    · change ((G.frame - 28#32).setWidth 64).toNat + 4 ≤ ((G.frame - 24#32).setWidth 64).toNat
      rw [G.stack_toNat (by decide : 28 ≤ 128), G.stack_toNat (by decide : 24 ≤ 128)]; omega
    · change ((G.frame - 24#32).setWidth 64).toNat + 24 ≤ 2 ^ 64
      rw [G.stack_toNat (by decide : 24 ≤ 128)]; omega
  have lowarg : (⟨(G.frame - 60#32).setWidth 64, 32⟩ : Region).Disjoint ⟨validateArgsBase G, 24⟩ := by
    apply Offset.disjoint_of_le
    · change ((G.frame - 60#32).setWidth 64).toNat + 32 ≤ ((G.frame - 24#32).setWidth 64).toNat
      rw [G.stack_toNat (by decide : 60 ≤ 128), G.stack_toNat (by decide : 24 ≤ 128)]; omega
    · change ((G.frame - 24#32).setWidth 64).toNat + 24 ≤ 2 ^ 64
      rw [G.stack_toNat (by decide : 24 ≤ 128)]; omega
  have pb := G.pointer_fit packedStart pr
  have sb := G.pointer_fit scratchStart sr
  have scrWords : Spec.Dsa.scratchWords G.pLen ≤ 16 * G.pLen := Nat.le_refl _
  have ps' := ps.symm
  have pa' := pa.symm
  have sa' := sa.symm
  have pret' := pret.symm
  have sret' := sret.symm
  have plow' := plow.symm
  have slow' := slow.symm
  dsimp only [GenerationGeometry.part] at pa sa pret sret plow slow ps ps' pa' sa' pret' sret' plow' slow'
  dsimp only [validateArgsBase] at retarg lowarg
  sig_pre [Spec.Dsa.checkParametersContract, Spec.Dsa.checkParametersSig, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [validate_arg sp slots (validateRd G) (validateWr G) (show 0 < 6 by decide),
    validate_arg sp slots (validateRd G) (validateWr G) (show 1 < 6 by decide),
    validate_arg sp slots (validateRd G) (validateWr G) (show 2 < 6 by decide),
    validate_arg sp slots (validateRd G) (validateWr G) (show 3 < 6 by decide),
    validate_arg sp slots (validateRd G) (validateWr G) (show 4 < 6 by decide),
    validate_arg sp slots (validateRd G) (validateWr G) (show 5 < 6 by decide),
    validateValue, BitVec.toNat_ofNat, Nat.mod_eq_of_lt pl, Nat.mod_eq_of_lt ql,
    Nat.mod_eq_of_lt total, Nat.mod_eq_of_lt scratch, G.pointer_addr packedStart, G.pointer_addr scratchStart,
    ha, hs, hl, show 16 * G.pLen * 8 = 128 * G.pLen by omega]
  sig_and_intros
  all_goals try dsimp only [validateArgsBase]
  all_goals first
    | exact rfl
    | exact True.intro
    | exact validate_lengths G
    | with_reducible assumption
end VG.Proof.Dsa.X86.Generation
