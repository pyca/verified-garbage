module

public import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingABIPre
import VerifiedGarbage.Proof.Dsa.X86_64.PublicSlices
import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingCT
import VerifiedGarbage.Proof.Bignum.Octets

/-! # Only the verifying ABI's declared public observations determine its schedule -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem verifyingLayout_eq {p₁ p₂ : VerifyingInput} {s₁ s₂ : State}
    {hp₁ : s₁.gpr .rdx = BitVec.ofNat 64 p₁.pLen} {hp₂ : s₂.gpr .rdx = BitVec.ofNat 64 p₂.pLen}
    {hq₁ : s₁.gpr .rcx = BitVec.ofNat 64 p₁.qLen} {hq₂ : s₂.gpr .rcx = BitVec.ofNat 64 p₂.qLen}
    (hb : p₁.base = p₂.base) (hp : p₁.pLen = p₂.pLen) (hq : p₁.qLen = p₂.qLen)
    (hd : p₁.digestPointer = p₂.digestPointer) (hdl : p₁.digest.length = p₂.digest.length)
    (hpb : p₁.components.p = p₂.components.p) (hqb : p₁.components.q = p₂.components.q)
    (hdi : s₁.gpr .rdi = s₂.gpr .rdi) (hdx : s₁.gpr .rdx = s₂.gpr .rdx)
    (h8 : s₁.gpr .r8 = s₂.gpr .r8) (hcx : s₁.gpr .rcx = s₂.gpr .rcx) :
    p₁.layout s₁ hp₁ hq₁ = p₂.layout s₂ hp₂ hq₂ := by
  have hac : p₁.accepted = p₂.accepted := by
    unfold VerifyingInput.accepted
    congr 1
  have hprefix : p₁.prefixLength = p₂.prefixLength := by
    unfold VerifyingInput.prefixLength
    rw [hdl, hqb]
  have hfields : verifyFieldValues s₁ p₁.digestPointer
      (BitVec.ofNat 64 p₁.digest.length) (BitVec.ofNat 64 p₁.prefixLength) p₁.accepted =
      verifyFieldValues s₂ p₂.digestPointer
      (BitVec.ofNat 64 p₂.digest.length) (BitVec.ofNat 64 p₂.prefixLength) p₂.accepted := by
    funext f
    cases f <;> simp only [verifyFieldValues, hd, hdl, hprefix, hac, hdi, hdx, h8, hcx]
  unfold VerifyingInput.layout
  congr 1
  · exact congrArg Spec.Dsa.decodeBE hpb
  · exact congrArg Spec.Dsa.decodeBE hqb

theorem verifyingAgreement {s₁ s₂ : State} (h₁ : VerifyingABI s₁) (h₂ : VerifyingABI s₂)
    (hdi : s₁.gpr .rdi = s₂.gpr .rdi) (hdx : s₁.gpr .rdx = s₂.gpr .rdx)
    (h8 : s₁.gpr .r8 = s₂.gpr .r8) (hcx : s₁.gpr .rcx = s₂.gpr .rcx)
    (hsp : s₁.gpr .rsp = s₂.gpr .rsp)
    (a0 : stackArg s₁ 0 = stackArg s₂ 0) (a1 : stackArg s₁ 1 = stackArg s₂ 1)
    (a2 : stackArg s₁ 2 = stackArg s₂ 2)
    (hpub : h₁.input.key.take (3 * h₁.input.pLen + h₁.input.qLen) =
      h₂.input.key.take (3 * h₂.input.pLen + h₂.input.qLen)) : VerifyingAgrees h₂.call h₁.call := by
  have hp : h₁.input.pLen = h₂.input.pLen := congrArg BitVec.toNat hdx
  have hq : h₁.input.qLen = h₂.input.qLen := congrArg BitVec.toNat hcx
  have hdl : h₁.input.digest.length = h₂.input.digest.length := by
    change (Spec.Rsa.bytesAt _ _ _).length = (Spec.Rsa.bytesAt _ _ _).length
    rw [bytesAt_length, bytesAt_length, a1]
  rw [← hp, ← hq] at hpub
  have hpb : h₁.input.components.p = h₂.input.components.p := by
    have he := prefix_component_eq (offset := 0) (len := h₁.input.pLen) hpub (by omega)
    simp only [List.drop_zero] at he
    change h₁.input.key.take h₁.input.pLen = h₂.input.key.take h₂.input.pLen
    rw [← hp]
    exact he
  have hqb : h₁.input.components.q = h₂.input.components.q := by
    have he := prefix_component_eq (offset := h₁.input.pLen) (len := h₁.input.qLen) hpub (by omega)
    change (h₁.input.key.drop h₁.input.pLen).take h₁.input.qLen = (h₂.input.key.drop h₂.input.pLen).take h₂.input.qLen
    rw [← hp, ← hq]
    exact he
  exact ⟨verifyingLayout_eq a2 hp hq a0 hdl hpb hqb hdi hdx h8 hcx, hpb, hqb, hdl, hsp⟩

theorem verifyingPublicRelated {s₁ s₂ : State} (h₁ : VerifyingABI s₁) (h₂ : VerifyingABI s₂)
    (h : (Spec.Dsa.verifyContract abi).pub s₁ s₂) : Two VerifyingStart s₁ s₂ := by
  sig_pub [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argRegs, stackArgs_four] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, hdi, _, hdx, hcx, h8, _, a0, a1, a2, _⟩ := h
  have hpub := (List.append_inj' hl (List.length_singleton.trans List.length_singleton.symm)).1
  have hb := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hpub
  exact ⟨h₂.call, ⟨h₁.call, verifyingAgreement h₁ h₂ hdi hdx h8 hcx hsp a0 a1 a2 hb, rfl⟩,
    ⟨h₂.call, ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩⟩

theorem verifyingConstantTime (M : Mont) (Sq : MontS) : ConstantTime isa (Spec.Dsa.verifyContract abi).pre
    (Spec.Dsa.verifyContract abi).pub (SignVerify.verify Sq.mm M.mm) := by
  intro s₁ s₂ trace₁ trace₂ t₁ t₂ h₁ h₂ hp e₁ e₂
  exact (verifyingMain_ct M Sq _ _ _ _ _ _ (verifyingPublicRelated (verifyingABI_of h₁) (verifyingABI_of h₂) hp) e₁ e₂).1

end VG.Proof.Dsa.X86_64
