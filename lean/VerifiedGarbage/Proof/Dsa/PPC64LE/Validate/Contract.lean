module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Params.Front
public import VerifiedGarbage.Spec.Dsa.Prevalidated

/-!
# DSA public-key validation on PPC64LE: the contract on the registers

`vkContract`: `vg_dsa_validate_public_key(key = r3, key_len = r4, p_len = r5,
q_len = r6, scratch = r7, scratch_len = r8)`, `pcContract`'s registers with
the packed key p||q||g||y in place of the domain.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE

/-- `vg_dsa_validate_public_key`, on the registers. -/
def vkContract : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let scr : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat * 8⟩
    s.rd = [key] ∧ s.wr = [scr] ∧ key.Disjoint scr ∧
      (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64 ∧ (s.gpr .r7).toNat + (s.gpr .r8).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Dsa.lengthsValid (s.gpr .r5).toNat (s.gpr .r6).toNat ∧
      (s.gpr .r4).toNat = 3 * (s.gpr .r5).toNat + (s.gpr .r6).toNat ∧
      Spec.Dsa.scratchWords (s.gpr .r5).toNat ≤ (s.gpr .r8).toNat
  post s t :=
    ((t.gpr .r3).setWidth 32).toNat = if Spec.Dsa.validatePublicKeyBytes (s.gpr .r5).toNat (s.gpr .r6).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat) then 1 else 0
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
      Spec.Dsa.publicBytesLeak (s₁.gpr .r5).toNat (s₁.gpr .r6).toNat
          (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r3) (s₁.gpr .r4).toNat) =
        Spec.Dsa.publicBytesLeak (s₂.gpr .r5).toNat (s₂.gpr .r6).toNat
          (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r3) (s₂.gpr .r4).toNat)

theorem vkContract_lay {s : State} (h : vkContract.pre s) : (playOf s).Ok :=
  playOf_ok_of h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.2

end VG.Proof.Dsa.PPC64LE
