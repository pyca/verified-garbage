import VerifiedGarbage.Proof.Scrypt.X86_64.FusedCT
namespace VG.Proof.Scrypt.X86_64.BlockMix.Fused
open VG VG.X86_64
theorem blockMix_correct (s : State) (hs : Proof.Scrypt.blockMixX86_64.pre s) :
    ∃ t s', Exec isa Impl.Scrypt.X86_64.blockMixFused s t s' ∧ abiPreserved s s' ∧
      Proof.Scrypt.blockMixX86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct (pre_of hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩

theorem blockMix_ct : ConstantTime isa Proof.Scrypt.blockMixX86_64.pre
    Proof.Scrypt.blockMixX86_64.pub Impl.Scrypt.X86_64.blockMixFused := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  exact (blockMix_rel (pre_of h₁) (pre_of h₂) (pubEq_of hpub) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem blockMix_verified :
    Verified X86_64.target Impl.Scrypt.X86_64.blockMixFused (Spec.Scrypt.blockMixContract X86_64.abi 8) :=
  Verified.of_correct blockMix_correct blockMix_ct
    { pre := by
        sig_implies_pre [Spec.Scrypt.blockMixContract, Spec.Scrypt.blockMixSig,
          Proof.Scrypt.blockMixX86_64, X86_64.abi, X86_64.argRegs]
      post := by
        sig_implies_post [Spec.Scrypt.blockMixContract, Spec.Scrypt.blockMixSig,
          Proof.Scrypt.blockMixX86_64, X86_64.abi, X86_64.argRegs]
      pub := by
        sig_implies_pub [Spec.Scrypt.blockMixContract, Spec.Scrypt.blockMixSig,
          Proof.Scrypt.blockMixX86_64, X86_64.abi, X86_64.argRegs]
      sat := by
        sig_implies_sat [Spec.Scrypt.blockMixContract, Spec.Scrypt.blockMixSig,
          Proof.Scrypt.blockMixX86_64, X86_64.abi, X86_64.argRegs,
          Proof.Scrypt.X86_64.BlockMix.satState]
          [Proof.Scrypt.X86_64.BlockMix.satState] using Proof.Scrypt.X86_64.BlockMix.satState }

end VG.Proof.Scrypt.X86_64.BlockMix.Fused
