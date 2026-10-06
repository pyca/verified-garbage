import VerifiedGarbage.Proof.Rsa.AArch64.PrivCallees

/-!
# The interface `RsaPrivateCrt` on AArch64

What a variant of `RsaPrivateCrt` on AArch64 is (see `TCB/Emit.lean`): an
implementation of `vg_rsa_private_crt`, and the implementations of
`vg_rsa_public_precompute` and `vg_rsa_public_precomputed_checked` that
`vg_rsa_private_checked` checks its result with, each verified against its
shared contract with no stack (none has a frame, so each runs in the stack
its caller's call leaves).
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64

/-- An implementation of `vg_rsa_private_crt`, with the public operation
that checks it. -/
structure CrtImpl where
  /-- Its symbol and code. -/
  name : String
  code : Prog isa
  verified : Verified AArch64.target code (Spec.Rsa.privateCrtContract AArch64.abi 0)
  noFrames : code.noFrames = true
  /-- `vg_rsa_public_precompute` (`pc`) and
  `vg_rsa_public_precomputed_checked` (`pd`), by their symbols. -/
  pcName : String
  pc : Prog isa
  pcVerified : Verified AArch64.target pc (Spec.Rsa.publicPrecomputeContract AArch64.abi 0)
  pcNoFrames : pc.noFrames = true
  pdName : String
  pd : Prog isa
  pdVerified : Verified AArch64.target pd (Spec.Rsa.publicPrecomputedCheckedContract AArch64.abi 0)
  pdNoFrames : pd.noFrames = true
  /-- What the names of `vg_rsa_private_checked`'s instances end with (e.g.
  `_neon`; nothing for the baseline implementation). -/
  suffix : String
  /-- The CPU features its code and that of the public operation require,
  which `vg_rsa_private_checked` requires too. -/
  features : List String

namespace CrtImpl

variable (v : CrtImpl)

theorem crt_ok (s : State) (h : crtA.pre s) : ∃ t s', Exec isa v.code s t s' ∧ abiPreserved s s' ∧ crtA.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := v.verified.1 s (crt_pre h)
  exact ⟨t, s', he, ha, crt_post hp⟩

theorem crt_ct : ConstantTime isa crtA.pre crtA.pub v.code :=
  fun _ _ _ _ _ _ h₁ h₂ hp e₁ e₂ => v.verified.2.1 _ _ _ _ _ _ (crt_pre h₁) (crt_pre h₂) (crt_pub hp) e₁ e₂

theorem pc_ok (s : State) (h : pcA.pre s) : ∃ t s', Exec isa v.pc s t s' ∧ abiPreserved s s' ∧ pcA.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := v.pcVerified.1 s (pc_pre h)
  exact ⟨t, s', he, ha, pc_post hp⟩

theorem pc_ct : ConstantTime isa pcA.pre pcA.pub v.pc :=
  fun _ _ _ _ _ _ h₁ h₂ hp e₁ e₂ => v.pcVerified.2.1 _ _ _ _ _ _ (pc_pre h₁) (pc_pre h₂) (pc_pub hp) e₁ e₂

theorem pd_ok (s : State) (h : pdA.pre s) : ∃ t s', Exec isa v.pd s t s' ∧ abiPreserved s s' ∧ pdA.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := v.pdVerified.1 s (pd_pre h)
  exact ⟨t, s', he, ha, pd_post hp⟩

theorem pd_ct : ConstantTime isa pdA.pre pdA.pub v.pd :=
  fun _ _ _ _ _ _ h₁ h₂ hp e₁ e₂ => v.pdVerified.2.1 _ _ _ _ _ _ (pd_pre h₁) (pd_pre h₂) (pd_pub hp) e₁ e₂

end CrtImpl

end VG.Proof.Rsa.AArch64
