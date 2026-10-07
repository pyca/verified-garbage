import VerifiedGarbage.Proof.RsaPss.X86_64.PrecomputedCtCall

namespace VG.Proof.RsaPss.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.Rsa.X86_64 (PublicImpl)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)

variable {H : Hash} (impl : PublicImpl) (hH : HashOK H) (K : Callees H) (lk : MgfLink H hH)
  (hc : PssChecks H.P H.D)

include K hc in
theorem main_ct :
    RelCT isa (Two fun a t => At (G := lk.G) (J7 H) a t ∧ isa.eval .b t = some false) (Impl.RsaPss.X86_64.Precomputed.main H impl.name impl.code)
      (Two (At (G := lk.G) (JR H))) := by
  unfold Impl.RsaPss.X86_64.Precomputed.main
  simp only [seqs]
  exact RelCT.assoc (dbPub_ct.seq ((call_ct impl).seq (acc0_ct.seq ((mgf_ct hH K lk hc.hash1).seq
    (clearTop_ct.seq (posScan_ct.seq ((posCheck_ct hH hc.verify).seq (RelCT.assoc ((cyd_ct hH lk hc.verify).seq
      ((copyDb_ct hH hc.verify).seq ((shift_ct hH hc.verify).seq ((verifyNb_ct hH hc.verify).seq
        ((mhash_ct hH K hc.hash1).seq (cmpH_ct hH hc.verify))))))))))))))

include K hc in
theorem body_ct : RelCT isa (Two (At (G := lk.G) J0)) (Impl.RsaPss.X86_64.Precomputed.body H impl.name impl.code) fun _ _ => True := by
  unfold Impl.RsaPss.X86_64.Precomputed.body
  simp only [seqs]
  refine pro_ct.seq ((two_ite (fun a t₁ t₂ ⟨s₁, S₁, h₁⟩ ⟨s₂, S₂, h₂⟩ => by
      rw [show isa.eval .e t₁ = t₁.zf from rfl, show isa.eval .e t₂ = t₂.zf from rfl, h₁.2.2.2.2, h₂.2.2.2.2,
        S₁.n0v, S₂.n0v])
    (fail_ct (Φ := fun a t => At (G := lk.G) (J1 H) a t ∧ isa.eval .e t = some true)
      fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, _, S, h.1⟩) (RelCT.assoc ((emLen_ct hc.verify hH).seq
      (two_ite (fun a t₁ t₂ ⟨s₁, S₁, h₁⟩ ⟨s₂, S₂, h₂⟩ => by
          rw [show isa.eval .b t₁ = t₁.cf from rfl, show isa.eval .b t₂ = t₂.cf from rfl, h₁.2.2.2.2, h₂.2.2.2.2,
            S₁.veml, S₂.veml])
        (fail_ct (Φ := fun a t => At (G := lk.G) (J4 H) a t ∧ isa.eval .b t = some true)
          fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, _, S, h.1⟩)
        (anyArgs_ct.seq ((salt_ct hc.verify hH).seq (two_ite (fun a t₁ t₂ ⟨s₁, S₁, h₁⟩ ⟨s₂, S₂, h₂⟩ => by
            rw [show isa.eval .b t₁ = t₁.cf from rfl, show isa.eval .b t₂ = t₂.cf from rfl, h₁.2.2.2.2.1,
              h₂.2.2.2.2.1, S₁.veml, S₂.veml, S₁.vrdx, S₂.vrdx])
          (fail_ct (Φ := fun a t => At (G := lk.G) (J7 H) a t ∧ isa.eval .b t = some true)
            fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, _, S, h.1⟩)
          (main_ct impl hH K lk hc)))))))).seq restore_ct)

include K hc in
theorem code_ct : ConstantTime isa (contract lk.G).pre (contract lk.G).pub
    (Impl.RsaPss.X86_64.Precomputed.code H impl.name impl.code) := by
  apply RelCT.constantTime
  apply valloc
  apply (body_ct impl hH K lk hc).mono
  · rintro _ _ ⟨s₁, s₂, ⟨h₁, h₂, hpub⟩, e₁, e₂⟩
    have p₁ := pre_of lk.G h₁
    have p₂ := pre_of lk.G h₂
    exact ⟨s₁, ⟨s₁, ⟨p₁.toVPre, vpub_refl lk.G s₁, p₁.toVPre, p₁, p₁, rfl, rfl, rfl⟩, e₁⟩,
      ⟨s₂, ⟨p₁.toVPre, hpub.1, p₂.toVPre, p₁, p₂, hpub.2.1.symm, hpub.2.2.1.symm, hpub.2.2.2.symm⟩, e₂⟩⟩
  · exact fun _ _ h => h

include K hc in
theorem verified : Verified X86_64.target
    (Impl.RsaPss.X86_64.Precomputed.code H impl.name impl.code)
    (Spec.RsaPss.verifyPrecomputedContract lk.G lk.G abi verifyStack) :=
  Verified.of_correct (k := contract lk.G) (code_correct hH K lk impl)
    (code_ct impl hH K lk hc) (implies lk.G lk.mem)

end VG.Proof.RsaPss.X86_64.Pc
