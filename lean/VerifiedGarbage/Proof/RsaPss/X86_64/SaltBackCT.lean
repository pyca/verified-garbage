import VerifiedGarbage.Proof.RsaPss.X86_64.FixedSaltCT

/-! Constant-time public dispatch for PSS salt verification. -/
namespace VG.Proof.RsaPss.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)

variable {G : Spec.Mgf1.Hash} {H : Hash} {extra : State → State → Prop}

/-- Testing the public salt mode preserves the verification state. -/
theorem saltAny_ct : RelCT isa (Two (VAt (extra := extra) G (JM H (X7 H))))
    (.block [.mov .rax (.mem (sp sAny)), .alu .test .rax (.reg .rax)])
    (Two fun a t => VAt (extra := extra) G (JM H (X7 H)) a t ∧
      isa.eval .e t = some (decide (vw H a 35 = 0))) := by
  refine two_post (vtwo (G := G) (H := H) [35] [] (fun _ => [])
    (fun a t h => jm_vs h _) (fun _ => rfl) (by decide) (by taint_decide))
    fun a t ⟨s, S, v, hrd, hok⟩ => ?_
  obtain ⟨V, W, R, hw, _⟩ := v.W
  refine WP.mono (WP.keep [.rax] (Q := fun u => u.mem = t.mem ∧
    u.zf = some (decide (W 35 = 0))) ?_ rfl) fun u ⟨⟨hm, hz⟩, ku⟩ => ?_
  · xrun [ea_sp, v.L.rsp, v.L.ld (d := sAny) (by decide), R.rd (d := sAny) 35 rfl (by decide)]
    rw [BitVec.and_self]
    rfl
  · refine ⟨⟨s, S, v.keep ku hm (by decide) (fun _ hp => by cases hp), ku.2.1.trans hrd, hok⟩, ?_⟩
    change u.zf = _
    rw [hz, hw 35 (by decide), S.vw]

/-- The bound on the requested length is public too. -/
theorem saltLen_ct : RelCT isa (Two (VAt (extra := extra) G (JM H (X7 H))))
    (.block [.mov .rax (.mem (sp sSlen)), .alu .cmp .rax (.mem (sp sDb))])
    (Two fun a t => VAt (extra := extra) G (JM H (X7 H)) a t ∧
      isa.eval .b t = some (decide ((stackArg a 1).toNat < vdb H.D a))) := by
  refine two_post (vtwo (G := G) (H := H) [24, 36] [] (fun _ => [])
    (fun a t h => jm_vs h _) (fun _ => rfl) (by decide) (by taint_decide))
    fun a t ⟨s, S, v, hrd, hok⟩ => ?_
  obtain ⟨V, W, R, hw, _⟩ := v.W
  have hk2 := S.ps.k2
  refine WP.mono (WP.keep [.rax] (Q := fun u => u.mem = t.mem ∧
    u.cf = some (decide ((stackArg s 1).toNat < vdb H.D s))) ?_ rfl) fun u ⟨⟨hm, hz⟩, ku⟩ => ?_
  · xrun [ea_sp, v.L.rsp, v.L.ld (d := sSlen) (by decide), v.L.ld (d := sDb) (by decide),
      R.rd (d := sSlen) 36 rfl (by decide), R.rd (d := sDb) 24 rfl (by decide),
      hw 36 (by decide), hw 24 (by decide)]
    simp only [vw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show vdb H.D s < 2 ^ 64 by unfold vdb veml; omega)]
  · refine ⟨⟨s, S, v.keep ku hm (by decide) (fun _ hp => by cases hp), ku.2.1.trans hrd, hok⟩, ?_⟩
    change u.cf = _
    rw [hz, S.arg1, S.vdb]

variable (hH : HashOK H) (K : Callees H) (lk : MgfLink H hH)

include hH K in
theorem genericSaltBack_ct (hc : PssChecks H.P H.D) :
    RelCT isa (Two (VAt (extra := extra) lk.G (JM H (X7 H)))) (genericSaltBack H)
      (Two (VAt (extra := extra) lk.G (JR H))) :=
  RelCT.assoc ((cyd_ct hH lk hc.verify).seq ((copyDb_ct hH hc.verify).seq
    ((shift_ct hH hc.verify).seq ((verifyNb_ct hH hc.verify).seq
      ((mhash_ct hH K hc.hash1).seq (cmpH_ct hH hc.verify))))))

include hH K in
theorem saltBack_ct (hc : PssChecks H.P H.D) :
    RelCT isa (Two (VAt (extra := extra) lk.G (JM H (X7 H)))) (saltBack H)
      (Two (VAt (extra := extra) lk.G (JR H))) := by
  have generic := genericSaltBack_ct (extra := extra) hH K lk hc
  have fixed := fixedSaltBack_ct (extra := extra) hH K lk hc
  unfold saltBack
  refine saltAny_ct.seq (two_ite (fun a t₁ t₂ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_
    (generic.mono (fun _ _ => two_mono fun _ _ h => h.1.1) fun _ _ h => h))
  refine (saltLen_ct.seq (two_ite (fun a t₁ t₂ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_
    (generic.mono (fun _ _ => two_mono fun _ _ h => h.1.1) fun _ _ h => h))).mono
    (fun _ _ => two_mono fun _ _ h => h.1.1) (fun _ _ h => h)
  refine fixed.mono (fun _ _ => two_mono fun a t ⟨⟨⟨s, S, h⟩, hz⟩, hb⟩ => ?_) fun _ _ h => h
  have hf : (stackArg a 1).toNat < vdb H.D a := by
    rw [hz, Option.some.injEq, decide_eq_true_eq] at hb
    exact hb
  exact ⟨s, S, h, by rwa [S.arg1, S.vdb]⟩

end VG.Proof.RsaPss.X86_64
