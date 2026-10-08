import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombInput

namespace VG.Proof.Ecdsa.Verify.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86

theorem vPoints_rel (hc : CfgOk p256Comb) (hC : Law p256Comb.C)
    (hT : CombTbls p256Comb) (hd : CombOk p256Comb p256d) (ham3 : AM3 p256Comb.C)
    {s₀ t₀ : State} {extra₁ extra₂ : List Region}
    (hp : VPre p256Comb s₀ extra₁) (hq : VPre p256Comb t₀ extra₂)
    (ht₁ : VCombTables s₀) (ht₂ : VCombTables t₀)
    (he : s₀.gpr .esp = t₀.gpr .esp) (ha : ∀ j < 4, arg s₀ j = arg t₀ j)
    (hg : s₀.gpr .eax = t₀.gpr .eax) (hspG : SpOk p256Comb.gMul 20) :
    RelCT isa (fun s t => Mid p256Comb s₀ (ptr s₀ 3) s ∧ Mid p256Comb t₀ (ptr t₀ 3) t)
      (Impl.Ecdsa.Verify.X86.Cfg.pointsComb p256Comb) (fun _ _ => True) := by
  have hspG' : SpOk p256Comb.gMul p256Comb.stk := ⟨hspG.1, Nat.le_trans hspG.2 (Cfg.stk_ge _)⟩
  have hsp20 : ∀ {u₀ u : State} {extra : List Region}, VPre p256Comb u₀ extra →
      Keep p256Comb u₀ (ptr u₀ 3) u → 20 ≤ (u.gpr .esp).toNat := fun hp k => by
    rw [k.esp]; exact Nat.le_trans (Cfg.stk_ge _) hp.sp_lo
  have bits := vBits_rel.mono
    (P' := fun s t => Mid p256Comb s₀ (ptr s₀ 3) s ∧ Mid p256Comb t₀ (ptr t₀ 3) t)
    (fun _ _ h => vKeepArgAgree hp hq h.1.keep h.2.keep he ha) (fun _ _ _ => trivial)
  have bits' := bits.wp (F₁ := VCombInput p256Comb s₀ (ptr s₀ 3))
    (F₂ := VCombInput p256Comb t₀ (ptr t₀ 3)) (by
      intro s t h
      change WP isa vBitsCode s (VCombInput p256Comb s₀ (ptr s₀ 3)) ∧
        WP isa vBitsCode t (VCombInput p256Comb t₀ (ptr t₀ 3))
      exact ⟨vBits_ok hc h.1, vBits_ok hc h.2⟩)
  have hCo : ∀ d, p256Comb.comb = some d → CombOk p256Comb d := by
    intro d h; have e : p256d = d := Option.some.inj h; rw [← e]; exact hd
  have multCT : RelCT isa (fun s t => True ∧
      VCombInput p256Comb s₀ (ptr s₀ 3) s ∧ VCombInput p256Comb t₀ (ptr t₀ 3) t)
      p256Comb.gMul (fun _ _ => True) := by
    intro s t tr₁ tr₂ s' t' h e₁ e₂
    obtain ⟨_, S, T⟩ := h
    obtain ⟨tb₁, ap₁⟩ := vTables_keep ht₁ S.toKeep
    obtain ⟨tb₂, ap₂⟩ := vTables_keep ht₂ T.toKeep
    have hb : ptr s₀ 3 = ptr t₀ 3 := congrArg (BitVec.setWidth 64) (ha 3 (by decide))
    have T' := T
    rw [← hb] at T'
    obtain ⟨k₁, hk₁, b₁⟩ := S.scalar
    obtain ⟨k₂, hk₂, b₂⟩ := T'.scalar
    exact gMul_rel hc hC hT hd ham3 S.scr T'.scr S.fixed T'.fixed
      hk₁ hk₂ b₁ b₂ tb₁ tb₂ ht₁.2.1 ap₁ ap₂ (hsp20 hp S.toKeep) (hsp20 hq T.toKeep) hg
      (vKeepCombWf hp S.toKeep) (vKeepCombWf hq T.toKeep)
      (by rw [S.wr, T.wr, hp.wr, hq.wr]; simp only [ptr, ha 3 (by decide)])
      (by rw [S.esp, T.esp, he])
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  have functional : ∀ {u₀ u : State} {extra : List Region}, VPre p256Comb u₀ extra → VCombTables u₀ →
      VCombInput p256Comb u₀ (ptr u₀ 3) u →
      WP isa p256Comb.gMul u (Keep p256Comb u₀ (ptr u₀ 3)) := by
    intro u₀ u extra hp ht S
    obtain ⟨k, hk, b⟩ := S.scalar
    refine S.toKeep.withSp hspG' (WP.mono (gMul_ok' hc hC hT hCo ham3 S.scr S.fixed
      hk S.rx S.ry S.rz b ?_ (hsp20 hp S.toKeep) hspG) fun _ h f => S.toKeep.gMul hc h.1 h.2.1 f)
    intro d h
    have e : p256d = d := Option.some.inj h
    subst d
    obtain ⟨tb, ap⟩ := vTables_keep ht S.toKeep
    exact ⟨tb, ht.2.1, ap⟩
  have mult := multCT.wp (F₁ := Keep p256Comb s₀ (ptr s₀ 3))
    (F₂ := Keep p256Comb t₀ (ptr t₀ 3))
    (fun _ _ h => ⟨functional hp ht₁ h.2.1, functional hq ht₂ h.2.2⟩)
  exact bits'.seq (mult.seq (vPointTail_rel.mono
    (fun _ _ h => vKeepScratchAgree hp hq h.2.1 h.2.2 he ha) (fun _ _ _ => trivial)))

theorem vCombBody_rel (hc : CfgOk p256Comb) (hC : Law p256Comb.C)
    (hT : CombTbls p256Comb) (hd : CombOk p256Comb p256d) (ham3 : AM3 p256Comb.C)
    {s₀ t₀ : State} {extra₁ extra₂ : List Region}
    (hp : VPre p256Comb s₀ extra₁) (hq : VPre p256Comb t₀ extra₂)
    (ht₁ : VCombTables s₀) (ht₂ : VCombTables t₀)
    (he : s₀.gpr .esp = t₀.gpr .esp) (ha : ∀ j < 4, arg s₀ j = arg t₀ j)
    (hg : s₀.gpr .eax = t₀.gpr .eax) (hspG : SpOk p256Comb.gMul 20)
    (hsp : SpOk (Impl.Ecdsa.Verify.X86.Cfg.verifyCombBody p256Comb) p256Comb.stk) :
    RelCT isa (fun s t => s = s₀ ∧ t = t₀) (Impl.Ecdsa.Verify.X86.Cfg.verifyCombBody p256Comb)
      (fun _ _ => True) := by
  have H := VCSp.of hsp
  have front := vFront_rel.mono (P' := fun s t => s = s₀ ∧ t = t₀)
    (fun _ _ h => by
      rcases h with ⟨rfl, rfl⟩
      exact vFrontAgree hp hq he ha)
    (fun _ _ _ => trivial)
  have front' := front.wp (F₁ := Front p256Comb s₀ (ptr s₀ 3))
    (F₂ := Front p256Comb t₀ (ptr t₀ 3)) (fun _ _ h => by
      rcases h with ⟨rfl, rfl⟩
      exact ⟨front_ok hc hp H.validate (fun _ h => WP.block_nil h),
        front_ok hc hq H.validate (fun _ h => WP.block_nil h)⟩)
  have mid := vMid_rel.mono
    (P' := fun s t => True ∧ Front p256Comb s₀ (ptr s₀ 3) s ∧ Front p256Comb t₀ (ptr t₀ 3) t)
    (fun _ _ h => vKeepScratchAgree hp hq h.2.1.keep h.2.2.keep he ha) (fun _ _ _ => trivial)
  have mid' := mid.wp (F₁ := Mid p256Comb s₀ (ptr s₀ 3))
    (F₂ := Mid p256Comb t₀ (ptr t₀ 3)) (fun _ _ h =>
      ⟨mid_ok hc h.2.1 H.scalars H.nPow H.uv (fun _ h => WP.block_nil h),
        mid_ok hc h.2.2 H.scalars H.nPow H.uv (fun _ h => WP.block_nil h)⟩)
  have pts := (vPoints_rel hc hC hT hd ham3 hp hq ht₁ ht₂ he ha hg hspG).mono
    (P' := fun s t => True ∧ Mid p256Comb s₀ (ptr s₀ 3) s ∧ Mid p256Comb t₀ (ptr t₀ 3) t)
    (fun _ _ h => h.2) (fun _ _ _ => trivial)
  have hCo : ∀ d, p256Comb.comb = some d → CombOk p256Comb d := by
    intro d h; have e : p256d = d := Option.some.inj h; rw [← e]; exact hd
  have pts' := pts.wp (F₁ := Keep p256Comb s₀ (ptr s₀ 3)) (F₂ := Keep p256Comb t₀ (ptr t₀ 3))
    (fun _ _ h => ⟨vPoints_keep hc hC hT hCo ham3 ht₁ h.2.1 hspG H.points,
      vPoints_keep hc hC hT hCo ham3 ht₂ h.2.2 hspG H.points⟩)
  exact front'.seq (mid'.seq (pts'.seq (vFinal_rel.mono
    (fun _ _ h => vKeepScratchAgree hp hq h.2.1 h.2.2 he ha) (fun _ _ _ => trivial))))

end VG.Proof.Ecdsa.Verify.X86
