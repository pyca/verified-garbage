import VerifiedGarbage.Proof.Ecdsa.X86.CombStagesCT

/-! # Constant time of the signing body with a fixed-base comb -/
namespace VG.Proof.Ecdsa.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

/-- Static tables remain readable and outside scratch throughout setup. -/
def CombTables (s : State) : Prop :=
  TblMem s ((s.gpr .eax).setWidth 64) (p256Comb.combWords p256d) ∧
  ∀ i < (p256Comb.combWords p256d).length, ∀ b < 8,
    size ≤ ofs (ptr s 4) ((s.gpr .eax).setWidth 64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b)

theorem signCombBody_rel (hc : CfgOk p256Comb) (hC : Law p256Comb.C)
    (hT : CombTbls p256Comb) (hd : CombOk p256Comb p256d) (ham3 : AM3 p256Comb.C)
    {s₀ t₀ : State} {extra₁ extra₂ : List Region}
    (hp : Pre p256Comb s₀ extra₁) (hq : Pre p256Comb t₀ extra₂)
    (ht₁ : CombTables s₀) (ht₂ : CombTables t₀)
    (he : s₀.gpr .esp = t₀.gpr .esp) (ha : ∀ j < 5, arg s₀ j = arg t₀ j)
    (hg : s₀.gpr .eax = t₀.gpr .eax) :
    RelCT isa (fun s t => s = s₀ ∧ t = t₀) (p256Comb.signWithMul p256Comb.gMul) (fun _ _ => True) := by
  have prep := signPrep_rel.mono (P' := fun s t => s = s₀ ∧ t = t₀)
    (fun _ _ h => by
      rcases h with ⟨rfl, rfl⟩
      exact argAgree (argWf _ hp rfl rfl) (argWf _ hq rfl rfl)
        (fun r hr => by rw [List.mem_singleton.mp hr]; exact he) he ha)
    (fun _ _ _ => trivial)
  have prep' := prep.wp
    (F₁ := fun s => St₁ p256Comb .sign s₀ (ptr s₀ 4) s)
    (F₂ := fun t => St₁ p256Comb .sign t₀ (ptr t₀ 4) t)
    (fun _ _ h => by
      rcases h with ⟨rfl, rfl⟩
      exact ⟨stage₁ hc hp.setup (fun _ h => WP.block_nil h),
        stage₁ hc hq.setup (fun _ h => WP.block_nil h)⟩)
  have hCo : ∀ d, p256Comb.comb = some d → CombOk p256Comb d := by
    intro d h
    have e : p256d = d := Option.some.inj h
    rw [← e]; exact hd
  have multCT : RelCT isa (fun s t => True ∧
      St₁ p256Comb .sign s₀ (ptr s₀ 4) s ∧ St₁ p256Comb .sign t₀ (ptr t₀ 4) t)
      p256Comb.gMul (fun _ _ => True) := by
    intro s t tr₁ tr₂ s' t' h e₁ e₂
    obtain ⟨_, S, T⟩ := h
    have tb₁ := ht₁.1.of_unch (by rw [S.rd, S.wr]) S.whole
      (fun w hw => by rw [List.mem_singleton.mp hw]; exact Nat.le_refl _) ht₁.2
    have tb₂ := ht₂.1.of_unch (by rw [T.rd, T.wr]) T.whole
      (fun w hw => by rw [List.mem_singleton.mp hw]; exact Nat.le_refl _) ht₂.2
    have hb : ptr s₀ 4 = ptr t₀ 4 := congrArg (BitVec.setWidth 64) (ha 4 (by decide))
    have T' := T
    rw [← hb] at T'
    exact gMul_rel hc hC hT hd ham3 S.scr T'.scr S.fixed T'.fixed
      (S.k ▸ wordsVal_lt _ _ _ _) (T'.k ▸ wordsVal_lt _ _ _ _) S.t₀ T'.t₀ tb₁ tb₂ ht₁.2 hg
      (keepCombWf hp S.toKeep) (keepCombWf hq T.toKeep)
      (by rw [S.wr, T.wr, hp.wr, hq.wr]; simp only [outR, scR, ptr, ha 0 (by decide), ha 4 (by decide)])
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  have functional : ∀ {u₀ u : State}, CombTables u₀ →
      St₁ p256Comb .sign u₀ (ptr u₀ 4) u →
      WP isa p256Comb.gMul u (Keep p256Comb u₀ (ptr u₀ 4)) := by
    intro u₀ u ht S
    refine WP.mono (gMul_ok' hc hC hT hCo ham3 S.scr S.fixed
      (S.k ▸ wordsVal_lt _ _ _ _) S.rx S.ry S.rz S.t₀ ?_) fun _ h => S.toKeep.gMul hc h.1 h.2.1
    intro d h
    have e : p256d = d := Option.some.inj h
    subst d
    exact ⟨ht.1.of_unch (by rw [S.rd, S.wr]) S.whole
      (fun w hw => by rw [List.mem_singleton.mp hw]; exact Nat.le_refl _) ht.2, ht.2⟩
  have mult := multCT.wp (F₁ := fun s => Keep p256Comb s₀ (ptr s₀ 4) s)
    (F₂ := fun t => Keep p256Comb t₀ (ptr t₀ 4) t)
    (fun _ _ h => ⟨functional ht₁ h.2.1, functional ht₂ h.2.2⟩)
  exact prep'.seq (mult.seq (signTail_rel.mono
    (fun _ _ h => keepScratchAgree hp hq h.2.1 h.2.2 he ha) (fun _ _ _ => trivial)))

end VG.Proof.Ecdsa.X86
