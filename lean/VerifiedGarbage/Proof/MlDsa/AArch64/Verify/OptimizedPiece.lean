import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedTimingBase

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Call

structure Piece (p : Params) (S : Nat) (I J : State → State → Prop) (c : Prog isa) : Prop where
  ok : ∀ σ s, vPre p S σ → I σ s → WP isa c s (J σ)
  tr : RelCT isa (RootPair p S I) c fun _ _ => True

section
variable {p : Params} {S : Nat} {I J K : State → State → Prop}

theorem Piece.seq {c₁ c₂ : Prog isa} (h₁ : Piece p S I J c₁) (h₂ : Piece p S J K c₂) :
    Piece p S I K (.seq c₁ c₂) :=
  ⟨fun σ s hp hs => WP.seq (WP.mono (h₁.ok σ s hp hs) fun s' h => h₂.ok σ s' hp h),
    RelCT.seq (rootPair_progress h₁.ok h₁.tr) h₂.tr⟩

theorem Piece.mono {c : Prog isa} {I' J' : State → State → Prop} (h : Piece p S I J c)
    (hI : ∀ σ s, vPre p S σ → I' σ s → I σ s) (hJ : ∀ σ s, vPre p S σ → J σ s → J' σ s) :
    Piece p S I' J' c :=
  ⟨fun σ s hp hs => WP.mono (h.ok σ s hp (hI σ s hp hs)) fun s' h => hJ σ s' hp h,
    RelCT.mono h.tr (fun _ _ ⟨⟨σ₁, σ₂, p₁, p₂, pub, i₁, i₂⟩,et⟩ => ⟨⟨σ₁, σ₂, p₁, p₂, pub, hI _ _ p₁ i₁, hI _ _ p₂ i₂⟩,et⟩)
      fun _ _ h => h⟩

theorem Piece.seqR {f : Nat → Prog isa} {I : Nat → State → State → Prop} :
    ∀ (n a : Nat), (∀ k, a ≤ k → k < a + n → Piece p S (I k) (I (k + 1)) (f k)) →
      Piece p S (I a) (I (a + n)) (seqR f a n)
  | n, a, h =>
    ⟨fun σ s hp hs => seqR_ok (I := fun k => I k σ) n a (fun k h₁ h₂ s hs => (h k h₁ h₂).ok σ s hp hs) s hs,
      RelCT.mono (seqR_tr (Q := fun k => RootPair p S (I k)) n a fun k h₁ h₂ => rootPair_progress (h k h₁ h₂).ok (h k h₁ h₂).tr)
        (fun _ _ h => h) fun _ _ _ => trivial⟩

theorem Piece.ifOk {c : Prog isa} {T : State → Prop} [DecidablePred T]
    (hx : ∀ σ s, vPre p S σ → I σ s → s.gpr .x24 = if T σ then 1 else 0)
    (hT : ∀ σ₁ σ₂, vPre p S σ₁ → vPre p S σ₂ → vPub p S σ₁ σ₂ → (T σ₁ ↔ T σ₂))
    (ht : Piece p S (fun σ s => I σ s ∧ T σ) J c) (he : ∀ σ s, vPre p S σ → I σ s → ¬ T σ → J σ s) :
    Piece p S I J (ifOk c) := by
  have ev : ∀ σ s, vPre p S σ → I σ s → isa.eval (.nonzero .x .x24) s = some (decide (T σ)) := fun σ s hp hs => by
    rw [eval24, hx σ s hp hs]; by_cases h : T σ <;> simp [h]
  refine ⟨fun σ s hp hs => WP.ite (decide (T σ)) (ev σ s hp hs) (fun hb => ht.ok σ s hp ⟨hs, of_decide_eq_true hb⟩)
    fun hb => WP.block_nil (he σ s hp hs (of_decide_eq_false hb)), relIte ?_ ?_ ?_⟩
  · rintro x y ⟨⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩,et⟩
    rw [ev σ₁ x p₁ h₁, ev σ₂ y p₂ h₂, decide_eq_decide.mpr (hT σ₁ σ₂ p₁ p₂ pub)]
  · refine RelCT.mono ht.tr (fun x y ⟨⟨⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩,et⟩, hc⟩ => ?_) fun _ _ h => h
    rw [ev σ₁ x p₁ h₁] at hc
    have t₁ : T σ₁ := of_decide_eq_true (Option.some.inj hc)
    exact ⟨⟨σ₁, σ₂, p₁, p₂, pub, ⟨h₁, t₁⟩, h₂, (hT σ₁ σ₂ p₁ p₂ pub).mp t₁⟩,et⟩
  · exact RelCT.block_nil fun _ _ _ => trivial

end

theorem Piece.of_vpiece {p : Params} {S : Nat} {I J : State→State→Prop} {c : Prog isa}
    (h : VPiece p S I J c) : Piece p S I J c :=
  ⟨h.ok, h.tr.mono (fun _ _ h=>h.1) (fun _ _ h=>h)⟩

end VG.Proof.MlDsa.AArch64.Verify.Optimized
