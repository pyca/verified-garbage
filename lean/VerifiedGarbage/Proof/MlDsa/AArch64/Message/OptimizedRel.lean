import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Rel
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.OptimizedCall

namespace VG.Proof.MlDsa.AArch64.Message.Optimized
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message

abbrev MovedS (as : List (Reg × Arg)) (t u : State) : Prop := Moved as t u ∧ u.syms=t.syms

variable {I : Lay → Mem → Mem → Prop}
theorem call_tr {Φ : Lay → Mem → State → Prop} {as : List (Reg × Arg)} (hok : argsOk as = true) {n : String}
    {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (rd wr : Lay → List Region)
    (hpre : ∀ (L : Lay) g v m₀ (t t1 : State), L.Ok → Ctx L g v m₀ t → Φ L m₀ t → MovedS as t t1 →
      k.pre (t1.callEntry.withRegions (rd L) (wr L)))
    (hpub : ∀ (L : Lay) g₁ g₂ v₁ v₂ m₁ m₂ (a b a1 b1 : State), L.Ok → I L m₁ m₂ → Ctx L g₁ v₁ m₁ a →
      Ctx L g₂ v₂ m₂ b → Φ L m₁ a → Φ L m₂ b → MovedS as a a1 → MovedS as b b1 →
      k.pub (a1.callEntry.withRegions (rd L) (wr L)) (b1.callEntry.withRegions (rd L) (wr L)))
    (hcov : ∀ (L : Lay) g v m₀ (t : State), L.Ok → Ctx L g v m₀ t → Φ L m₀ t →
      Covers (rd L++wr L) (L.rd++L.wr) ∧ Covers (wr L) L.wr) :
    RelCT isa (Two I Φ) (callA n c as) fun _ _ => True := by
  refine RelCT.seq (RelCT.postDep (Q := fun a1 b1 => ∃ a b, Two I Φ a b ∧ MovedS as a a1 ∧ MovedS as b b1)
    (block_x28_tr (setArgs_xOnly hok) fun _ _ h => h.x28)
    (fun x y ⟨L, _, _, _, _, _, _, hL, _, c₁, c₂, _, _⟩ =>
      ⟨WP.mono_syms (setArgs_ok as hok x (c₁.xOk hL)) (fun _ h hy=>⟨h,hy⟩),
        WP.mono_syms (setArgs_ok as hok y (c₂.xOk hL)) (fun _ h hy=>⟨h,hy⟩)⟩)
    fun x y x1 y1 hp f₁ f₂ => ⟨x, y, hp, f₁, f₂⟩) ?_
  -- The layout, out of the relation, so that the call's regions are fixed.
  refine RelCT.mono (P := fun a1 b1 => ∃ L : Lay, ∃ a b, (∃ (g₁ g₂ : Reg → BitVec 64) (v₁ v₂ : VReg → BitVec 128)
      (m₁ m₂ : Mem), L.Ok ∧ I L m₁ m₂ ∧ Ctx L g₁ v₁ m₁ a ∧ Ctx L g₂ v₂ m₂ b ∧ Φ L m₁ a ∧ Φ L m₂ b) ∧
      MovedS as a a1 ∧ MovedS as b b1)
    (RelCT.exists_ fun L => RelCT.call hv hct (rd L) (wr L) fun a1 b1 ⟨a, b, hp, f₁, f₂⟩ => ?_)
    (fun a1 b1 ⟨a, b, ⟨L, hp⟩, f₁, f₂⟩ => ⟨L, a, b, hp, f₁, f₂⟩) fun _ _ h => h
  obtain ⟨g₁, g₂, v₁, v₂, m₁, m₂, hL, hi, c₁, c₂, φ₁, φ₂⟩ := hp
  obtain ⟨hr, hw⟩ := hcov L g₁ v₁ m₁ a hL c₁ φ₁
  have cov : ∀ {t t1 : State} {g v m₀}, Ctx L g v m₀ t → MovedS as t t1 →
      Covers (rd L ++ wr L) (t1.rd ++ t1.wr) ∧ Covers (wr L) t1.wr := fun hc f => by
    rw [f.1.2.rd, f.1.2.wr, hc.rd, hc.wr]
    exact ⟨hr,hw⟩
  exact ⟨hpre L g₁ v₁ m₁ a a1 hL c₁ φ₁ f₁, hpre L g₂ v₂ m₂ b b1 hL c₂ φ₂ f₂,
    hpub L g₁ g₂ v₁ v₂ m₁ m₂ a b a1 b1 hL hi c₁ c₂ φ₁ φ₂ f₁ f₂, (cov c₁ f₁).1, (cov c₁ f₁).2,
    (cov c₂ f₂).1, (cov c₂ f₂).2⟩

end VG.Proof.MlDsa.AArch64.Message.Optimized
