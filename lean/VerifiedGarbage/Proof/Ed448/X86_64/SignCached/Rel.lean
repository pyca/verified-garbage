import VerifiedGarbage.Proof.Ed448.X86_64.SignCached.Hash
import VerifiedGarbage.Proof.Ed448.X86_64.Verify.Rel

/-!
# Ed448 signing with a cached public key on x86-64: relating two runs

Two runs between the frame's push and pop with the same layout, each in a
`Ctx` state, whose inputs agree on `I`, and each satisfying `Φ` (`Two`). What
each run satisfies by correctness carries over (`two_wp`), and a call of
code whose public data agree in both runs leaks the same (`call_tr`). Blocks
addressed from `rsp` and the moves of arguments are `Verify`'s
(`block_rsp_tr`, `setArgs_spOnly`).
-/

namespace VG.Proof.Ed448.X86_64.SignCached

open VG VG.X86_64
open VG.Impl.Ed448.X86_64.Verify (Arg setArgs callA)
open VG.Proof.Ed448.X86_64.Verify (Within covers_of_within block_rsp_tr setArgs_spOnly setArgs_ok ArgsIn Moved)
open VG.Proof.MlKem.X86_64 (Keep RelCT.postDep)

/-! ## Two runs -/

/-- Two runs with the layout `L`, inputs related by `I`, each satisfying `Φ`. -/
def Two (I : Lay → Mem → Mem → Prop) (Φ : Lay → Mem → State → Prop) (a b : State) : Prop :=
  ∃ (L : Lay) (g₁ g₂ : Reg → BitVec 64) (mx₁ mx₂ : BitVec 32) (m₁ m₂ : Mem), L.Ok ∧ I L m₁ m₂ ∧
    Ctx L g₁ mx₁ m₁ a ∧ Ctx L g₂ mx₂ m₂ b ∧ Φ L m₁ a ∧ Φ L m₂ b

section
variable {I : Lay → Mem → Mem → Prop}

theorem Two.rsp {Φ : Lay → Mem → State → Prop} {a b : State} (h : Two I Φ a b) : a.gpr .rsp = b.gpr .rsp :=
  let ⟨_, _, _, _, _, _, _, _, _, c₁, c₂, _, _⟩ := h; c₁.rsp.trans c₂.rsp.symm

theorem two_wp {c : Prog isa} {Φ Ψ : Lay → Mem → State → Prop}
    (hct : RelCT isa (Two I Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay) g mx m₀ (t : State), L.Ok → Ctx L g mx m₀ t → Φ L m₀ t →
      WP isa c t fun t' => Ctx L g mx m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (Two I Φ) c (Two I Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨L, g₁, g₂, mx₁, mx₂, m₁, m₂, hL, hi, c₁, c₂, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw L g₁ mx₁ m₁ s₁ hL c₁ f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw L g₂ mx₂ m₂ s₂ hL c₂ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, L, g₁, g₂, mx₁, mx₂, m₁, m₂, hL, hi, y₁.1, y₂.1, y₁.2, y₂.2⟩

theorem two_mono {Φ Ψ : Lay → Mem → State → Prop} (h : ∀ L m t, Φ L m t → Ψ L m t) {a b : State}
    (hp : Two I Φ a b) : Two I Ψ a b :=
  let ⟨L, g₁, g₂, mx₁, mx₂, m₁, m₂, hL, hi, c₁, c₂, f₁, f₂⟩ := hp
  ⟨L, g₁, g₂, mx₁, mx₂, m₁, m₂, hL, hi, c₁, c₂, h _ _ _ f₁, h _ _ _ f₂⟩

/-- A call after the moves of its arguments, of verified code whose public
data agree in both runs. -/
theorem call_tr {Φ : Lay → Mem → State → Prop} {as : List Arg} (hok : as.all Arg.ok = true) {n : String}
    {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (rd wr : Lay → List Region)
    (hpre : ∀ (L : Lay) g mx m₀ (t t1 : State), L.Ok → Ctx L g mx m₀ t → Φ L m₀ t → Moved as t t1 →
      k.pre (t1.callEntry.withRegions (rd L) (wr L)))
    (hpub : ∀ (L : Lay) g₁ g₂ mx₁ mx₂ m₁ m₂ (a b a1 b1 : State), L.Ok → I L m₁ m₂ → Ctx L g₁ mx₁ m₁ a →
      Ctx L g₂ mx₂ m₂ b → Φ L m₁ a → Φ L m₂ b → Moved as a a1 → Moved as b b1 →
      k.pub (a1.callEntry.withRegions (rd L) (wr L)) (b1.callEntry.withRegions (rd L) (wr L)))
    (hcov : ∀ (L : Lay) g mx m₀ (t : State), L.Ok → Ctx L g mx m₀ t → Φ L m₀ t →
      (∀ r ∈ rd L, ∃ R ∈ L.rd ++ L.FR :: L.wr, Within r R) ∧ (∀ r ∈ wr L, ∃ R ∈ L.FR :: L.wr, Within r R)) :
    RelCT isa (Two I Φ) (callA n c as) fun _ _ => True := by
  refine RelCT.seq (RelCT.postDep (Q := fun a1 b1 => ∃ a b, Two I Φ a b ∧ Moved as a a1 ∧ Moved as b b1)
    (block_rsp_tr (setArgs_spOnly as) fun _ _ h => h.rsp)
    (fun x y ⟨_, _, _, _, _, _, _, _, _, c₁, c₂, _, _⟩ =>
      ⟨setArgs_ok as hok x c₁.frOk, setArgs_ok as hok y c₂.frOk⟩)
    fun x y x1 y1 hp f₁ f₂ => ⟨x, y, hp, f₁, f₂⟩) ?_
  refine RelCT.callEx hv hct fun a1 b1 ⟨a, b, hp, f₁, f₂⟩ => ?_
  obtain ⟨L, g₁, g₂, mx₁, mx₂, m₁, m₂, hL, hi, c₁, c₂, φ₁, φ₂⟩ := hp
  obtain ⟨hr, hw⟩ := hcov L g₁ mx₁ m₁ a hL c₁ φ₁
  have cov : ∀ {t t1 : State} {g mx m₀}, Ctx L g mx m₀ t → Moved as t t1 →
      Covers (rd L ++ wr L) (t1.rd ++ t1.wr) ∧ Covers (wr L) t1.wr := fun hc f => by
    rw [f.2.2.1, f.2.2.2, hc.rd, hc.wr]
    refine ⟨covers_of_within fun r hr' => ?_, covers_of_within fun r hr' => ?_⟩
    · rcases List.mem_append.mp hr' with h' | h'
      · exact hr r h'
      · obtain ⟨R, hR, hW⟩ := hw r h'
        exact ⟨R, List.mem_append_right _ hR, hW⟩
    · exact hw r hr'
  exact ⟨rd L, wr L, rd L, wr L, hpre L g₁ mx₁ m₁ a a1 hL c₁ φ₁ f₁, hpre L g₂ mx₂ m₂ b b1 hL c₂ φ₂ f₂,
    hpub L g₁ g₂ mx₁ mx₂ m₁ m₂ a b a1 b1 hL hi c₁ c₂ φ₁ φ₂ f₁ f₂, (cov c₁ f₁).1, (cov c₁ f₁).2,
    (cov c₂ f₂).1, (cov c₂ f₂).2,
    by rw [f₁.2.gpr (by decide), f₂.2.gpr (by decide), c₁.rsp, c₂.rsp]⟩

end

end VG.Proof.Ed448.X86_64.SignCached
