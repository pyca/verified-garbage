import VerifiedGarbage.Proof.Framework.Spectre

/-!
# Sequential runs are speculative runs

`Exec.sexec`: a sequential run of `c` is a speculative run that starts
before any misspeculation, with its own branch directions as directives and
its number of instructions as fuel, and leaks the same trace (`Leak.toS`);
and each prefix of it that stops at a branch is a speculative run too.
So `SpecConstantTime.constantTime`: speculative constant time implies
constant time, and the speculative semantics is not vacuous.
-/

namespace VG

/-- A sequential observation as a speculative one. -/
def Leak.toS : Leak → SLeak
  | .addr a => .addr a
  | .branch b => .cond (some b)

theorem Leak.toS_injective : Function.Injective Leak.toS := by
  intro a b h
  cases a <;> cases b <;> simp only [Leak.toS, SLeak.addr.injEq, SLeak.cond.injEq, Option.some.injEq,
    reduceCtorEq] at h <;> rw [h]

theorem map_toS_inj {t₁ t₂ : List Leak} (h : t₁.map Leak.toS = t₂.map Leak.toS) : t₁ = t₂ := by
  induction t₁ generalizing t₂ with
  | nil => cases t₂ <;> simp_all
  | cons a t₁ ih =>
    cases t₂ with
    | nil => simp at h
    | cons b t₂ =>
      simp only [List.map_cons, List.cons.injEq] at h
      rw [Leak.toS_injective h.1, ih h.2]

theorem map_addr_toS (l : List Addr) : (l.map Leak.addr).map Leak.toS = l.map SLeak.addr := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, ih]; rfl

def SLeak.isCond : SLeak → Bool
  | .cond _ => true
  | .addr _ => false

/-- The number of branch observations. -/
def nConds (u : List SLeak) : Nat := u.countP SLeak.isCond

theorem nConds_append (u v : List SLeak) : nConds (u ++ v) = nConds u + nConds v :=
  List.countP_append

theorem nConds_addrs (l : List Addr) : nConds (l.map SLeak.addr) = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [nConds, List.map_cons, List.countP_cons, SLeak.isCond] at ih ⊢; simpa using ih

theorem nConds_cond (v : Option Bool) (u : List SLeak) : nConds (.cond v :: u) = nConds u + 1 := by
  simp [nConds, List.countP_cons, SLeak.isCond]

variable {M : ISA} (S : Spectre M)

theorem execBlock_sblock {is : List M.Instr} {s s' : M.State} {t : List Leak}
    (h : execBlock M is s = some (s', t)) (n : Nat) :
    SBlock S is s false (is.length + n) (t.map Leak.toS) (some (s', n)) := by
  induction is generalizing s t with
  | nil =>
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [List.length_nil, Nat.zero_add]; exact .nil
  | cons i is ih =>
    simp only [execBlock] at h
    split at h
    · cases h
    rename_i s₁ e
    simp only [Option.map_eq_some_iff, Prod.exists] at h
    obtain ⟨_, u, h', he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    rw [List.length_cons, Nat.add_right_comm, List.map_append, map_addr_toS]
    exact .cons rfl e (ih h')

theorem execBlock_nConds {is : List M.Instr} {s s' : M.State} {t : List Leak}
    (h : execBlock M is s = some (s', t)) : nConds (t.map Leak.toS) = 0 := by
  induction is generalizing s t with
  | nil =>
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl
  | cons i is ih =>
    simp only [execBlock] at h
    split at h
    · cases h
    simp only [Option.map_eq_some_iff, Prod.exists] at h
    obtain ⟨_, u, h', he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    rw [List.map_append, map_addr_toS, nConds_append, nConds_addrs, ih h']

theorem getLast?_append_of {α : Type} {l u : List α} {y : α} (h : u.getLast? = some y) :
    (l ++ u).getLast? = some y := by
  rw [List.getLast?_append, h]; rfl

theorem getLast?_cons_of {α : Type} {a : α} {u : List α} {y : α} (h : u.getLast? = some y) :
    (a :: u).getLast? = some y :=
  getLast?_append_of (l := [a]) h

/-- What a run stopped at the branch after the first `j` of `D` leaks: a
prefix of the whole trace, ending with the value of that branch, which is
direction `j` of `D`. -/
def StopAt (D : List Bool) (j : Nat) (u w : List SLeak) : Prop :=
  u <+: w ∧ u.getLast? = D[j]?.map (fun b => .cond (some b)) ∧ nConds u = j + 1

/-- A sequential run is a speculative run, from a clear misspeculation flag,
with directives `D` (its branches' directions) and fuel `k` (its number of
instructions), leaving any further directives and fuel; its trace has one
branch observation per directive; and stopping at each of its branches is a
speculative run too. -/
theorem Exec.sexec {c : Prog M} {s s' : M.State} {t : List Leak} (e : Exec M c s t s') :
    ∃ D k, (∀ D' n, SExec S c s false (D ++ D') (k + n) (t.map Leak.toS) (.done s' false D' n)) ∧
      nConds (t.map Leak.toS) = D.length ∧
      ∀ j < D.length, ∀ n, ∃ u, SExec S c s false (D.take j) (k + n) u .halt ∧
        StopAt D j u (t.map Leak.toS) := by
  induction e with
  | @block is _ _ _ h =>
    exact ⟨[], is.length, fun D' n => .blockDone (execBlock_sblock S h n), execBlock_nConds h,
      fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | @seq c₁ c₂ _ _ _ t₁ t₂ _ _ ih₁ ih₂ =>
    obtain ⟨D₁, k₁, f₁, n₁, p₁⟩ := ih₁
    obtain ⟨D₂, k₂, f₂, n₂, p₂⟩ := ih₂
    refine ⟨D₁ ++ D₂, k₁ + k₂, fun D' n => ?_, ?_, fun j hj n => ?_⟩
    · have := SExec.seq (f₁ (D₂ ++ D') (k₂ + n)) (f₂ D' n)
      rwa [← List.append_assoc, ← Nat.add_assoc, ← List.map_append] at this
    · rw [List.map_append, nConds_append, n₁, n₂, List.length_append]
    · rw [List.length_append] at hj
      by_cases hj₁ : j < D₁.length
      · obtain ⟨u, hu, hp, hl, hc⟩ := p₁ j hj₁ (k₂ + n)
        refine ⟨u, ?_, ?_, ?_, hc⟩
        · rw [List.take_append_of_le_length (Nat.le_of_lt hj₁), Nat.add_assoc]; exact .seqHalt hu
        · rw [List.map_append]; exact hp.trans (List.prefix_append _ _)
        · rw [List.getElem?_append_left hj₁]; exact hl
      · obtain ⟨u, hu, hp, hl, hc⟩ := p₂ (j - D₁.length) (by omega) n
        refine ⟨t₁.map Leak.toS ++ u, ?_, ?_, ?_, ?_⟩
        · rw [List.take_append, List.take_of_length_le (by omega), Nat.add_assoc]
          exact .seq (f₁ _ (k₂ + n)) hu
        · rw [List.map_append]; exact (List.prefix_append_right_inj _).mpr hp
        · rw [List.getElem?_append_right (by omega)]
          obtain ⟨b, hb⟩ : ∃ b, D₂[j - D₁.length]? = some b :=
            ⟨_, List.getElem?_eq_getElem (by omega)⟩
          rw [hb] at hl ⊢; exact getLast?_append_of hl
        · rw [nConds_append, n₁, hc]; omega
  | @iteT c th el s₀ _ t hc _ ih =>
    obtain ⟨D, k, f, nc, p⟩ := ih
    have hm : Spectre.mis false (M.eval c s₀) true = false := by rw [hc]; rfl
    refine ⟨true :: D, k, fun D' n => ?_, ?_, fun j hj n => ?_⟩
    · have := SExec.iteT (S := S) (el := el) (hm ▸ f D' n)
      rw [hc] at this; exact this
    · show nConds (.cond (some true) :: t.map Leak.toS) = D.length + 1
      rw [nConds_cond, nc]
    · cases j with
      | zero =>
        refine ⟨[.cond (some true)], ?_, ⟨t.map Leak.toS, rfl⟩, rfl, rfl⟩
        have := SExec.iteEnd (S := S) (c := c) (th := th) (el := el) (s := s₀) (ms := false) (n := k + n)
        rw [hc] at this; exact this
      | succ j =>
        obtain ⟨u, hu, hp, hl, hc'⟩ := p j (by simp only [List.length_cons] at hj; omega) n
        refine ⟨.cond (some true) :: u, ?_, List.cons_prefix_cons.mpr ⟨rfl, hp⟩, ?_, ?_⟩
        · have := SExec.iteT (S := S) (el := el) (hm ▸ hu)
          rw [hc] at this; exact this
        · obtain ⟨b, hb⟩ : ∃ b, D[j]? = some b := ⟨_, List.getElem?_eq_getElem (by simp at hj; omega)⟩
          rw [hb] at hl
          show _ = (D[j]?).map _
          rw [hb]; exact getLast?_cons_of hl
        · rw [nConds_cond, hc']
  | @iteF c th el s₀ _ t hc _ ih =>
    obtain ⟨D, k, f, nc, p⟩ := ih
    have hm : Spectre.mis false (M.eval c s₀) false = false := by rw [hc]; rfl
    refine ⟨false :: D, k, fun D' n => ?_, ?_, fun j hj n => ?_⟩
    · have := SExec.iteF (S := S) (th := th) (hm ▸ f D' n)
      rw [hc] at this; exact this
    · show nConds (.cond (some false) :: t.map Leak.toS) = D.length + 1
      rw [nConds_cond, nc]
    · cases j with
      | zero =>
        refine ⟨[.cond (some false)], ?_, ⟨t.map Leak.toS, rfl⟩, rfl, rfl⟩
        have := SExec.iteEnd (S := S) (c := c) (th := th) (el := el) (s := s₀) (ms := false) (n := k + n)
        rw [hc] at this; exact this
      | succ j =>
        obtain ⟨u, hu, hp, hl, hc'⟩ := p j (by simp only [List.length_cons] at hj; omega) n
        refine ⟨.cond (some false) :: u, ?_, List.cons_prefix_cons.mpr ⟨rfl, hp⟩, ?_, ?_⟩
        · have := SExec.iteF (S := S) (th := th) (hm ▸ hu)
          rw [hc] at this; exact this
        · obtain ⟨b, hb⟩ : ∃ b, D[j]? = some b := ⟨_, List.getElem?_eq_getElem (by simp at hj; omega)⟩
          rw [hb] at hl
          show _ = (D[j]?).map _
          rw [hb]; exact getLast?_cons_of hl
        · rw [nConds_cond, hc']
  | @loopExit body c _ s₁ t hb hc ih =>
    obtain ⟨D, k, f, nc, p⟩ := ih
    refine ⟨D ++ [false], k, fun D' n => ?_, ?_, fun j hj n => ?_⟩
    · have := SExec.loopExit (S := S) (c := c) (f (false :: D') n)
      rw [hc] at this
      rw [List.append_assoc, List.singleton_append, List.map_append]; exact this
    · rw [List.map_append, nConds_append, nc, List.length_append]; rfl
    · rw [List.length_append, List.length_singleton] at hj
      by_cases hj₁ : j < D.length
      · obtain ⟨u, hu, hp, hl, hc'⟩ := p j hj₁ n
        refine ⟨u, ?_, ?_, ?_, hc'⟩
        · rw [List.take_append_of_le_length (Nat.le_of_lt hj₁)]; exact .loopHalt hu
        · rw [List.map_append]; exact hp.trans (List.prefix_append _ _)
        · rw [List.getElem?_append_left hj₁]; exact hl
      · obtain rfl : j = D.length := by omega
        refine ⟨t.map Leak.toS ++ [.cond (some false)], ?_, ?_, ?_, ?_⟩
        · have := SExec.loopEnd (S := S) (c := c) (f [] n)
          rw [hc, List.append_nil] at this
          rw [List.take_append_of_le_length (Nat.le_refl _), List.take_of_length_le (Nat.le_refl _)]
          exact this
        · rw [List.map_append]; exact List.prefix_refl _
        · rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; exact getLast?_append_of rfl
        · rw [nConds_append, nc]; rfl
  | @loopNext body c _ s₁ _ t t' hb hc _ ih₁ ih₂ =>
    obtain ⟨D₁, k₁, f₁, n₁, p₁⟩ := ih₁
    obtain ⟨D₂, k₂, f₂, n₂, p₂⟩ := ih₂
    have hm : Spectre.mis false (M.eval c s₁) true = false := by rw [hc]; rfl
    refine ⟨D₁ ++ true :: D₂, k₁ + k₂, fun D' n => ?_, ?_, fun j hj n => ?_⟩
    · have := SExec.loopNext (f₁ (true :: (D₂ ++ D')) (k₂ + n)) (hm ▸ f₂ D' n)
      rw [hc] at this
      rw [List.append_assoc, List.cons_append, Nat.add_assoc, List.map_append, List.map_cons]
      exact this
    · rw [List.map_append, List.map_cons, nConds_append]
      show _ + nConds (.cond (some true) :: _) = _
      rw [nConds_cond, n₁, n₂, List.length_append, List.length_cons]
    · rw [List.length_append, List.length_cons] at hj
      rcases Nat.lt_trichotomy j D₁.length with hj₁ | rfl | hj₁
      · obtain ⟨u, hu, hp, hl, hc'⟩ := p₁ j hj₁ (k₂ + n)
        refine ⟨u, ?_, ?_, ?_, hc'⟩
        · rw [List.take_append_of_le_length (Nat.le_of_lt hj₁), Nat.add_assoc]; exact .loopHalt hu
        · rw [List.map_append]; exact hp.trans (List.prefix_append _ _)
        · rw [List.getElem?_append_left hj₁]; exact hl
      · refine ⟨t.map Leak.toS ++ [.cond (some true)], ?_, ?_, ?_, ?_⟩
        · have := SExec.loopEnd (S := S) (c := c) (f₁ [] (k₂ + n))
          rw [hc, List.append_nil] at this
          rw [List.take_append_of_le_length (Nat.le_refl _), List.take_of_length_le (Nat.le_refl _),
            Nat.add_assoc]
          exact this
        · rw [List.map_append, List.map_cons]
          exact (List.prefix_append_right_inj _).mpr (List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩)
        · rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; exact getLast?_append_of rfl
        · rw [nConds_append, n₁]; rfl
      · obtain ⟨u, hu, hp, hl, hc'⟩ := p₂ (j - D₁.length - 1) (by omega) n
        refine ⟨t.map Leak.toS ++ .cond (some true) :: u, ?_, ?_, ?_, ?_⟩
        · have := SExec.loopNext (f₁ (true :: D₂.take (j - D₁.length - 1)) (k₂ + n)) (hm ▸ hu)
          rw [hc] at this
          rw [List.take_append, List.take_of_length_le (by omega), Nat.add_assoc,
            show j - D₁.length = (j - D₁.length - 1) + 1 by omega, List.take_succ_cons]
          exact this
        · rw [List.map_append, List.map_cons]
          exact (List.prefix_append_right_inj _).mpr (List.cons_prefix_cons.mpr ⟨rfl, hp⟩)
        · rw [List.getElem?_append_right (by omega),
            show j - D₁.length = (j - D₁.length - 1) + 1 by omega, List.getElem?_cons_succ]
          obtain ⟨b, hb⟩ : ∃ b, D₂[j - D₁.length - 1]? = some b :=
            ⟨_, List.getElem?_eq_getElem (by omega)⟩
          rw [hb] at hl ⊢; exact getLast?_append_of (getLast?_cons_of hl)
        · rw [nConds_append, nConds_cond, n₁, hc']; omega
  | @call _ body _ s₁ s₂ _ t hcall _ hr ih =>
    obtain ⟨D, k, f, nc, p⟩ := ih
    refine ⟨D, k, fun D' n => ?_, ?_, fun j hj n => ?_⟩
    · rw [List.map_append, List.map_append, map_addr_toS, map_addr_toS]
      exact .call hcall (f D' n) hr
    · rw [List.map_append, List.map_append, map_addr_toS, map_addr_toS, nConds_append, nConds_append,
        nConds_addrs, nConds_addrs, nc]; omega
    · obtain ⟨u, hu, hp, hl, hc'⟩ := p j hj n
      refine ⟨(M.callAddrs _).map SLeak.addr ++ u, .callHalt hcall hu, ?_, ?_, ?_⟩
      · rw [List.map_append, List.map_append, map_addr_toS, List.append_assoc]
        exact (List.prefix_append_right_inj _).mpr (hp.trans (List.prefix_append _ _))
      · obtain ⟨b, hb⟩ : ∃ b, D[j]? = some b := ⟨_, List.getElem?_eq_getElem hj⟩
        rw [hb] at hl ⊢; exact getLast?_append_of hl
      · rw [nConds_append, nConds_addrs, hc']; omega
  | @frame i j body _ s₁ s₂ _ t hpush _ hpop ih =>
    obtain ⟨D, k, f, nc, p⟩ := ih
    refine ⟨D, k, fun D' n => ?_, ?_, fun j hj n => ?_⟩
    · rw [List.map_append, List.map_append, map_addr_toS, map_addr_toS]
      exact .frame hpush (f D' n) hpop
    · rw [List.map_append, List.map_append, map_addr_toS, map_addr_toS, nConds_append, nConds_append,
        nConds_addrs, nConds_addrs, nc]; omega
    · obtain ⟨u, hu, hp, hl, hc'⟩ := p j hj n
      refine ⟨(M.addrs i _).map SLeak.addr ++ u, .frameHalt hpush hu, ?_, ?_, ?_⟩
      · rw [List.map_append, List.map_append, map_addr_toS, List.append_assoc]
        exact (List.prefix_append_right_inj _).mpr (hp.trans (List.prefix_append _ _))
      · obtain ⟨b, hb⟩ : ∃ b, D[j]? = some b := ⟨_, List.getElem?_eq_getElem hj⟩
        rw [hb] at hl ⊢; exact getLast?_append_of hl
      · rw [nConds_append, nConds_addrs, hc']; omega

/-- Two lists are equal, differ at an index both have, or one is a proper
prefix of the other. -/
theorem list_cases (D₁ D₂ : List Bool) : D₁ = D₂ ∨
    (∃ j, j < D₁.length ∧ j < D₂.length ∧ D₁.take j = D₂.take j ∧ D₁[j]? ≠ D₂[j]?) ∨
    (D₁.length < D₂.length ∧ D₂.take D₁.length = D₁) ∨
    (D₂.length < D₁.length ∧ D₁.take D₂.length = D₂) := by
  induction D₁ generalizing D₂ with
  | nil => cases D₂ with
    | nil => exact .inl rfl
    | cons b D₂ => exact .inr (.inr (.inl ⟨by simp, rfl⟩))
  | cons a D₁ ih => cases D₂ with
    | nil => exact .inr (.inr (.inr ⟨by simp, rfl⟩))
    | cons b D₂ =>
      by_cases hab : a = b
      · subst hab
        rcases ih D₂ with rfl | ⟨j, h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · exact .inl rfl
        · exact .inr (.inl ⟨j + 1, by simp [h₁], by simp [h₂], by simp [h₃], by simpa using h₄⟩)
        · exact .inr (.inr (.inl ⟨by simp [h₁], by simp [h₂]⟩))
        · exact .inr (.inr (.inr ⟨by simp [h₁], by simp [h₂]⟩))
      · exact .inr (.inl ⟨0, by simp, by simp, rfl, by simpa using hab⟩)

/-- Speculative constant time implies constant time. -/
theorem SpecConstantTime.constantTime {Pre : M.State → Prop} {Pub : M.State → M.State → Prop}
    {c : Prog M} (h : SpecConstantTime S Pre Pub c) : ConstantTime M Pre Pub c := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  obtain ⟨D₁, k₁, f₁, c₁, p₁⟩ := e₁.sexec S
  obtain ⟨D₂, k₂, f₂, c₂, p₂⟩ := e₂.sexec S
  have F₁ := f₁ [] k₂
  have F₂ := f₂ [] k₁
  rw [List.append_nil] at F₁
  rw [List.append_nil, Nat.add_comm] at F₂
  have hf : Function.Injective fun b : Bool => SLeak.cond (some b) := by
    intro a b h; simpa using h
  rcases list_cases D₁ D₂ with rfl | ⟨j, hj₁, hj₂, ht, hd⟩ | ⟨hl, ht⟩ | ⟨hl, ht⟩
  · exact map_toS_inj (h _ _ _ _ _ _ _ _ h₁ h₂ hp F₁ F₂)
  · obtain ⟨u₁, x₁, -, l₁, -⟩ := p₁ j hj₁ k₂
    obtain ⟨u₂, x₂, -, l₂, -⟩ := p₂ j hj₂ k₁
    rw [Nat.add_comm, ← ht] at x₂
    have := h _ _ _ _ _ _ _ _ h₁ h₂ hp x₁ x₂
    subst this
    exact absurd (Option.map_injective hf (l₁.symm.trans l₂)) hd
  · obtain ⟨u₂, x₂, -, -, n₂⟩ := p₂ D₁.length hl k₁
    rw [Nat.add_comm, ht] at x₂
    have := h _ _ _ _ _ _ _ _ h₁ h₂ hp F₁ x₂
    rw [← this, c₁] at n₂; omega
  · obtain ⟨u₁, x₁, -, -, n₁⟩ := p₁ D₂.length hl k₂
    rw [ht] at x₁
    have := h _ _ _ _ _ _ _ _ h₁ h₂ hp x₁ F₂
    rw [this, c₂] at n₁; omega

end VG
