module

public import VerifiedGarbage.Impl.ICall
public import VerifiedGarbage.Proof.Framework.RelCT

/-!
# Running an indirect call of a list of functions

An indirect call of the functions `ts` (`Code.icalls`) from `s`, by an
instruction calling the address `a`, is a call of the first of them at `a`
(`icallTarget`): it runs as that function's call (`Exec.icalls`), and every
run of it is one (`Exec.icalls_inv`). So two runs that call the same
address, with the functions at the same addresses, run the same function
(`icallTarget_congr`): what a proof of constant time needs, with
`Abi.withTables` making the table, and so the address called, public.
-/

@[expose] public section

namespace VG

variable {M : ISA}

/-- The function of `ts` that an indirect call to `a` from `s` reaches: the
first at `a`. -/
def icallTarget (M : ISA) (s : M.State) (a : Addr) (ts : List (String × Prog M)) :
    Option (String × Prog M) :=
  ts.find? fun p => M.fnAddr s p.1 == a

/-- The trace of an indirect call by `i` from `s` of the address `a`, whose
function's run leaks `t` and ends in `s₂` (`Exec.icall`). -/
abbrev icallTrace (M : ISA) (i : M.Instr) (s : M.State) (a : Addr) (s₂ : M.State) (t : List Leak) :
    List Leak :=
  (M.addrs i s).map .addr ++ .addr a :: ((M.callAddrs s).map .addr ++ t ++ (M.retAddrs s₂).map .addr)

/-- An indirect call of `ts` runs as the call of the function it reaches. -/
theorem Exec.icalls {i : M.Instr} {ts : List (String × Prog M)} {s s₁ s₂ s' : M.State}
    {t : List Leak} {a : Addr} {n : String} {b : Prog M} (hi : M.icall i s = some a)
    (hf : icallTarget M s a ts = some (n, b)) (hc : M.call s = some s₁) (hb : Exec M b s₁ t s₂)
    (hr : M.ret s₁ s₂ = some s') : Exec M (Code.icalls i ts) s (icallTrace M i s a s₂ t) s' := by
  induction ts with
  | nil => simp [icallTarget] at hf
  | cons p ts ih =>
    obtain ⟨n', b'⟩ := p
    simp only [icallTarget, List.find?_cons] at hf ih
    by_cases he : M.fnAddr s n' = a
    · simp only [he, beq_self_eq_true, Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      subst he
      exact .icall hi hc hb hr
    · have hne : (M.fnAddr s n' == a) = false := by simpa using he
      simp only [hne] at hf
      cases ts with
      | nil => simp at hf
      | cons q ts' =>
        obtain ⟨n'', b''⟩ := q
        exact .icallNext hi (fun h => he h.symm) (ih hf)

/-- Every run of an indirect call of the functions `p :: ts` is the call of
the function it reaches. -/
theorem Exec.icalls_inv {i : M.Instr} :
    ∀ {p : String × Prog M} {ts : List (String × Prog M)} {s s' : M.State} {t : List Leak},
      Exec M (Code.icalls i (p :: ts)) s t s' →
      ∃ a n b s₁ s₂ t', M.icall i s = some a ∧ icallTarget M s a (p :: ts) = some (n, b) ∧
        M.call s = some s₁ ∧ Exec M b s₁ t' s₂ ∧ M.ret s₁ s₂ = some s' ∧ t = icallTrace M i s a s₂ t'
  | (n, b), [], s, s', t, h => by
    cases h with
    | icall hi hc hb hr =>
      exact ⟨_, n, b, _, _, _, hi, by simp [icallTarget], hc, hb, hr, rfl⟩
  | (n, b), (n', b') :: ts, s, s', t, h => by
    cases h with
    | icall hi hc hb hr =>
      exact ⟨_, n, b, _, _, _, hi, by simp [icallTarget], hc, hb, hr, rfl⟩
    | icallNext hi hne h' =>
      obtain ⟨a', n₀, b₀, s₁, s₂, t', hi', hf, hc, hb, hr, rfl⟩ :=
        Exec.icalls_inv (i := i) (p := (n', b')) (ts := ts) h'
      obtain rfl : a' = _ := Option.some.inj (hi'.symm.trans hi)
      refine ⟨a', n₀, b₀, s₁, s₂, t', hi', ?_, hc, hb, hr, rfl⟩
      have hx : (M.fnAddr s n == a') = false := by simpa using fun h => hne h.symm
      simp only [icallTarget, List.find?_cons, hx] at hf ⊢
      exact hf

/-- The function an indirect call reaches depends on the state only through
the addresses of the functions. -/
theorem icallTarget_congr {s₁ s₂ : M.State} {a : Addr} {ts : List (String × Prog M)}
    (h : ∀ p ∈ ts, M.fnAddr s₁ p.1 = M.fnAddr s₂ p.1) :
    icallTarget M s₁ a ts = icallTarget M s₂ a ts := by
  induction ts with
  | nil => rfl
  | cons p ts ih =>
    have := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
    simp only [icallTarget, List.find?_cons] at this ⊢
    rw [h p (List.mem_cons_self ..), this]

/-- An indirect call that reaches `(n, c)` runs as the call of `c`. -/
theorem WP.icalls_of_call {i : M.Instr} {ts : List (String × Prog M)} {s : M.State} {a : Addr}
    {n : String} {c : Prog M} {Q : M.State → Prop} (hi : M.icall i s = some a)
    (hf : icallTarget M s a ts = some (n, c)) (h : WP M (.call n c) s Q) :
    WP M (Code.icalls i ts) s Q := by
  obtain ⟨t, s', e, hq⟩ := h
  cases e with
  | call hc hb hr => exact ⟨_, _, Exec.icalls hi hf hc hb hr, hq⟩

/-- Two runs of an indirect call that reach the same function at the same
address, with the instruction accessing the same addresses, are two runs of
its call, with the address added to both traces. -/
theorem RelCT.icalls_of_call {i : M.Instr} {p : String × Prog M} {ts : List (String × Prog M)}
    {n : String} {c : Prog M} {P Q : M.State → M.State → Prop} (h : RelCT M P (.call n c) Q)
    (hs : ∀ s₁ s₂, P s₁ s₂ → ∃ a, M.icall i s₁ = some a ∧ M.icall i s₂ = some a ∧
      icallTarget M s₁ a (p :: ts) = some (n, c) ∧ icallTarget M s₂ a (p :: ts) = some (n, c) ∧
      M.addrs i s₁ = M.addrs i s₂) :
    RelCT M P (Code.icalls i (p :: ts)) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨a, hi₁, hi₂, hf₁, hf₂, ha⟩ := hs _ _ hp
  obtain ⟨a₁, n₁, b₁, x₁, y₁, u₁, hj₁, hg₁, hc₁, hb₁, hr₁, rfl⟩ := Exec.icalls_inv e₁
  obtain ⟨a₂, n₂, b₂, x₂, y₂, u₂, hj₂, hg₂, hc₂, hb₂, hr₂, rfl⟩ := Exec.icalls_inv e₂
  obtain rfl := Option.some.inj (hj₁.symm.trans hi₁)
  obtain rfl := Option.some.inj (hj₂.symm.trans hi₂)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hg₁.symm.trans hf₁))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hg₂.symm.trans hf₂))
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.call hc₁ hb₁ hr₁) (.call hc₂ hb₂ hr₂)
  refine ⟨?_, hq⟩
  simp only [icallTrace, ha, ht]

/-- An indirect call in a frame, that reaches `(n, c)` from the state the
frame's push leaves, runs as the call of `c` in that frame. -/
theorem WP.frame_icalls_of_call {i j ins : M.Instr} {ts : List (String × Prog M)} {s : M.State}
    {n : String} {c : Prog M} {Q : M.State → Prop}
    (hs : ∀ s₁, M.push i s = some s₁ → ∃ a, M.icall ins s₁ = some a ∧ icallTarget M s₁ a ts = some (n, c))
    (h : WP M (.frame i (.call n c) j) s Q) : WP M (.frame i (Code.icalls ins ts) j) s Q := by
  obtain ⟨t, s', e, hq⟩ := h
  cases e with
  | frame hp hb hj =>
    cases hb with
    | call hc hb hr =>
      obtain ⟨a, hi, hf⟩ := hs _ hp
      exact ⟨_, _, .frame hp (Exec.icalls hi hf hc hb hr) hj, hq⟩

/-- Two runs of an indirect call in a frame, whose pushes access the same
addresses and from whose pushed states the call reaches the same function
at the same address, accessing the same addresses, are two runs of its call
in that frame, with the address added to both traces. -/
theorem RelCT.frame_icalls_of_call {i j ins : M.Instr} {p : String × Prog M} {ts : List (String × Prog M)}
    {n : String} {c : Prog M} {P Q : M.State → M.State → Prop} (h : RelCT M P (.frame i (.call n c) j) Q)
    (hs : ∀ s₁ s₂, P s₁ s₂ → M.addrs i s₁ = M.addrs i s₂ ∧ ∀ u₁ u₂, M.push i s₁ = some u₁ →
      M.push i s₂ = some u₂ → ∃ a, M.icall ins u₁ = some a ∧ M.icall ins u₂ = some a ∧
        icallTarget M u₁ a (p :: ts) = some (n, c) ∧ icallTarget M u₂ a (p :: ts) = some (n, c) ∧
        M.addrs ins u₁ = M.addrs ins u₂) :
    RelCT M P (.frame i (Code.icalls ins (p :: ts)) j) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨hpa, hs'⟩ := hs _ _ hp
  cases e₁ with
  | frame hp₁ hb₁ hj₁ =>
  cases e₂ with
  | frame hp₂ hb₂ hj₂ =>
  obtain ⟨a, hi₁, hi₂, hf₁, hf₂, ha⟩ := hs' _ _ hp₁ hp₂
  obtain ⟨a₁, n₁, b₁, x₁, y₁, u₁, hj₁', hg₁, hc₁, hb₁', hr₁, rfl⟩ := Exec.icalls_inv hb₁
  obtain ⟨a₂, n₂, b₂, x₂, y₂, u₂, hj₂', hg₂, hc₂, hb₂', hr₂, rfl⟩ := Exec.icalls_inv hb₂
  obtain rfl := Option.some.inj (hj₁'.symm.trans hi₁)
  obtain rfl := Option.some.inj (hj₂'.symm.trans hi₂)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hg₁.symm.trans hf₁))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hg₂.symm.trans hf₂))
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.frame hp₁ (.call hc₁ hb₁' hr₁) hj₁) (.frame hp₂ (.call hc₂ hb₂' hr₂) hj₂)
  refine ⟨?_, hq⟩
  rw [hpa] at ht ⊢
  simp only [List.append_assoc, List.append_cancel_left_eq] at ht
  simp only [icallTrace, ha, List.append_assoc, List.cons_append, ht]

end VG
