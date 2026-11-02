module

public import VerifiedGarbage.Impl.ICall
public import VerifiedGarbage.Proof.Framework.Semantics

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

end VG
