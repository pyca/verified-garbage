module

public import VerifiedGarbage.Proof.Framework.AppendSlice
public import VerifiedGarbage.Proof.Framework.X86_64.Inline

/-!
# Contracts with one more read-only slice argument (x86-64)

`Verified.withSlice` for the System V calling convention, with tables of
functions (`Abi.withTables`) or none, for signatures of more than six words:
the first six in `rdi`, `rsi`, `rdx`, `rcx`, `r8` and `r9`, the others on the
stack, the slice's two last, on the stack after those of the shorter
signature, whose tables are among them (`verified_withSlice`).
-/

@[expose] public section

namespace VG.X86_64

/-- The arguments of a signature of `n` words, more than six. -/
def wordVals (n : Nat) (s : State) : List (BitVec 64) :=
  argRegs.map s.gpr ++ (List.range (n - 6)).map (stackArg s)

theorem abi_args_many (ws : List Nat) (hn : 6 < ws.length) :
    abi.args ws = some (wordVals ws.length) := by
  have h6 : ¬ ws.length ≤ argRegs.length := by simp only [argRegs, List.length_cons, List.length_nil]; omega_using [hn]
  simp only [abi, h6, ↓reduceIte]
  rfl

theorem wordVals_succ2 (n : Nat) (s : State) (hn : 6 ≤ n) :
    wordVals (n + 2) s = wordVals n s ++ [stackArg s (n - 6), stackArg s (n + 1 - 6)] := by
  simp only [wordVals, List.append_assoc]
  rw [show n + 2 - 6 = n - 6 + 1 + 1 by omega_using [hn], List.range_succ, List.range_succ]
  simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.cons_append,
    List.nil_append, show n - 6 + 1 = n + 1 - 6 by omega_using [hn]]

theorem wordVals_length (n : Nat) (s : State) (hn : 6 ≤ n) : (wordVals n s).length = n := by
  simp [wordVals, argRegs]; omega_using [hn]

theorem words_withSlice_map (sig : Sig) (nm : String) (e : Elem) (ln : String) :
    ((sig.withSlice nm e ln).words 64).map (·.bits 64) = (sig.words 64).map (·.bits 64) ++ [64, 64] := by
  rw [Sig.words_withSlice]; simp [ArgWord.bits]

theorem abi_wf_append {ws : List Nat} (hne : 6 < ws.length) {n : Nat} {s : State}
    (h : abi.wf (ws ++ [64, 64]) n s) (r w : List Region) : abi.wf ws n (s.withRegions r w) := by
  have hsp : (s.withRegions r w).gpr .rsp = s.gpr .rsp := rfl
  have hl : argRegs.length = 6 := rfl
  have hl2 : (ws ++ [64, 64]).length = ws.length + 2 := by simp
  have h8 : (ws.length ≤ 6) = False := by simp; omega_using [hne]
  have h8' : (ws.length + 2 ≤ 6) = False := by simp; omega_using [hne]
  simp only [abi, hsp, hl, hl2, h8, h8', ite_false] at h ⊢
  rcases n with _ | k
  · exact ⟨trivial, by omega⟩
  · exact ⟨h.1, by omega⟩

theorem abi_area_append {ws : List Nat} (hne : 6 < ws.length) (s : State) :
    List.Forall₂ RegionBelow (abi.argArea ws s) (abi.argArea (ws ++ [64, 64]) s) := by
  have h₁ : ws.length - argRegs.length ≠ 0 := by simp only [argRegs, List.length_cons, List.length_nil]; omega_using [hne]
  have h₂ : (ws ++ [64, 64]).length - argRegs.length ≠ 0 := by
    simp only [argRegs, List.length_append, List.length_cons, List.length_nil]; omega_using [hne]
  simp only [abi, h₁, h₂, ↓reduceIte]
  exact .cons ⟨⟨rfl, by simp only [argRegs, List.length_append, List.length_cons, List.length_nil]; omega_using []⟩, rfl⟩ .nil

/-- The words of `sig`'s arguments followed by a slice's two. -/
abbrev sliceVals (n : Nat) (s : State) : List (BitVec 64) :=
  wordVals n s ++ [stackArg s (n - 6), stackArg s (n + 1 - 6)]

/-- `Verified.withSlice` on x86-64, for contracts without tables of functions:
every argument a 32-bit word. -/
theorem verified_withSlice {sig : Sig} {nm ln : String} {e : Elem}
    (hne : 6 < (sig.words 64).length)
    {c : Prog isa} {writeArgs : Bool} {stack : Nat}
    {pre : Curry (sig.words 64) (Mem → Prop)} {post : sig.Post 64}
    {leak : Option (Curry (sig.words 64) (Mem → List Nat))}
    {pre' : Curry ((sig.withSlice nm e ln).words 64) (Mem → Prop)}
    {post' : (sig.withSlice nm e ln).Post 64}
    {leak' : Option (Curry ((sig.withSlice nm e ln).words 64) (Mem → List Nat))}
    (h : Verified target c (sig.contract abi pre post writeArgs stack leak))
    (hpre : ∀ s, Curry.apply _ pre' (sliceVals (sig.words 64).length s) s.mem →
      Curry.apply _ pre (wordVals (sig.words 64).length s) s.mem)
    (hpost : ∀ s m' (v : BitVec 64), Curry.apply _ pre' (sliceVals (sig.words 64).length s) s.mem →
      Curry.apply _ post (wordVals (sig.words 64).length s) s.mem m' (v.setWidth _) →
      Curry.apply _ post' (sliceVals (sig.words 64).length s) s.mem m' (v.setWidth _))
    (hleak : ∀ s₁ s₂, Curry.apply _ pre' (sliceVals (sig.words 64).length s₁) s₁.mem →
      Curry.apply _ pre' (sliceVals (sig.words 64).length s₂) s₂.mem →
      (∀ i, (sig.params.flatMap (·.2.pubs)).getD i false = true →
        ((wordVals (sig.words 64).length s₁).getD i 0).setWidth (((sig.words 64).map (·.bits 64)).getD i 64) =
          ((wordVals (sig.words 64).length s₂).getD i 0).setWidth (((sig.words 64).map (·.bits 64)).getD i 64)) →
      leakAgree leak' (sliceVals (sig.words 64).length s₁) s₁.mem (sliceVals (sig.words 64).length s₂) s₂.mem →
      leakAgree leak (wordVals (sig.words 64).length s₁) s₁.mem (wordVals (sig.words 64).length s₂) s₂.mem)
    (hsat : ∃ s, ((sig.withSlice nm e ln).contract abi pre' post' writeArgs stack leak').pre s) :
    Verified target c ((sig.withSlice nm e ln).contract abi pre' post' writeArgs stack leak') := by
  have hn : (((sig.withSlice nm e ln).words 64).map (·.bits 64)).length = (sig.words 64).length + 2 := by
    rw [Sig.words_withSlice]; simp
  have ha : abi.args ((sig.words 64).map (·.bits 64)) = some (wordVals (sig.words 64).length) := by
    rw [abi_args_many _ (by rw [List.length_map]; exact hne), List.length_map]
  have ha' : abi.args (((sig.withSlice nm e ln).words 64).map (·.bits 64)) =
      some (sliceVals (sig.words 64).length) := by
    rw [abi_args_many _ (by rw [hn]; omega_using [hne]), hn]; congr 1; funext s; exact wordVals_succ2 _ s (by omega_using [hne])
  have hret : ∀ (s : State) (r w : List Region), abi.ret (s.withRegions r w) = abi.ret s := fun _ _ _ => rfl
  have hres : ∀ n (s : State) (r w : List Region), abi.reserved n (s.withRegions r w) = abi.reserved n s :=
    fun _ _ _ _ => rfl
  have hpubA : ∀ (s₁ s₂ : State) r₁ w₁ r₂ w₂, abi.pub s₁ s₂ → abi.pub (s₁.withRegions r₁ w₁) (s₂.withRegions r₂ w₂) :=
    fun _ _ _ _ _ _ h => h
  exact Verified.withSlice (T := target) regionModel (fun _ _ _ _ h => h) abi abi rfl (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hret hpubA hres rfl
    (sig := sig) (nm := nm) (e := e) (ln := ln) (vals := wordVals (sig.words 64).length)
    (X := fun s => stackArg s ((sig.words 64).length - 6)) (Y := fun s => stackArg s ((sig.words 64).length + 1 - 6))
    ha ha' (fun s => wordVals_length _ s (by omega_using [hne])) (fun _ _ _ => rfl)
    (fun n s r w h => abi_wf_append (ws := (sig.words 64).map (·.bits 64)) (by rw [List.length_map]; exact hne)
      (by have h' : abi.wf (((sig.withSlice nm e ln).words 64).map (·.bits 64)) n s := h
          rw [words_withSlice_map] at h'; exact h') r w)
    (fun s => by
      have := abi_area_append (ws := (sig.words 64).map (·.bits 64)) (by rw [List.length_map]; exact hne) s
      rw [← words_withSlice_map sig nm e ln] at this
      exact this)
    (fun _ _ _ => rfl)
    (c := c) (writeArgs := writeArgs) (stack := stack) (pre := pre) (post := post) (leak := leak)
    (pre' := pre') (post' := post') (leak' := leak') h hpre hpost hleak hsat

/-- `Verified.withSlice` on x86-64, for contracts with the tables `t :: ts`, which
the shorter signature names: every argument a 32-bit word. -/
theorem verified_withSlice_tables {sig : Sig} {nm ln : String} {e : Elem} {t : String × List FnTable} {ts : List (String × List FnTable)}
    (hts : ∀ u ∈ t :: ts, ∃ k, Sig.wordIndex sig.params u.1 = some k ∧ k < (sig.words 64).length)
    (hne : 6 < (sig.words 64).length)
    {c : Prog isa} {writeArgs : Bool} {stack : Nat}
    {pre : Curry (sig.words 64) (Mem → Prop)} {post : sig.Post 64}
    {leak : Option (Curry (sig.words 64) (Mem → List Nat))}
    {pre' : Curry ((sig.withSlice nm e ln).words 64) (Mem → Prop)}
    {post' : (sig.withSlice nm e ln).Post 64}
    {leak' : Option (Curry ((sig.withSlice nm e ln).words 64) (Mem → List Nat))}
    (h : Verified target c (sig.contract (abi.withTables sig (t :: ts)) pre post writeArgs stack leak))
    (hpre : ∀ s, Curry.apply _ pre' (sliceVals (sig.words 64).length s) s.mem →
      Curry.apply _ pre (wordVals (sig.words 64).length s) s.mem)
    (hpost : ∀ s m' (v : BitVec 64), Curry.apply _ pre' (sliceVals (sig.words 64).length s) s.mem →
      Curry.apply _ post (wordVals (sig.words 64).length s) s.mem m' (v.setWidth _) →
      Curry.apply _ post' (sliceVals (sig.words 64).length s) s.mem m' (v.setWidth _))
    (hleak : ∀ s₁ s₂, Curry.apply _ pre' (sliceVals (sig.words 64).length s₁) s₁.mem →
      Curry.apply _ pre' (sliceVals (sig.words 64).length s₂) s₂.mem →
      (∀ i, (sig.params.flatMap (·.2.pubs)).getD i false = true →
        ((wordVals (sig.words 64).length s₁).getD i 0).setWidth (((sig.words 64).map (·.bits 64)).getD i 64) =
          ((wordVals (sig.words 64).length s₂).getD i 0).setWidth (((sig.words 64).map (·.bits 64)).getD i 64)) →
      leakAgree leak' (sliceVals (sig.words 64).length s₁) s₁.mem (sliceVals (sig.words 64).length s₂) s₂.mem →
      leakAgree leak (wordVals (sig.words 64).length s₁) s₁.mem (wordVals (sig.words 64).length s₂) s₂.mem)
    (hsat : ∃ s, ((sig.withSlice nm e ln).contract (abi.withTables (sig.withSlice nm e ln) (t :: ts)) pre' post' writeArgs stack leak').pre s) :
    Verified target c ((sig.withSlice nm e ln).contract (abi.withTables (sig.withSlice nm e ln) (t :: ts)) pre' post' writeArgs stack leak') := by
  have hn : (((sig.withSlice nm e ln).words 64).map (·.bits 64)).length = (sig.words 64).length + 2 := by
    rw [Sig.words_withSlice]; simp
  have ha : abi.args ((sig.words 64).map (·.bits 64)) = some (wordVals (sig.words 64).length) := by
    rw [abi_args_many _ (by rw [List.length_map]; exact hne), List.length_map]
  have ha' : abi.args (((sig.withSlice nm e ln).words 64).map (·.bits 64)) =
      some (sliceVals (sig.words 64).length) := by
    rw [abi_args_many _ (by rw [hn]; omega_using [hne]), hn]; congr 1; funext s; exact wordVals_succ2 _ s (by omega_using [hne])
  have hret : ∀ (s : State) (r w : List Region), abi.ret (s.withRegions r w) = abi.ret s := fun _ _ _ => rfl
  have hres : ∀ n (s : State) (r w : List Region), abi.reserved n (s.withRegions r w) = abi.reserved n s :=
    fun _ _ _ _ => rfl
  -- The tables' addresses, the same arguments of either signature.
  have harg : ∀ (s : State) (x : String) (k : Nat), Sig.wordIndex sig.params x = some k →
      k < (sig.words 64).length →
      (Sig.wordIndex (sig.withSlice nm e ln).params x).map (fun k => (sliceVals (sig.words 64).length s).getD k 0) =
        (Sig.wordIndex sig.params x).map (fun k => (wordVals (sig.words 64).length s).getD k 0) := by
    intro s x k hk hlt
    rw [show (sig.withSlice nm e ln).params = sig.params ++ [(nm, .slice false e ln)] from rfl,
      Sig.wordIndex_append _ _ _ _ hk, hk]
    simp only [Option.map_some, sliceVals]
    rw [getD_append_lt _ _ _ (by rw [wordVals_length _ _ (by omega_using [hne])]; exact hlt)]
  exact Verified.withSlice (T := target) regionModel (fun _ _ _ _ h => h) (abi.withTables sig (t :: ts))
    (abi.withTables (sig.withSlice nm e ln) (t :: ts)) rfl (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hret
    (fun s₁ s₂ r₁ w₁ r₂ w₂ hp => by
      simp only [Abi.withTables, show abi.ptrBits = 64 from rfl] at hp ⊢
      rw [ha'] at hp
      rw [ha]
      obtain ⟨h₁, h₂, h₃⟩ := hp
      refine ⟨h₁, h₂, fun t' ht' p₁ p₂ e₁ e₂ T hT => ?_⟩
      obtain ⟨k, hk, hlt⟩ := hts t' ht'
      have e₁' : Option.map (fun k => (wordVals (sig.words 64).length s₁).getD k 0)
          (Sig.wordIndex sig.params t'.1) = some p₁ := e₁
      have e₂' : Option.map (fun k => (wordVals (sig.words 64).length s₂).getD k 0)
          (Sig.wordIndex sig.params t'.1) = some p₂ := e₂
      rw [← harg s₁ t'.1 k hk hlt] at e₁'
      rw [← harg s₂ t'.1 k hk hlt] at e₂'
      exact h₃ t' ht' p₁ p₂ e₁' e₂' T hT)
    hres rfl
    (sig := sig) (nm := nm) (e := e) (ln := ln) (vals := wordVals (sig.words 64).length)
    (X := fun s => stackArg s ((sig.words 64).length - 6)) (Y := fun s => stackArg s ((sig.words 64).length + 1 - 6))
    ha ha' (fun s => wordVals_length _ s (by omega_using [hne])) (fun _ _ _ => rfl)
    (fun n s r w hwf => by
      simp only [Abi.withTables, show abi.ptrBits = 64 from rfl] at hwf ⊢
      rw [ha'] at hwf
      rw [ha]
      obtain ⟨h₁, h₂, h₃⟩ := hwf
      refine ⟨abi_wf_append (by rw [List.length_map]; exact hne) (by rw [← words_withSlice_map sig nm e ln]; exact h₁) r w, fun t' ht' => ?_, h₃⟩
      obtain ⟨p, hp, T, hT, hh⟩ := h₂ t' ht'
      obtain ⟨k, hk, hlt⟩ := hts t' ht'
      rw [harg s t'.1 k hk hlt] at hp
      exact ⟨p, hp, T, hT, hh⟩)
    (fun s => by
      have := abi_area_append (ws := (sig.words 64).map (·.bits 64)) (by rw [List.length_map]; exact hne) s
      rw [← words_withSlice_map sig nm e ln] at this
      exact this)
    (fun _ _ _ => rfl)
    (c := c) (writeArgs := writeArgs) (stack := stack) (pre := pre) (post := post) (leak := leak)
    (pre' := pre') (post' := post') (leak' := leak') h hpre hpost hleak hsat

end VG.X86_64
