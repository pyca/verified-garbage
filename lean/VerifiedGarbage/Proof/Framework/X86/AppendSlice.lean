module

public import VerifiedGarbage.Proof.Framework.AppendSlice
public import VerifiedGarbage.Proof.Framework.X86.Inline

/-!
# Contracts with one more read-only slice argument (x86)

`Verified.withSlice` for x86's calling convention, with tables of functions
(`Abi.withTables`) or none: every argument a 32-bit word on the stack, the
slice's two last, after those of the shorter signature, whose tables are among
them (`verified_withSlice`).
-/

@[expose] public section

namespace VG.X86

/-- The arguments of a signature of `n` 32-bit words. -/
def wordVals (n : Nat) (s : State) : List (BitVec 64) := (List.range n).map (argVal s 32)

theorem argSlots_all32 : ∀ (ws : List Nat) (i : Nat), (∀ w ∈ ws, w = 32) →
    argSlots ws i = List.range' i ws.length
  | [], _, _ => rfl
  | w :: ws, i, h => by
    have hw := h w (List.mem_cons_self ..)
    subst hw
    simp only [argSlots, List.length_cons, List.range'_succ]
    rw [argSlots_all32 ws (i + 1) (fun w hw => h w (List.mem_cons_of_mem _ hw))]

theorem zip_range' : ∀ (ws : List Nat) (i : Nat), (∀ w ∈ ws, w = 32) →
    (ws.zip (List.range' i ws.length)).map (fun (w, j) => (w, j)) = (List.range' i ws.length).map fun j => (32, j)
  | [], _, _ => rfl
  | w :: ws, i, h => by
    have hw := h w (List.mem_cons_self ..)
    subst hw
    simp only [List.length_cons, List.range'_succ, List.zip_cons_cons, List.map_cons]
    rw [zip_range' ws (i + 1) (fun w hw => h w (List.mem_cons_of_mem _ hw))]

theorem abi_args_all32 (ws : List Nat) (h : ∀ w ∈ ws, w = 32) :
    abi.args ws = some (wordVals ws.length) := by
  have hall : ws.all (fun w => w = 32 ∨ w = 64) = true := List.all_eq_true.mpr fun w hw => by simp [h w hw]
  simp only [abi, hall, ↓reduceIte, Option.some.injEq]
  funext s
  rw [argSlots_all32 ws 0 h]
  have := zip_range' ws 0 h
  simp only [List.map_id'] at this
  rw [this, List.map_map, wordVals, List.range_eq_range']
  rfl

theorem wordVals_succ2 (n : Nat) (s : State) :
    wordVals (n + 2) s = wordVals n s ++ [argVal s 32 n, argVal s 32 (n + 1)] := by
  simp [wordVals, List.range_succ]

theorem wordVals_length (n : Nat) (s : State) : (wordVals n s).length = n := by simp [wordVals]

theorem wordVals_withRegions (n : Nat) (s : State) (r w : List Region) :
    wordVals n (s.withRegions r w) = wordVals n s := rfl

theorem argBytes_append2 (ws : List Nat) : argBytes (ws ++ [32, 32]) = argBytes ws + 8 := by
  simp [argBytes, List.map_append, List.sum_append]; omega_using []

theorem argBytes_pos (ws : List Nat) (h : ∀ w ∈ ws, w = 32) (hne : 0 < ws.length) : 0 < argBytes ws := by
  obtain ⟨w, ws', rfl⟩ := List.exists_cons_of_length_pos hne
  have := h w (List.mem_cons_self ..)
  subst this
  simp [argBytes]; omega_using []

theorem words_withSlice_map (sig : Sig) (nm : String) (e : Elem) (ln : String) :
    ((sig.withSlice nm e ln).words 32).map (·.bits 32) = (sig.words 32).map (·.bits 32) ++ [32, 32] := by
  rw [Sig.words_withSlice]; simp [ArgWord.bits]

theorem abi_wf_append {ws : List Nat} {n : Nat} {s : State} (h : abi.wf (ws ++ [32, 32]) n s)
    (r w : List Region) : abi.wf ws n (s.withRegions r w) := by
  have := argBytes_append2 ws
  cases n <;> simp only [abi, State.withRegions_gpr] at h ⊢ <;> omega_using [this, h]

theorem abi_area_append {ws : List Nat} (h : ∀ w ∈ ws, w = 32) (hne : 0 < ws.length) (s : State) :
    List.Forall₂ RegionBelow (abi.argArea ws s) (abi.argArea (ws ++ [32, 32]) s) := by
  have hp := argBytes_pos ws h hne
  have := argBytes_append2 ws
  have h8 : argBytes ws + 8 ≠ 0 := by omega_using []
  simp only [abi, Nat.pos_iff_ne_zero.mp hp, ↓reduceIte, this, h8]
  exact .cons ⟨⟨rfl, by simp only; omega_using []⟩, rfl⟩ .nil

/-- The words of `sig`'s arguments followed by a slice's two. -/
abbrev sliceVals (n : Nat) (s : State) : List (BitVec 64) :=
  wordVals n s ++ [argVal s 32 n, argVal s 32 (n + 1)]

/-- `Verified.withSlice` on x86, for contracts without tables of functions:
every argument a 32-bit word. -/
theorem verified_withSlice {sig : Sig} {nm ln : String} {e : Elem}
    (hw : ∀ w ∈ (sig.words 32).map (·.bits 32), w = 32) (hne : 0 < (sig.words 32).length)
    {c : Prog isa} {writeArgs : Bool} {stack : Nat}
    {pre : Curry (sig.words 32) (Mem → Prop)} {post : sig.Post 32}
    {leak : Option (Curry (sig.words 32) (Mem → List Nat))}
    {pre' : Curry ((sig.withSlice nm e ln).words 32) (Mem → Prop)}
    {post' : (sig.withSlice nm e ln).Post 32}
    {leak' : Option (Curry ((sig.withSlice nm e ln).words 32) (Mem → List Nat))}
    (h : Verified target c (sig.contract abi pre post writeArgs stack leak))
    (hpre : ∀ s, Curry.apply _ pre' (sliceVals (sig.words 32).length s) s.mem →
      Curry.apply _ pre (wordVals (sig.words 32).length s) s.mem)
    (hpost : ∀ s m' (v : BitVec 64), Curry.apply _ pre' (sliceVals (sig.words 32).length s) s.mem →
      Curry.apply _ post (wordVals (sig.words 32).length s) s.mem m' (v.setWidth _) →
      Curry.apply _ post' (sliceVals (sig.words 32).length s) s.mem m' (v.setWidth _))
    (hleak : ∀ s₁ s₂, Curry.apply _ pre' (sliceVals (sig.words 32).length s₁) s₁.mem →
      Curry.apply _ pre' (sliceVals (sig.words 32).length s₂) s₂.mem →
      (∀ i, (sig.params.flatMap (·.2.pubs)).getD i false = true →
        ((wordVals (sig.words 32).length s₁).getD i 0).setWidth (((sig.words 32).map (·.bits 32)).getD i 64) =
          ((wordVals (sig.words 32).length s₂).getD i 0).setWidth (((sig.words 32).map (·.bits 32)).getD i 64)) →
      leakAgree leak' (sliceVals (sig.words 32).length s₁) s₁.mem (sliceVals (sig.words 32).length s₂) s₂.mem →
      leakAgree leak (wordVals (sig.words 32).length s₁) s₁.mem (wordVals (sig.words 32).length s₂) s₂.mem)
    (hsat : ∃ s, ((sig.withSlice nm e ln).contract abi pre' post' writeArgs stack leak').pre s) :
    Verified target c ((sig.withSlice nm e ln).contract abi pre' post' writeArgs stack leak') := by
  have hw' : ∀ w ∈ ((sig.withSlice nm e ln).words 32).map (·.bits 32), w = 32 := by
    rw [Sig.words_withSlice]; simp only [List.map_append, List.mem_append]
    rintro w (hw₁ | hw₁)
    · exact hw w hw₁
    · simp [ArgWord.bits] at hw₁; exact hw₁
  have hn : (((sig.withSlice nm e ln).words 32).map (·.bits 32)).length = (sig.words 32).length + 2 := by
    rw [Sig.words_withSlice]; simp
  have ha : abi.args ((sig.words 32).map (·.bits 32)) = some (wordVals (sig.words 32).length) := by
    rw [abi_args_all32 _ hw, List.length_map]
  have ha' : abi.args (((sig.withSlice nm e ln).words 32).map (·.bits 32)) =
      some (sliceVals (sig.words 32).length) := by
    rw [abi_args_all32 _ hw', hn]; congr 1; funext s; exact wordVals_succ2 _ s
  have hret : ∀ (s : State) (r w : List Region), abi.ret (s.withRegions r w) = abi.ret s := fun _ _ _ => rfl
  have hres : ∀ n (s : State) (r w : List Region), abi.reserved n (s.withRegions r w) = abi.reserved n s :=
    fun _ _ _ _ => rfl
  have hpubA : ∀ (s₁ s₂ : State) r₁ w₁ r₂ w₂, abi.pub s₁ s₂ → abi.pub (s₁.withRegions r₁ w₁) (s₂.withRegions r₂ w₂) :=
    fun _ _ _ _ _ _ h => h
  exact Verified.withSlice (T := target) regionModel (fun _ _ _ _ h => h) abi abi rfl (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hret hpubA hres rfl
    (sig := sig) (nm := nm) (e := e) (ln := ln) (vals := wordVals (sig.words 32).length)
    (X := fun s => argVal s 32 (sig.words 32).length) (Y := fun s => argVal s 32 ((sig.words 32).length + 1))
    ha ha' (fun s => wordVals_length _ s) (fun _ _ _ => rfl)
    (fun n s r w h => abi_wf_append (ws := (sig.words 32).map (·.bits 32))
      (by have h' : abi.wf (((sig.withSlice nm e ln).words 32).map (·.bits 32)) n s := h
          rw [words_withSlice_map] at h'; exact h') r w)
    (fun s => by
      have := abi_area_append hw (by rw [List.length_map]; exact hne) s
      rw [← words_withSlice_map sig nm e ln] at this
      exact this)
    (fun _ _ _ => rfl)
    (c := c) (writeArgs := writeArgs) (stack := stack) (pre := pre) (post := post) (leak := leak)
    (pre' := pre') (post' := post') (leak' := leak') h hpre hpost hleak hsat

/-- `Verified.withSlice` on x86, for contracts with the tables `t :: ts`, which
the shorter signature names: every argument a 32-bit word. -/
theorem verified_withSlice_tables {sig : Sig} {nm ln : String} {e : Elem} {t : String × List FnTable} {ts : List (String × List FnTable)}
    (hts : ∀ u ∈ t :: ts, ∃ k, Sig.wordIndex sig.params u.1 = some k ∧ k < (sig.words 32).length)
    (hw : ∀ w ∈ (sig.words 32).map (·.bits 32), w = 32) (hne : 0 < (sig.words 32).length)
    {c : Prog isa} {writeArgs : Bool} {stack : Nat}
    {pre : Curry (sig.words 32) (Mem → Prop)} {post : sig.Post 32}
    {leak : Option (Curry (sig.words 32) (Mem → List Nat))}
    {pre' : Curry ((sig.withSlice nm e ln).words 32) (Mem → Prop)}
    {post' : (sig.withSlice nm e ln).Post 32}
    {leak' : Option (Curry ((sig.withSlice nm e ln).words 32) (Mem → List Nat))}
    (h : Verified target c (sig.contract (abi.withTables sig (t :: ts)) pre post writeArgs stack leak))
    (hpre : ∀ s, Curry.apply _ pre' (sliceVals (sig.words 32).length s) s.mem →
      Curry.apply _ pre (wordVals (sig.words 32).length s) s.mem)
    (hpost : ∀ s m' (v : BitVec 64), Curry.apply _ pre' (sliceVals (sig.words 32).length s) s.mem →
      Curry.apply _ post (wordVals (sig.words 32).length s) s.mem m' (v.setWidth _) →
      Curry.apply _ post' (sliceVals (sig.words 32).length s) s.mem m' (v.setWidth _))
    (hleak : ∀ s₁ s₂, Curry.apply _ pre' (sliceVals (sig.words 32).length s₁) s₁.mem →
      Curry.apply _ pre' (sliceVals (sig.words 32).length s₂) s₂.mem →
      (∀ i, (sig.params.flatMap (·.2.pubs)).getD i false = true →
        ((wordVals (sig.words 32).length s₁).getD i 0).setWidth (((sig.words 32).map (·.bits 32)).getD i 64) =
          ((wordVals (sig.words 32).length s₂).getD i 0).setWidth (((sig.words 32).map (·.bits 32)).getD i 64)) →
      leakAgree leak' (sliceVals (sig.words 32).length s₁) s₁.mem (sliceVals (sig.words 32).length s₂) s₂.mem →
      leakAgree leak (wordVals (sig.words 32).length s₁) s₁.mem (wordVals (sig.words 32).length s₂) s₂.mem)
    (hsat : ∃ s, ((sig.withSlice nm e ln).contract (abi.withTables (sig.withSlice nm e ln) (t :: ts)) pre' post' writeArgs stack leak').pre s) :
    Verified target c ((sig.withSlice nm e ln).contract (abi.withTables (sig.withSlice nm e ln) (t :: ts)) pre' post' writeArgs stack leak') := by
  have hw' : ∀ w ∈ ((sig.withSlice nm e ln).words 32).map (·.bits 32), w = 32 := by
    rw [Sig.words_withSlice]; simp only [List.map_append, List.mem_append]
    rintro w (hw₁ | hw₁)
    · exact hw w hw₁
    · simp [ArgWord.bits] at hw₁; exact hw₁
  have hn : (((sig.withSlice nm e ln).words 32).map (·.bits 32)).length = (sig.words 32).length + 2 := by
    rw [Sig.words_withSlice]; simp
  have ha : abi.args ((sig.words 32).map (·.bits 32)) = some (wordVals (sig.words 32).length) := by
    rw [abi_args_all32 _ hw, List.length_map]
  have ha' : abi.args (((sig.withSlice nm e ln).words 32).map (·.bits 32)) =
      some (sliceVals (sig.words 32).length) := by
    rw [abi_args_all32 _ hw', hn]; congr 1; funext s; exact wordVals_succ2 _ s
  have hret : ∀ (s : State) (r w : List Region), abi.ret (s.withRegions r w) = abi.ret s := fun _ _ _ => rfl
  have hres : ∀ n (s : State) (r w : List Region), abi.reserved n (s.withRegions r w) = abi.reserved n s :=
    fun _ _ _ _ => rfl
  -- The tables' addresses, the same arguments of either signature.
  have harg : ∀ (s : State) (x : String) (k : Nat), Sig.wordIndex sig.params x = some k →
      k < (sig.words 32).length →
      (Sig.wordIndex (sig.withSlice nm e ln).params x).map (fun k => (sliceVals (sig.words 32).length s).getD k 0) =
        (Sig.wordIndex sig.params x).map (fun k => (wordVals (sig.words 32).length s).getD k 0) := by
    intro s x k hk hlt
    rw [show (sig.withSlice nm e ln).params = sig.params ++ [(nm, .slice false e ln)] from rfl,
      Sig.wordIndex_append _ _ _ _ hk, hk]
    simp only [Option.map_some, sliceVals]
    rw [getD_append_lt _ _ _ (by rw [wordVals_length]; exact hlt)]
  exact Verified.withSlice (T := target) regionModel (fun _ _ _ _ h => h) (abi.withTables sig (t :: ts))
    (abi.withTables (sig.withSlice nm e ln) (t :: ts)) rfl (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hret
    (fun s₁ s₂ r₁ w₁ r₂ w₂ hp => by
      simp only [Abi.withTables, show abi.ptrBits = 32 from rfl] at hp ⊢
      rw [ha'] at hp
      rw [ha]
      obtain ⟨h₁, h₂, h₃⟩ := hp
      refine ⟨h₁, h₂, fun t' ht' p₁ p₂ e₁ e₂ T hT => ?_⟩
      obtain ⟨k, hk, hlt⟩ := hts t' ht'
      have e₁' : Option.map (fun k => (wordVals (sig.words 32).length s₁).getD k 0)
          (Sig.wordIndex sig.params t'.1) = some p₁ := e₁
      have e₂' : Option.map (fun k => (wordVals (sig.words 32).length s₂).getD k 0)
          (Sig.wordIndex sig.params t'.1) = some p₂ := e₂
      rw [← harg s₁ t'.1 k hk hlt] at e₁'
      rw [← harg s₂ t'.1 k hk hlt] at e₂'
      exact h₃ t' ht' p₁ p₂ e₁' e₂' T hT)
    hres rfl
    (sig := sig) (nm := nm) (e := e) (ln := ln) (vals := wordVals (sig.words 32).length)
    (X := fun s => argVal s 32 (sig.words 32).length) (Y := fun s => argVal s 32 ((sig.words 32).length + 1))
    ha ha' (fun s => wordVals_length _ s) (fun _ _ _ => rfl)
    (fun n s r w hwf => by
      simp only [Abi.withTables, show abi.ptrBits = 32 from rfl] at hwf ⊢
      rw [ha'] at hwf
      rw [ha]
      obtain ⟨h₁, h₂, h₃⟩ := hwf
      refine ⟨abi_wf_append (by rw [← words_withSlice_map sig nm e ln]; exact h₁) r w, fun t' ht' => ?_, h₃⟩
      obtain ⟨p, hp, T, hT, hh⟩ := h₂ t' ht'
      obtain ⟨k, hk, hlt⟩ := hts t' ht'
      rw [harg s t'.1 k hk hlt] at hp
      exact ⟨p, hp, T, hT, hh⟩)
    (fun s => by
      have := abi_area_append hw (by rw [List.length_map]; exact hne) s
      rw [← words_withSlice_map sig nm e ln] at this
      exact this)
    (fun _ _ _ => rfl)
    (c := c) (writeArgs := writeArgs) (stack := stack) (pre := pre) (post := post) (leak := leak)
    (pre' := pre') (post' := post') (leak' := leak') h hpre hpost hleak hsat

end VG.X86
