module

public import VerifiedGarbage.Proof.Framework.AppendSlice
public import VerifiedGarbage.Proof.Framework.Arm.Inline

/-!
# Contracts with one more read-only slice argument (ARMv7)

`Verified.withSlice` for AAPCS, with tables of functions (`Abi.withTables`)
or none, for signatures of more than four 32-bit words: the first four in
`r0`–`r3`, the others on the stack (`locAt`), the slice's two last, on the
stack after those of the shorter signature, whose tables are among them
(`verified_withSlice`).
-/

@[expose] public section

namespace VG.Arm

/-- Where AAPCS passes the `i`-th of 32-bit arguments. -/
def locAt (i : Nat) : Loc :=
  if h : i < 4 then .reg (argRegs[i]'(by simp [argRegs]; omega_using [h])) else .stack (4 * (i - 4)) 32

/-- The arguments of a signature of `n` 32-bit words. -/
def wordVals (n : Nat) (s : State) : List (BitVec 64) := (List.range n).map fun i => Loc.val s (locAt i)

theorem classify_all32 : ∀ (ws : List Nat) (i : Nat), (∀ w ∈ ws, w = 32) →
    classify ws (min i 4) (4 * (i - 4)) = ((List.range' i ws.length).map locAt, 4 * (i + ws.length - 4))
  | [], i, _ => by simp [classify]
  | w :: ws, i, h => by
    have hw := h w (List.mem_cons_self ..)
    subst hw
    have ih := classify_all32 ws (i + 1) (fun w hw => h w (List.mem_cons_of_mem _ hw))
    simp only [List.length_cons, List.range'_succ, List.map_cons]
    rw [classify]
    simp only [show (32 : Nat) ≠ 64 by decide, ↓reduceIte]
    by_cases hi : i < 4
    · have hm : min i 4 = i := by omega_using [hi]
      have hm' : min (i + 1) 4 = i + 1 := by omega_using [hi]
      rw [hm] at ⊢
      rw [hm'] at ih
      have hs : i - 4 = 0 := by omega_using [hi]
      have hs' : i + 1 - 4 = 0 := by omega_using [hi]
      rw [hs'] at ih
      rw [hs]
      rcases i with _ | _ | _ | _ | i
      · simp only [argRegs, List.getElem?_cons_zero]; rw [ih]; simp [locAt, argRegs]; omega_using []
      · simp only [argRegs, List.getElem?_cons_succ, List.getElem?_cons_zero]; rw [ih]; simp [locAt, argRegs]; omega_using []
      · simp only [argRegs, List.getElem?_cons_succ, List.getElem?_cons_zero]; rw [ih]; simp [locAt, argRegs]; omega_using []
      · simp only [argRegs, List.getElem?_cons_succ, List.getElem?_cons_zero]; rw [ih]; simp [locAt, argRegs]; omega_using []
      · omega
    · have hm : min i 4 = 4 := by omega_using [hi]
      have hm' : min (i + 1) 4 = 4 := by omega_using [hi]
      rw [hm]
      rw [hm'] at ih
      have hn : argRegs[4]? = none := rfl
      rw [hn]
      simp only [show argRegs.length = 4 from rfl, show 4 * (i - 4) + 4 = 4 * (i + 1 - 4) by omega_using [hi]]
      rw [ih]
      simp only [locAt, hi, dite_false, Prod.mk.injEq, true_and]
      omega_using []

theorem abi_args_all32 (ws : List Nat) (h : ∀ w ∈ ws, w = 32) :
    abi.args ws = some (wordVals ws.length) := by
  have hall : ws.all (fun w => w = 32 ∨ w = 64) = true := List.all_eq_true.mpr fun w hw => by simp [h w hw]
  simp only [abi, hall, ↓reduceIte, Option.some.injEq]
  funext s
  have := classify_all32 ws 0 h
  simp only [Nat.zero_min, Nat.zero_sub, Nat.mul_zero, Nat.zero_add] at this
  rw [this, List.map_map, wordVals, List.range_eq_range']
  rfl

theorem classify_all32_snd (ws : List Nat) (h : ∀ w ∈ ws, w = 32) : (classify ws 0 0).2 = 4 * (ws.length - 4) := by
  have := classify_all32 ws 0 h
  simp only [Nat.zero_min, Nat.zero_sub, Nat.mul_zero, Nat.zero_add] at this
  rw [this]

theorem wordVals_succ2 (n : Nat) (s : State) :
    wordVals (n + 2) s = wordVals n s ++ [Loc.val s (locAt n), Loc.val s (locAt (n + 1))] := by
  simp [wordVals, List.range_succ]

theorem wordVals_length (n : Nat) (s : State) : (wordVals n s).length = n := by simp [wordVals]

theorem wordVals_withRegions (n : Nat) (s : State) (r w : List Region) :
    wordVals n (s.withRegions r w) = wordVals n s := rfl

theorem words_withSlice_map (sig : Sig) (nm : String) (e : Elem) (ln : String) :
    ((sig.withSlice nm e ln).words 32).map (·.bits 32) = (sig.words 32).map (·.bits 32) ++ [32, 32] := by
  rw [Sig.words_withSlice]; simp [ArgWord.bits]

theorem all32_append {ws : List Nat} (h : ∀ w ∈ ws, w = 32) : ∀ w ∈ ws ++ [32, 32], w = 32 := by
  intro w hw
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with hw | hw | hw
  · exact h w hw
  · exact hw
  · exact hw

theorem abi_wf_append {ws : List Nat} (hw : ∀ w ∈ ws, w = 32) (hne : 4 < ws.length) {n : Nat} {s : State}
    (h : abi.wf (ws ++ [32, 32]) n s) (r w : List Region) : abi.wf ws n (s.withRegions r w) := by
  have e₁ := classify_all32_snd ws hw
  have e₂ := classify_all32_snd _ (all32_append hw)
  simp only [List.length_append, List.length_cons, List.length_nil] at e₂
  have hsp : (s.withRegions r w).sp = s.sp := State.withRegions_sp _ _ _
  cases n <;> simp only [abi, e₁, e₂, hsp] at h ⊢ <;> omega

theorem abi_area_append {ws : List Nat} (hw : ∀ w ∈ ws, w = 32) (hne : 4 < ws.length) (s : State) :
    List.Forall₂ RegionBelow (abi.argArea ws s) (abi.argArea (ws ++ [32, 32]) s) := by
  have e₁ := classify_all32_snd ws hw
  have e₂ := classify_all32_snd _ (all32_append hw)
  simp only [List.length_append, List.length_cons, List.length_nil] at e₂
  have h₁ : 4 * (ws.length - 4) ≠ 0 := by omega_using [hne]
  have h₂ : 4 * (ws.length + (1 + 1) - 4) ≠ 0 := by omega_using [hne]
  simp only [abi, e₁, e₂, h₁, h₂, ↓reduceIte]
  exact .cons ⟨⟨rfl, by simp only; omega_using []⟩, rfl⟩ .nil

/-- The words of `sig`'s arguments followed by a slice's two. -/
abbrev sliceVals (n : Nat) (s : State) : List (BitVec 64) :=
  wordVals n s ++ [Loc.val s (locAt n), Loc.val s (locAt (n + 1))]

/-- `Verified.withSlice` on ARMv7, for contracts without tables of functions:
every argument a 32-bit word. -/
theorem verified_withSlice {sig : Sig} {nm ln : String} {e : Elem}
    (hw : ∀ w ∈ (sig.words 32).map (·.bits 32), w = 32) (hne : 4 < (sig.words 32).length)
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
    (X := fun s => Loc.val s (locAt (sig.words 32).length)) (Y := fun s => Loc.val s (locAt ((sig.words 32).length + 1)))
    ha ha' (fun s => wordVals_length _ s) (fun _ _ _ => rfl)
    (fun n s r w h => abi_wf_append (ws := (sig.words 32).map (·.bits 32)) hw (by rw [List.length_map]; exact hne)
      (by have h' : abi.wf (((sig.withSlice nm e ln).words 32).map (·.bits 32)) n s := h
          rw [words_withSlice_map] at h'; exact h') r w)
    (fun s => by
      have := abi_area_append hw (by rw [List.length_map]; exact hne) s
      rw [← words_withSlice_map sig nm e ln] at this
      exact this)
    (fun _ _ _ => rfl)
    (c := c) (writeArgs := writeArgs) (stack := stack) (pre := pre) (post := post) (leak := leak)
    (pre' := pre') (post' := post') (leak' := leak') h hpre hpost hleak hsat

/-- `Verified.withSlice` on ARMv7, for contracts with the tables `t :: ts`, which
the shorter signature names: every argument a 32-bit word. -/
theorem verified_withSlice_tables {sig : Sig} {nm ln : String} {e : Elem} {t : String × List FnTable} {ts : List (String × List FnTable)}
    (hts : ∀ u ∈ t :: ts, ∃ k, Sig.wordIndex sig.params u.1 = some k ∧ k < (sig.words 32).length)
    (hw : ∀ w ∈ (sig.words 32).map (·.bits 32), w = 32) (hne : 4 < (sig.words 32).length)
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
    (X := fun s => Loc.val s (locAt (sig.words 32).length)) (Y := fun s => Loc.val s (locAt ((sig.words 32).length + 1)))
    ha ha' (fun s => wordVals_length _ s) (fun _ _ _ => rfl)
    (fun n s r w hwf => by
      simp only [Abi.withTables, show abi.ptrBits = 32 from rfl] at hwf ⊢
      rw [ha'] at hwf
      rw [ha]
      obtain ⟨h₁, h₂, h₃⟩ := hwf
      refine ⟨abi_wf_append hw (by rw [List.length_map]; exact hne) (by rw [← words_withSlice_map sig nm e ln]; exact h₁) r w, fun t' ht' => ?_, h₃⟩
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

end VG.Arm
