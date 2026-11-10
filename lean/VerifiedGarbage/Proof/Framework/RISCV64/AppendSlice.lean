module

public import VerifiedGarbage.Proof.Framework.AppendSlice
public import VerifiedGarbage.Proof.Framework.RISCV64.RelCT

/-!
# Contracts with one more read-only slice argument (RISC-V)

`Verified.withSlice` for RISC-V's calling convention, for signatures of more
than eight words: the first eight in `a0`–`a7`, the others, the slice's two
last, on the stack (`verified_withSlice`). Both contracts require aligned
buffers (`Abi.alignsBufs`).
-/

@[expose] public section

namespace VG.RISCV64

/-- The arguments of a signature of `n ≥ 8` words of at most 64 bits. -/
def stackVals (n : Nat) (s : State) : List (BitVec 64) :=
  argRegs.map s.gpr ++ (List.range (n - 8)).map (stackArg s)

theorem argRegs_length : argRegs.length = 8 := rfl

theorem abi_args_long (ws : List Nat) (h8 : 8 < ws.length) (h64 : ∀ w ∈ ws, w ≤ 64) :
    abi.args ws = some (stackVals ws.length) := by
  have hd : ((ws.drop argRegs.length).all fun w => decide (w ≤ 64)) = true :=
    List.all_eq_true.mpr fun w hw => decide_eq_true (h64 w (List.mem_of_mem_drop hw))
  simp only [abi, argRegs_length, show ¬ ws.length ≤ 8 by omega, ↓reduceIte]
  rw [argRegs_length] at hd
  simp only [hd, ↓reduceIte]
  rfl

theorem stackVals_succ2 (n : Nat) (h : 8 ≤ n) (s : State) :
    stackVals (n + 2) s = stackVals n s ++ [stackArg s (n - 8), stackArg s (n - 8 + 1)] := by
  simp only [stackVals, show n + 2 - 8 = n - 8 + 1 + 1 by omega, List.range_succ, List.map_append,
    List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append]

theorem stackVals_length (n : Nat) (h : 8 ≤ n) (s : State) : (stackVals n s).length = n := by
  simp [stackVals, argRegs_length]; omega

theorem words_withSlice_map64 (sig : Sig) (nm : String) (e : Elem) (ln : String) :
    ((sig.withSlice nm e ln).words 64).map (·.bits 64) = (sig.words 64).map (·.bits 64) ++ [64, 64] := by
  rw [Sig.words_withSlice]; simp [ArgWord.bits]

theorem abi_wf_append {ws : List Nat} {n : Nat} {s : State} (h : abi.wf (ws ++ [64, 64]) n s)
    (r w : List Region) : abi.wf ws n (s.withRegions r w) := by
  obtain ⟨a, b, c⟩ := h
  refine ⟨a, b, ?_⟩
  change ws.length ≤ argRegs.length ∨ s.sp.toNat + 8 * (ws.length - argRegs.length) ≤ 2 ^ 64
  simp only [List.length_append, List.length_cons, List.length_nil] at c
  rw [argRegs_length] at c ⊢
  omega

theorem abi_area_append {ws : List Nat} (h8 : 8 < ws.length) (s : State) :
    List.Forall₂ RegionBelow (abi.argArea ws s) (abi.argArea (ws ++ [64, 64]) s) := by
  simp only [abi, List.length_append, List.length_cons, List.length_nil, argRegs_length,
    show ws.length - 8 ≠ 0 by omega, show ws.length + (0 + 1 + 1) - 8 ≠ 0 by omega, ↓reduceIte]
  refine List.forall₂_cons.mpr ⟨?_, .nil⟩
  refine ⟨⟨rfl, ?_⟩, rfl⟩
  show 8 * (ws.length - 8) ≤ 8 * (ws.length + (0 + 1 + 1) - 8)
  omega

/-- `Verified.withSlice` on RISC-V, for a signature of more than eight words of
at most 64 bits. -/
theorem verified_withSlice {sig : Sig} {nm ln : String} {e : Elem}
    (hw : ∀ w ∈ (sig.words 64).map (·.bits 64), w ≤ 64) (h8 : 8 < (sig.words 64).length)
    {c : Prog isa} {writeArgs : Bool} {stack : Nat}
    {pre : Curry (sig.words 64) (Mem → Prop)} {post : sig.Post 64}
    {leak : Option (Curry (sig.words 64) (Mem → List Nat))}
    {pre' : Curry ((sig.withSlice nm e ln).words 64) (Mem → Prop)}
    {post' : (sig.withSlice nm e ln).Post 64}
    {leak' : Option (Curry ((sig.withSlice nm e ln).words 64) (Mem → List Nat))}
    (h : Verified target c (sig.contract abi pre post writeArgs stack leak))
    (hpre : ∀ s, Curry.apply _ pre' (stackVals ((sig.words 64).length + 2) s) s.mem →
      Curry.apply _ pre (stackVals (sig.words 64).length s) s.mem)
    (hpost : ∀ s m' (v : BitVec 64), Curry.apply _ pre' (stackVals ((sig.words 64).length + 2) s) s.mem →
      Curry.apply _ post (stackVals (sig.words 64).length s) s.mem m' (v.setWidth _) →
      Curry.apply _ post' (stackVals ((sig.words 64).length + 2) s) s.mem m' (v.setWidth _))
    (hleak : ∀ s₁ s₂, Curry.apply _ pre' (stackVals ((sig.words 64).length + 2) s₁) s₁.mem →
      Curry.apply _ pre' (stackVals ((sig.words 64).length + 2) s₂) s₂.mem →
      (∀ i, (sig.params.flatMap (·.2.pubs)).getD i false = true →
        ((stackVals (sig.words 64).length s₁).getD i 0).setWidth (((sig.words 64).map (·.bits 64)).getD i 64) =
          ((stackVals (sig.words 64).length s₂).getD i 0).setWidth (((sig.words 64).map (·.bits 64)).getD i 64)) →
      leakAgree leak' (stackVals ((sig.words 64).length + 2) s₁) s₁.mem
        (stackVals ((sig.words 64).length + 2) s₂) s₂.mem →
      leakAgree leak (stackVals (sig.words 64).length s₁) s₁.mem (stackVals (sig.words 64).length s₂) s₂.mem)
    (hsat : ∃ s, ((sig.withSlice nm e ln).contract abi pre' post' writeArgs stack leak').pre s) :
    Verified target c ((sig.withSlice nm e ln).contract abi pre' post' writeArgs stack leak') := by
  have hw' : ∀ w ∈ ((sig.withSlice nm e ln).words 64).map (·.bits 64), w ≤ 64 := by
    rw [words_withSlice_map64]; simp only [List.mem_append]
    rintro w (hw₁ | hw₁)
    · exact hw w hw₁
    · simp at hw₁; omega
  have hn : (((sig.withSlice nm e ln).words 64).map (·.bits 64)).length = (sig.words 64).length + 2 := by
    rw [words_withSlice_map64]; simp
  have ha : abi.args ((sig.words 64).map (·.bits 64)) = some (stackVals (sig.words 64).length) := by
    rw [abi_args_long _ (by rw [List.length_map]; exact h8) hw, List.length_map]
  have ha' : abi.args (((sig.withSlice nm e ln).words 64).map (·.bits 64)) =
      some fun s => stackVals (sig.words 64).length s ++
        [stackArg s ((sig.words 64).length - 8), stackArg s ((sig.words 64).length - 8 + 1)] := by
    rw [abi_args_long _ (by omega) hw', hn]
    congr 1; funext s; exact stackVals_succ2 _ (by omega) s
  have hv2 : ∀ s, stackVals ((sig.words 64).length + 2) s = stackVals (sig.words 64).length s ++
      [stackArg s ((sig.words 64).length - 8), stackArg s ((sig.words 64).length - 8 + 1)] :=
    fun s => stackVals_succ2 _ (by omega) s
  exact Verified.withSlice (T := target) regionModel (fun _ _ _ _ h => h) abi abi rfl (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ _ _ _ h => h) (fun _ _ _ _ => rfl) rfl
    (sig := sig) (nm := nm) (e := e) (ln := ln) (vals := stackVals (sig.words 64).length)
    (X := fun s => stackArg s ((sig.words 64).length - 8))
    (Y := fun s => stackArg s ((sig.words 64).length - 8 + 1))
    ha ha' (fun s => stackVals_length _ (by omega) s) (fun _ _ _ => rfl)
    (fun n s r w hwf => by
      have h' : abi.wf (((sig.withSlice nm e ln).words 64).map (·.bits 64)) n s := hwf
      rw [words_withSlice_map64] at h'
      exact abi_wf_append h' r w)
    (fun s => by
      have := abi_area_append (ws := (sig.words 64).map (·.bits 64)) (by rw [List.length_map]; exact h8) s
      rw [← words_withSlice_map64 sig nm e ln] at this
      exact this)
    (fun _ _ _ => rfl)
    (c := c) (writeArgs := writeArgs) (stack := stack) (pre := pre) (post := post) (leak := leak)
    (pre' := pre') (post' := post') (leak' := leak') h
    (fun s hp => hpre s (by rw [hv2]; exact hp))
    (fun s m' v hp hq => by rw [← hv2]; exact hpost s m' v (by rw [hv2]; exact hp) hq)
    (fun s₁ s₂ h₁ h₂ hpo hl => hleak s₁ s₂ (by rw [hv2]; exact h₁) (by rw [hv2]; exact h₂) hpo
      (by rw [hv2, hv2]; exact hl))
    hsat

end VG.RISCV64
