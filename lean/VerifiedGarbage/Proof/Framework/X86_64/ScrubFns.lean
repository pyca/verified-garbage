module

public import VerifiedGarbage.Proof.Framework.X86_64.ScrubProved
public import VerifiedGarbage.TCB.Registration

/-!
# Scrubbed code that calls functions of public address (x86-64)

`verifiedScrubbedAllF` (`ScrubProved.lean`) asks that code call indirectly
only the functions of its tables. Code under a calling convention with
functions of public address (`Abi.withFns`, e.g. a body that calls the
functions whose addresses its caller leaves it, `Code.icalls i [(n, b)]`)
may call those too: two runs that agree on what is public agree on their
addresses, which is what `Verified.scrubM` needs of the functions code calls
indirectly. `verifiedScrubbedAllFns` is `verifiedScrubbedAllF` for such a
contract, stated of the contract itself.

`fillI` puts the candidates of code's indirect calls in place of stubs, as
`fillCallsG` does the holes of its direct calls: the cleanup's side
conditions of the code then follow from those of its code over the stubs,
which the kernel evaluates once, and of the candidates (`fillI_allInstrs`,
`fillI_inames`).
-/

@[expose] public section

namespace VG.X86_64.Scrub

open VG.Impl.Scrub.X86_64

/-! ## The calling convention -/

/-- The calling convention with the functions `x :: xs` of public address is
one the cleanup takes: `Abi.withFns` changes only what is public. -/
theorem scrubAbi_fns (x : String) (xs : List String) : ScrubAbi (abi.withFns (x :: xs)) :=
  ⟨rfl, rfl, fun _ => rfl, ScrubAbi.plain.wf, fun _ _ h => ScrubAbi.plain.pub _ _ h.1, fun _ => rfl,
    fun _ => rfl, ScrubAbi.plain.rdSub, abi_args_len, fun _ => rfl, abi_argRo, fun _ _ => rfl,
    ScrubAbi.plain.wfAbi⟩

section
variable {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {wa : Bool} {stack : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}
  {x : String} {xs : List String}

/-- Two runs that agree on what is public under `Abi.withFns` agree on the
addresses of its functions. -/
theorem fns_pub {s₁ s₂ : State}
    (h : (sig.contract (abi.withFns (x :: xs)) pre post wa stack leak).pub s₁ s₂) :
    ∀ g ∈ x :: xs, s₁.syms g = s₂.syms g :=
  (contract_pub h).2

/-- Code verified against a contract, constant time given also that two runs
agree on the addresses of the functions `x :: xs`, is verified against the
contract under `Abi.withFns (x :: xs)`. -/
theorem verified_withFns {c : Prog isa}
    (hok : ∀ s, (sig.contract abi pre post wa stack leak).pre s → ∃ t s', Exec isa c s t s' ∧
      X86_64.target.abiPreserved s s' ∧ (sig.contract abi pre post wa stack leak).post s s')
    (hct : ConstantTime isa (sig.contract abi pre post wa stack leak).pre
      (fun s₁ s₂ => (sig.contract abi pre post wa stack leak).pub s₁ s₂ ∧ ∀ f ∈ x :: xs, s₁.syms f = s₂.syms f) c)
    (hsat : ∃ s, (sig.contract abi pre post wa stack leak).pre s) :
    Verified X86_64.target c (sig.contract (abi.withFns (x :: xs)) pre post wa stack leak) := by
  refine ⟨hok, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => hct s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ ?_ e₁ e₂, hsat⟩
  revert hp
  simp only [Sig.contract, Abi.withFns]
  split
  · exact False.elim
  · cases leak with
    | none => exact fun ⟨⟨a, fa⟩, b, c⟩ => ⟨⟨a, b, c⟩, fa⟩
    | some f => exact fun ⟨⟨⟨a, fa⟩, l⟩, b, c⟩ => ⟨⟨⟨a, l⟩, b, c⟩, fa⟩

/-- `Abi.withFns` changes only what is public, so not what the cleanup needs
of the postcondition. -/
theorem PostOut.withFns {rb : Nat} (h : PostOut (sig.contract abi pre post wa stack leak) rb) :
    PostOut (sig.contract (abi.withFns (x :: xs)) pre post wa stack leak) rb := h

/-- Code whose frames and calls use at most the `stack` bytes its contract
reserves, with vector instructions of at most the level `v`, which calls
indirectly only the functions its contract makes public (`Abi.withFns`),
with its cleanup (`scrubAll`) meets its contract in constant time and
returns without secret residue, if its postcondition reads the memory on
return only within the buffers. -/
theorem verifiedScrubbedAllFns {c : Prog isa} (v : VecLevel) {rb : Nat}
    (h : Verified target c (sig.contract (abi.withFns (x :: xs)) pre post wa stack leak))
    (hpost : PostOut (sig.contract (abi.withFns (x :: xs)) pre post wa stack leak) rb)
    (hsp : c.all (fun i => !isa.writesSp i) = true) (hd : c.x86_64Depth ≤ stack)
    (hlv : c.allInstrs (fun i => decide (i.vecLevelR ≤ v.level)) = true) (hmx : MxSame c)
    (hin : ∀ n ∈ UpperLock.inames c, n ∈ x :: xs)
    (hb : sig.retBits 64 = rb := by rfl) (hl : litSide stack rb = true := by decide) :
    VerifiedScrubbed target (scrubAll v rb stack c) (sig.contract (abi.withFns (x :: xs)) pre post wa stack leak)
      rb := by
  subst hb
  have hl' := hl
  simp only [litSide, Bool.and_eq_true, beq_iff_eq] at hl'
  simp only [litSide, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hl
  obtain ⟨⟨⟨hst, hcs⟩, hcv⟩, hrb⟩ := hl
  have hcv' : ∀ b ∈ chunksA stack, 0 < b ∧ b < 4096 ∧ b % 8 = 0 :=
    fun b hb => of_decide_eq_true (List.all_eq_true.mp hcv b hb)
  have hlv' : ∀ i ∈ instrs c, i.vecLevelR ≤ v.level := fun i hi => by
    simpa using List.all_eq_true.mp ((Code.allInstrs_eq _ c).symm.trans hlv) i hi
  let ks := wipeKs (chunksA stack)
  have hres : ResOk c (sig.contract (abi.withFns (x :: xs)) pre post wa stack leak) stack ks (chunksA stack) := by
    show ResOk c _ stack (wipeKs (chunksA stack)) (chunksA stack)
    rw [wipeKs_eq]
    exact RScrub.resOk_allC _ _ (fun b hb => (of_decide_eq_true (List.all_eq_true.mp hl'.1.2 b hb)).2.2)
      hl'.1.1.2
  have ht : TailOk (sig.retBits 64) xregs (psOf ks) (gsAll ks) ks :=
    { x0 := fun _ => mem_xregs _
      r11 := fun hk => by simp [psOf, hk]
      psOk := fun q hq => by unfold psOf at hq; split at hq <;> simp_all [scratchRegs]
      gsOk := fun q hq => by
        unfold gsAll at hq; split at hq
        · exact hq
        · exact List.mem_of_mem_erase hq
      gne := by unfold gsAll; split <;> simp [scratchRegs] }
  have hgk : ∀ q ∈ scratchRegs, q ∉ gsAll ks → q ∉ psOf ks → ∀ i ∈ instrs c,
      Taint.clobbers i q = false := fun q hq hg hp =>
    ((gsAll_cover ks q hq).elim (fun h => absurd h hg) (fun h => absurd h hp))
  have key := Verified.scrubM (f := .avx) (scrubAbi_fns x xs) h (SpSafe.of_all hsp) hd
    hcs hst hcv' hlv' (fun _ => hmx) hrb hpost hres ht (.inl mem_xregs)
    (fun _ => mem_xregs) (fun _ _ e => absurd e (by decide)) hgk
  exact ⟨key.1, key.2 fun s₁ s₂ hp n hn => fns_pub hp n (hin n hn), fun ty _ h => by cases ty <;> cases h⟩

end

/-! ## The candidates of indirect calls -/

/-- `c` with the code of each indirect call's candidate `f` that `σ` maps to
a name and code replaced by that name and code. -/
def fillI (σ : String → Option (String × Prog isa)) : Prog isa → Prog isa
  | .block is => .block is
  | .seq a b => .seq (fillI σ a) (fillI σ b)
  | .ite c t e => .ite c (fillI σ t) (fillI σ e)
  | .loop b c => .loop (fillI σ b) c
  | .call f b => .call f (fillI σ b)
  | .frame i b j => .frame i (fillI σ b) j
  | .icall i f b x => match σ f with
    | some (g, d) => .icall i g d (fillI σ x)
    | none => .icall i f (fillI σ b) (fillI σ x)

/-- What each instruction of `c` and of the code `σ` gives meets, `fillI σ c`'s does. -/
theorem fillI_allInstrs {p : Instr → Bool} {σ : String → Option (String × Prog isa)}
    (hσ : ∀ f g d, σ f = some (g, d) → d.allInstrs p = true) :
    ∀ c : Prog isa, c.allInstrs p = true → (fillI σ c).allInstrs p = true
  | .block _, h => h
  | .seq a b, h => by
    simp only [Code.allInstrs, Bool.and_eq_true] at h
    simp only [fillI, Code.allInstrs, Bool.and_eq_true]
    exact ⟨fillI_allInstrs hσ a h.1, fillI_allInstrs hσ b h.2⟩
  | .ite _ t e, h => by
    simp only [Code.allInstrs, Bool.and_eq_true] at h
    simp only [fillI, Code.allInstrs, Bool.and_eq_true]
    exact ⟨fillI_allInstrs hσ t h.1, fillI_allInstrs hσ e h.2⟩
  | .loop b _, h => fillI_allInstrs hσ b h
  | .call _ b, h => fillI_allInstrs hσ b h
  | .frame _ b _, h => by
    simp only [Code.allInstrs, Bool.and_eq_true] at h
    simp only [fillI, Code.allInstrs, Bool.and_eq_true]
    exact ⟨⟨h.1.1, fillI_allInstrs hσ b h.1.2⟩, h.2⟩
  | .icall _ f b x, h => by
    simp only [Code.allInstrs, Bool.and_eq_true] at h
    simp only [fillI]
    split
    · rename_i g d hf
      simp only [Code.allInstrs, Bool.and_eq_true]
      exact ⟨⟨h.1.1, hσ f g d hf⟩, fillI_allInstrs hσ x h.2⟩
    · simp only [Code.allInstrs, Bool.and_eq_true]
      exact ⟨⟨h.1.1, fillI_allInstrs hσ b h.1.2⟩, fillI_allInstrs hσ x h.2⟩

/-- `fillI σ c` calls indirectly only functions of `fs`, if `c` calls
indirectly only those and those `σ` replaces, by functions of `fs` that call
none indirectly. -/
theorem fillI_inames {σ : String → Option (String × Prog isa)} {fs : List String}
    (hσ : ∀ f g d, σ f = some (g, d) → g ∈ fs ∧ UpperLock.inames d = []) :
    ∀ c : Prog isa, (∀ n ∈ UpperLock.inames c, n ∈ fs ∨ (σ n).isSome) →
      ∀ n ∈ UpperLock.inames (fillI σ c), n ∈ fs
  | .block _, _ => by simp [fillI, UpperLock.inames]
  | .seq a b, h | .ite _ a b, h => by
    simp only [UpperLock.inames, List.mem_append] at h
    simp only [fillI, UpperLock.inames, List.mem_append]
    intro n hn
    rcases hn with hn | hn
    · exact fillI_inames hσ a (fun m hm => h m (.inl hm)) n hn
    · exact fillI_inames hσ b (fun m hm => h m (.inr hm)) n hn
  | .loop b _, h | .call _ b, h | .frame _ b _, h => fillI_inames hσ b h
  | .icall _ f b x, h => by
    simp only [UpperLock.inames, List.mem_cons, List.mem_append] at h
    simp only [fillI]
    split
    · rename_i g d hf
      simp only [UpperLock.inames, (hσ f g d hf).2, List.mem_cons, List.mem_append, List.not_mem_nil,
        or_false]
      intro n hn
      rcases hn with hn | hn
      · rw [hn]; exact (hσ f g d hf).1
      · exact fillI_inames hσ x (fun m hm => h m (.inr hm)) n hn
    · rename_i hf
      simp only [UpperLock.inames, List.mem_cons, List.mem_append]
      intro n hn
      rcases hn with (rfl | hn) | hn
      · rcases h n (.inl (.inl rfl)) with h' | h'
        · exact h'
        · simp [hf] at h'
      · exact fillI_inames hσ b (fun m hm => h m (.inl (.inr hm))) n hn
      · exact fillI_inames hσ x (fun m hm => h m (.inr hm)) n hn

end VG.X86_64.Scrub
