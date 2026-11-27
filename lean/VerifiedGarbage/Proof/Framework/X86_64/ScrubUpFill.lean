module

public import VerifiedGarbage.Proof.Framework.X86_64.ScrubFillG
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubUp
public import VerifiedGarbage.Proof.Framework.X86_64.UpperLock
public import VerifiedGarbage.Proof.Framework.X86_64.TableFill
import VerifiedGarbage.Proof.Framework.X86_64.ScrubCall
import VerifiedGarbage.Proof.Framework.X86_64.ScrubChunks
import VerifiedGarbage.Proof.Framework.Lit

/-!
# The cleanup of code generic over an implementation it calls, at any level (x86-64)

`X86_64.Scrub.verifiedScrubbedAllUp` (`ScrubUpFn.lean`) states
`VerifiedScrubbed` of `scrubAll .sse rb n c` for code below the level `evex`
whose vectors' upper halves agree at the end if they did at the start, which
calls indirectly only its tables' functions (AVX hash functions that end with
`vzeroupper`). For code generic over an implementation it calls
(`fillCallsG σ a`, its code over a stub `a`), what this needs of the code
follows from what the stub meets and what each implementation's code meets
(`upCallee`, `TableFill.lean`): `fillCallsG_*`. `verifiedScrubbedOrUpFill` takes
that route at the level `sse`, and `verifiedScrubbedAllFillG`'s above it.
-/

@[expose] public section

namespace VG.X86_64.Scrub

open VG.X86_64 VG.Impl.Scrub.X86_64

section
variable {σ : String → Option (String × Prog isa)}

/-- The stack `fillCallsG σ a` uses is at most `depthG n a`, if each call `σ`
gives uses at most `n f`. -/
theorem fillCallsG_depth {n : String → Nat}
    (hσ : ∀ f g d, σ f = some (g, d) → (Code.call g d : Prog isa).x86_64Depth ≤ n f) :
    ∀ a : Prog isa, (fillCallsG σ a).x86_64Depth ≤ depthG n a
  | .block is => by simp [fillCallsG, Code.x86_64Depth, depthG]
  | .seq a b => by
    have := fillCallsG_depth hσ a; have := fillCallsG_depth hσ b
    simp only [fillCallsG, Code.x86_64Depth, depthG]; omega
  | .ite c t e => by
    have := fillCallsG_depth hσ t; have := fillCallsG_depth hσ e
    simp only [fillCallsG, Code.x86_64Depth, depthG]; omega
  | .loop b c => by
    have := fillCallsG_depth hσ b; simp only [fillCallsG, Code.x86_64Depth, depthG]; omega
  | .frame i b j => by
    have := fillCallsG_depth hσ b; simp only [fillCallsG, Code.x86_64Depth, depthG]; omega
  | .icall i f b x => by
    have := fillCallsG_depth hσ b; have := fillCallsG_depth hσ x
    simp only [fillCallsG, Code.x86_64Depth, depthG]; omega
  | .call f b => by
    cases b with
    | block is =>
      cases is with
      | nil =>
        simp only [fillCallsG]
        cases h : σ f with
        | none => simp only [Code.x86_64Depth, depthG]; omega
        | some p =>
          obtain ⟨g, d⟩ := p
          have := hσ f g d h
          simp only [depthG]; omega
      | cons i is => simp [fillCallsG, Code.x86_64Depth, depthG]
    | _ => exact Nat.add_le_add_right (fillCallsG_depth hσ _) 8

/-- A property of every instruction of `a` holds of every one of
`fillCallsG σ a`, if it holds of every one of the code `σ` gives. -/
theorem fillCallsG_allInstrs (p : Instr → Bool) (hσ : ∀ f g d, σ f = some (g, d) → d.allInstrs p = true)
    (a : Prog isa) : a.allInstrs p = true → (fillCallsG σ a).allInstrs p = true := by
  induction a with
  | block is => exact id
  | seq a b iha ihb =>
    intro h; simp only [Code.allInstrs, Bool.and_eq_true] at h
    simp only [fillCallsG, Code.allInstrs, iha h.1, ihb h.2, Bool.and_self]
  | ite c t e iht ihe =>
    intro h; simp only [Code.allInstrs, Bool.and_eq_true] at h
    simp only [fillCallsG, Code.allInstrs, iht h.1, ihe h.2, Bool.and_self]
  | loop b c ih => exact ih
  | frame i b j ih =>
    intro h; simp only [Code.allInstrs, Bool.and_eq_true] at h
    simp only [fillCallsG, Code.allInstrs, ih h.1.2, h.1.1, h.2, Bool.and_self]
  | icall i f b x ihb ihx =>
    intro h; simp only [Code.allInstrs, Bool.and_eq_true] at h
    simp only [fillCallsG, Code.allInstrs, ihb h.1.2, ihx h.2, h.1.1, Bool.and_self]
  | call f b ih =>
    intro h
    cases b with
    | block is =>
      cases is with
      | nil =>
        simp only [fillCallsG]
        cases e : σ f with
        | none => rfl
        | some q => obtain ⟨g, d⟩ := q; exact hσ f g d e
      | cons i is => exact h
    | _ => exact ih h

/-- `fillCallsG σ a` calls indirectly only what `a` does, if the code `σ`
gives calls nothing indirectly. -/
theorem fillCallsG_inames (hσ : ∀ f g d, σ f = some (g, d) → UpperLock.inames d = []) (a : Prog isa) :
    UpperLock.inames (fillCallsG σ a) = UpperLock.inames a := by
  induction a with
  | block _ => rfl
  | seq a b iha ihb => simp only [fillCallsG, UpperLock.inames, iha, ihb]
  | ite c t e iht ihe => simp only [fillCallsG, UpperLock.inames, iht, ihe]
  | loop b c ih => exact ih
  | frame i b j ih => exact ih
  | icall i f b x ihb ihx => simp only [fillCallsG, UpperLock.inames, ihb, ihx]
  | call f b ih =>
    cases b with
    | block is =>
      cases is with
      | nil =>
        simp only [fillCallsG]
        cases e : σ f with
        | none => rfl
        | some q => obtain ⟨g, d⟩ := q; simpa [UpperLock.inames] using hσ f g d e
      | cons i is => rfl
    | _ => exact ih

/-- The vectors' upper halves agree after `fillCallsG σ a` where they do
after `a`, if they agree after the code `σ` gives whenever they did before it. -/
theorem fillCallsG_up (hσ : ∀ f g d, σ f = some (g, d) → UpperLock.up d true = true) (a : Prog isa) :
    ∀ x : Bool, UpperLock.up a x = true → UpperLock.up (fillCallsG σ a) x = true := by
  induction a with
  | block is => exact fun _ h => h
  | seq a b iha ihb =>
    intro x h
    simp only [UpperLock.up] at h ⊢
    exact UpperLock.up_mono (fillCallsG σ b) (iha x) (ihb (UpperLock.up a x) h)
  | ite c t e iht ihe =>
    intro x h
    simp only [UpperLock.up, Bool.and_eq_true] at h
    simp only [fillCallsG, UpperLock.up, Bool.and_eq_true]
    exact ⟨iht x h.1, ihe x h.2⟩
  | loop b c ih => exact ih
  | frame i b j ih => exact ih
  | icall i f b y ihb ihy =>
    intro x h
    simp only [UpperLock.up, Bool.and_eq_true] at h
    simp only [fillCallsG, UpperLock.up, Bool.and_eq_true]
    exact ⟨ihb x h.1, ihy x h.2⟩
  | call f b ih =>
    intro x h
    cases b with
    | block is =>
      cases is with
      | nil =>
        simp only [fillCallsG]
        cases e : σ f with
        | none => exact h
        | some q =>
          obtain ⟨g, d⟩ := q
          have hx : x = true := h
          subst hx
          exact hσ f g d e
      | cons i is => exact h
    | _ => exact ih x h

/-- What the cleanup at the level `sse` needs of `fillCallsG σ a`, from
what it needs of the stub `a` (evaluated once) and of the code `σ` gives. -/
theorem upCallee_fillCallsG {n : String → Nat} {m : Nat}
    (hσ : ∀ f g d, σ f = some (g, d) → upCallee (.call g d) (n f) = true) (a : Prog isa)
    (ha : decide (depthG n a ≤ m) && lvAll 1 a && upF a true &&
      (UpperLock.inames a).isEmpty = true) :
    upCallee (fillCallsG σ a) m = true := by
  have hσ' : ∀ f g d, σ f = some (g, d) → (Code.call g d : Prog isa).x86_64Depth ≤ n f ∧
      d.allInstrs (fun i => decide (i.vecLevel ≤ 1)) = true ∧ UpperLock.up d true = true ∧
      UpperLock.inames d = [] := by
    intro f g d h
    have := hσ f g d h
    simp only [upCallee, lvAll_one, upF_eq, Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at this
    exact ⟨this.1.1.1, this.1.1.2, this.1.2, by simpa [UpperLock.inames] using this.2⟩
  simp only [lvAll_one, upF_eq, Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at ha
  simp only [upCallee, lvAll_one, upF_eq, Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff]
  exact ⟨⟨⟨Nat.le_trans (fillCallsG_depth (fun f g d h => (hσ' f g d h).1) a) ha.1.1.1,
      fillCallsG_allInstrs _ (fun f g d h => (hσ' f g d h).2.1) a ha.1.1.2⟩,
    fillCallsG_up (fun f g d h => (hσ' f g d h).2.2.1) a true ha.1.2⟩,
    by rw [fillCallsG_inames (fun f g d h => (hσ' f g d h).2.2.2)]; exact ha.2⟩

/-- `upCallee` of a call, from that of its code with 8 bytes more. -/
theorem upCallee_call {d : Prog isa} {m : Nat} (g : String) (h : upCallee d m = true) :
    upCallee (.call g d) (m + 8) = true := by
  simp only [upCallee, lvAll_one, upF_eq, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  exact ⟨⟨⟨by simp only [Code.x86_64Depth]; omega, by simpa only [Code.allInstrs] using h.1.1.2⟩,
    by simpa only [UpperLock.up] using h.1.2⟩, by simpa only [UpperLock.inames] using h.2⟩

end

/-- What fills a call calls nothing indirectly. -/
theorem sigma_inames {v : VecLevel} {n : String → Nat} {σ : String → Option (String × Prog isa)}
    (hu : v = .sse → ∀ f g d, σ f = some (g, d) → upCallee (.call g d) (n f) = true)
    (hs : v ≠ .sse → ∀ f g d, σ f = some (g, d) → calleeSide (.call g d) v.level (n f) = true)
    (f g : String) (d : Prog isa) (h : σ f = some (g, d)) : UpperLock.inames d = [] := by
  by_cases hv : v = .sse
  · have := hu hv f g d h
    simp only [upCallee, Bool.and_eq_true, List.isEmpty_iff] at this
    simpa only [UpperLock.inames] using this.2
  · have := hs hv f g d h
    simp only [calleeSide_eq, Bool.and_eq_true, List.isEmpty_iff] at this
    simpa only [UpperLock.inames] using this.2

/-- What `verifiedScrubbedOrUpFill` needs of a function's code over a stub
`a`, with stubs in the place of its tables' implementations (`tableStub`), at
the level `sse`: its stack, instructions below the level `evex`, and upper
halves that agree at its end if they did at its start. -/
noncomputable def upStubT (a : Prog isa) (n : String → Nat) (stack : Nat) : Bool :=
  Nat.ble (depthGK n a) stack && lvAll 1 a && upF a true

/-- `r`'s code, generic over the implementations it calls (`fillCallsG`) and
over those of the tables it takes (`TFill`, `TableFill.lean`), followed by
`scrubAll v rb stack`, meets `r`'s contract in constant time and returns
without secret residue: at the level `sse` from `upStubT` of its code with
stubs in the place of both, `upCallee` of what fills its calls and of the
tables' implementations (in `hf`; for code that runs AVX functions through
its tables), and at a higher level `v` from the same, which is more than
`calleeSide` at `v`, but `calleeSide` of what fills its calls. The kernel
evaluates the code of each of the tables' implementations once, and not at
each call of each table. -/
theorem verifiedScrubbedOrUpFill {api : Api} (r : Unscrubbed api target) (v : VecLevel) {a : Prog isa}
    {σ : String → Option (String × Prog isa)} {n : String → Nat} {m : Nat} {N : List String} {stack rb : Nat}
    (hpost : PostOut r.contract (retBitsOf r)) (hf : TFill m N (fillCallsG σ a) r.code)
    (hN : ∀ f ∈ N, f ∈ tableFns r.tables)
    (hσu : v = .sse → ∀ f g d, σ f = some (g, d) → upCallee (.call g d) (n f) = true)
    (hσc : v ≠ .sse → ∀ f g d, σ f = some (g, d) → calleeSide (.call g d) v.level (n f) = true)
    (hn : r.stack = stack := by rfl) (hb : retBitsOf r = rb := by rfl)
    (ha : upStubT a n stack = true := by rw [upStubT]; lit_decide)
    (hl : litSide stack rb = true := by decide) :
    VerifiedScrubbed target (scrubAll v rb stack r.code) r.contract rb := by
  simp only [upStubT, Bool.and_eq_true, ble_depthGK, decide_eq_true_eq] at ha
  obtain ⟨⟨hd, hl1⟩, hup⟩ := ha
  have hic : tablesCall r.code r.tables = true := by
    unfold tablesCall
    exact List.all_eq_true.mpr fun f hf' => decide_eq_true (hN f (hf.inames f hf'))
  have side (hv : 1 ≤ v.level) (hσ : ∀ f g d, σ f = some (g, d) → calleeSide (.call g d) v.level (n f) = true) :
      VerifiedScrubbed target (scrubAll v rb stack r.code) r.contract rb := by
    have hg : FillG v.level n a (fillCallsG σ a) := fillG_of hσ a
    rw [lvAll_eq] at hl1
    obtain ⟨hlv, hmx⟩ := allInstrs_level (Nat.le_refl _) (hf.all (fun c h => by
      simp only [upCallee, Bool.and_eq_true, lvAll_eq] at h
      exact side_mono hv h.1.1.2) (hg.side (side_mono hv hl1)))
    subst hn hb
    exact verifiedScrubbedAllF r v hpost (Nat.le_trans hf.depth_le (Nat.le_trans hg.depth_le hd)) hlv
      (mxSame_of_noLoad hmx) hic hl rfl rfl
  cases v with
  | sse =>
    have hσ := hσu rfl
    have hσ' : ∀ f g d, σ f = some (g, d) → (Code.call g d : Prog isa).x86_64Depth ≤ n f ∧
        d.allInstrs (fun i => decide (i.vecLevel ≤ 1)) = true ∧ UpperLock.up d true = true := by
      intro f g d h
      have := hσ f g d h
      simp only [upCallee, lvAll_one, upF_eq, Bool.and_eq_true, decide_eq_true_eq] at this
      exact ⟨this.1.1.1, this.1.1.2, this.1.2⟩
    rw [lvAll_one] at hl1
    rw [upF_eq] at hup
    subst hn hb
    exact verifiedScrubbedAllUp r hpost
      (Nat.le_trans hf.depth_le (Nat.le_trans (fillCallsG_depth (fun f g d h => (hσ' f g d h).1) a) hd))
      (hf.all (fun c h => (TFill.upCallee_parts h).2.1)
        (fillCallsG_allInstrs _ (fun f g d h => (hσ' f g d h).2.1) a hl1))
      (hf.up true (fillCallsG_up (fun f g d h => (hσ' f g d h).2.2) a true hup)) hic hl
  | avx => exact side (Nat.le_refl _) (hσc (by decide))
  | evex => exact side (by decide) (hσc (by decide))

end VG.X86_64.Scrub
