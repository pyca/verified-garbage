module

public import VerifiedGarbage.Impl.Scrub.X86_64.FnUp
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubFillG
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubUp
public import VerifiedGarbage.Proof.Framework.X86_64.UpperLock
public import VerifiedGarbage.Proof.Framework.X86_64.UpCallee
import VerifiedGarbage.Proof.Framework.X86_64.ScrubCall
import VerifiedGarbage.Proof.Framework.X86_64.ScrubChunks
import VerifiedGarbage.Proof.Framework.Lit

/-!
# The cleanup at the level `sse` of code over AVX functions it calls through tables (x86-64)

`verifiedScrubbedAllUp` states `VerifiedScrubbed` of `scrubAllUp rb n c`
(`Impl/Scrub/X86_64/FnUp.lean`): `X86_64.Scrub.Verified.scrubU` at the level
`sse`, for code whose instructions are below the level `evex`
(`Instr.vecLevel ≤ 1`) and whose vectors' upper halves agree at the end if
they did at the start (`UpperLock.up`), which calls indirectly only its
tables' functions (as `ScrubUp.lean`'s `scrubRegUp`, with every granule of
its stack wiped).

For code generic over an implementation it calls (`fillCallsG σ a`, its code
over a stub `a`), what this needs of the code follows from what the stub
meets and what each implementation's code meets (`upCallee`): `fillCallsG_*`.
-/

@[expose] public section

namespace VG.X86_64.Scrub

open VG.X86_64 VG.Impl.Scrub.X86_64

/-- `r`'s code followed by `scrubAllUp rb n`, which clears the SSE registers
and wipes every granule of its `n` bytes of stack, meets `r`'s contract in
constant time and returns without secret residue: for code below the level
`evex` (`hl1`) whose vectors' upper halves agree at the end if they did at
the start (`hup`), which calls indirectly only its tables' functions
(`hic`), whose postcondition reads the memory on return only within its
buffers (`hpost`). -/
theorem verifiedScrubbedAllUp {api : Api} (r : Unscrubbed api target) {n rb : Nat}
    (hpost : PostOut r.contract (retBitsOf r))
    (hd : r.code.x86_64Depth ≤ r.stack)
    (hl1 : r.code.allInstrs (fun i => decide (i.vecLevel ≤ 1)) = true)
    (hup : UpperLock.up r.code true = true) (hic : tablesCall r.code r.tables = true)
    (hl : litSide r.stack (retBitsOf r) = true := by decide)
    (hn : r.stack = n := by rfl) (hb : retBitsOf r = rb := by rfl) :
    VerifiedScrubbed target (scrubAllUp rb n r.code) r.contract rb := by
  subst hn hb
  simp only [litSide, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hl
  obtain ⟨⟨⟨hst, hcs⟩, hcv⟩, hrb⟩ := hl
  have hcv' : ∀ b ∈ chunksA r.stack, 0 < b ∧ b < 4096 ∧ b % 8 = 0 :=
    fun b hb => of_decide_eq_true (List.all_eq_true.mp hcv b hb)
  have hl1' : ∀ i ∈ instrs r.code, i.vecLevel ≤ 1 := fun i hi => by
    simpa using List.all_eq_true.mp ((Code.allInstrs_eq _ r.code).symm.trans hl1) i hi
  have hres : ResOk r.code r.contract r.stack (wipeKs (chunksA r.stack)) (chunksA r.stack) := by
    rw [wipeKs_eq]; exact RScrub.resOk_allC _ _ (fun b hb => (hcv' b hb).2.2) hcs
  have ht : TailOk (retBitsOf r) xregs (psOf (wipeKs (chunksA r.stack))) (gsAll (wipeKs (chunksA r.stack)))
      (wipeKs (chunksA r.stack)) :=
    { x0 := fun _ => mem_xregs _
      r11 := fun hk => by simp [psOf, hk]
      psOk := fun q hq => by unfold psOf at hq; split at hq <;> simp_all [scratchRegs]
      gsOk := fun q hq => by
        unfold gsAll at hq; split at hq
        · exact hq
        · exact List.mem_of_mem_erase hq
      gne := by unfold gsAll; split <;> simp [scratchRegs] }
  have hgk : ∀ q ∈ scratchRegs, q ∉ gsAll (wipeKs (chunksA r.stack)) → q ∉ psOf (wipeKs (chunksA r.stack)) →
      ∀ i ∈ instrs r.code, Taint.clobbers i q = false := fun q hq hg hp =>
    ((gsAll_cover _ q hq).elim (fun h => absurd h hg) (fun h => absurd h hp))
  have hrb' : retBitsOf r ≤ 32 ∨ retBitsOf r = 64 := hrb
  have hnames : ∀ f ∈ UpperLock.inames r.code, f ∈ tableFns r.tables := by
    intro f hf
    unfold tablesCall at hic
    exact of_decide_eq_true (List.all_eq_true.mp hic f hf)
  obtain ⟨pre, post, leak, e⟩ := r.ofSig
  have hv := r.verified
  have hp := hpost
  have hr := hres
  unfold retBitsOf at hrb' hp ht ⊢
  rw [e] at hv hp hr ⊢
  have key := Verified.scrubU (ScrubAbi.of r.consts api.sig r.tables) hv (SpSafe.of_all r.spSafe) hd
    hcs hst hcv' (fun _ => hl1')
    (upperOk_lock hv.2.1 (fun s₁ s₂ h f hf => tables_pub_syms h f (hnames f hf)) hup)
    hrb' hp hr ht (.inl mem_xregs) (fun e => absurd e (by decide)) (fun _ _ e => absurd e (by decide))
    hgk (fun s₁ s₂ h f hf => tables_pub_syms (contract_pub h) f (hnames f hf))
  exact ⟨key.1, key.2⟩

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
    (ha : decide (depthG n a ≤ m) && a.allInstrs (fun i => decide (i.vecLevel ≤ 1)) && UpperLock.up a true &&
      (UpperLock.inames a).isEmpty = true) :
    upCallee (fillCallsG σ a) m = true := by
  have hσ' : ∀ f g d, σ f = some (g, d) → (Code.call g d : Prog isa).x86_64Depth ≤ n f ∧
      d.allInstrs (fun i => decide (i.vecLevel ≤ 1)) = true ∧ UpperLock.up d true = true ∧
      UpperLock.inames d = [] := by
    intro f g d h
    have := hσ f g d h
    simp only [upCallee, Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at this
    exact ⟨this.1.1.1, this.1.1.2, this.1.2, by simpa [UpperLock.inames] using this.2⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at ha
  simp only [upCallee, Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff]
  exact ⟨⟨⟨Nat.le_trans (fillCallsG_depth (fun f g d h => (hσ' f g d h).1) a) ha.1.1.1,
      fillCallsG_allInstrs _ (fun f g d h => (hσ' f g d h).2.1) a ha.1.1.2⟩,
    fillCallsG_up (fun f g d h => (hσ' f g d h).2.2.1) a true ha.1.2⟩,
    by rw [fillCallsG_inames (fun f g d h => (hσ' f g d h).2.2.2)]; exact ha.2⟩

/-- `upCallee` of a call, from that of its code with 8 bytes more. -/
theorem upCallee_call {d : Prog isa} {m : Nat} (g : String) (h : upCallee d m = true) :
    upCallee (.call g d) (m + 8) = true := by
  simp only [upCallee, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  exact ⟨⟨⟨by simp only [Code.x86_64Depth]; omega, by simpa only [Code.allInstrs] using h.1.1.2⟩,
    by simpa only [UpperLock.up] using h.1.2⟩, by simpa only [UpperLock.inames] using h.2⟩

end

/-- What `verifiedScrubbedOrUp` needs of a function's code over a stub `a`,
at the level `sse`: its stack, instructions below the level `evex`, upper
halves that agree at its end if they did at its start, and indirect calls
only of its tables' functions. -/
noncomputable def upStub (a : Prog isa) (n : String → Nat) (stack : Nat) (ts : List (String × List FnTable)) : Bool :=
  decide (depthG n a ≤ stack) && a.allInstrs (fun i => decide (i.vecLevel ≤ 1)) && upK a true && tablesCall a ts

/-- `r`'s code, `fillCallsG σ a` (its code over a stub `a` with the
implementations' code), followed by `scrubAllOrUp v rb stack`, meets `r`'s
contract in constant time and returns without secret residue: at the level
`sse` from `upStub` of the stub and `upCallee` of what fills its holes (for
code that runs AVX functions through its tables), at a higher level `v` from
`stubSideG` of the stub at the level `avx` and `calleeSide` of what fills
its holes at `v`. -/
theorem verifiedScrubbedOrUp {api : Api} (r : Unscrubbed api target) (v : VecLevel) {a : Prog isa}
    {σ : String → Option (String × Prog isa)} {n : String → Nat} {stack rb : Nat} (ts : List (String × List FnTable))
    (hpost : PostOut r.contract (retBitsOf r)) (he : r.code = fillCallsG σ a)
    (hσu : v = .sse → ∀ f g d, σ f = some (g, d) → upCallee (.call g d) (n f) = true)
    (hσc : v ≠ .sse → ∀ f g d, σ f = some (g, d) → calleeSide (.call g d) v.level (n f) = true)
    (hn : r.stack = stack := by rfl) (hb : retBitsOf r = rb := by rfl) (htb : r.tables = ts := by rfl)
    (hau : upStub a n stack ts = true := by rw [upStub]; lit_decide)
    (hac : stubSideG a VecLevel.avx.level n stack ts = true := by lit_decide)
    (hl : litSide stack rb = true := by decide) :
    VerifiedScrubbed target (scrubAllOrUp v rb stack r.code) r.contract rb := by
  cases v with
  | sse =>
    have hσ := hσu rfl
    have hσ' : ∀ f g d, σ f = some (g, d) → (Code.call g d : Prog isa).x86_64Depth ≤ n f ∧
        d.allInstrs (fun i => decide (i.vecLevel ≤ 1)) = true ∧ UpperLock.up d true = true ∧
        UpperLock.inames d = [] := by
      intro f g d h
      have := hσ f g d h
      simp only [upCallee, Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at this
      exact ⟨this.1.1.1, this.1.1.2, this.1.2, by simpa [UpperLock.inames] using this.2⟩
    simp only [upStub, Bool.and_eq_true, decide_eq_true_eq, upK_eq] at hau
    obtain ⟨⟨⟨hd, hl1⟩, hup⟩, hic⟩ := hau
    subst hn hb htb
    exact verifiedScrubbedAllUp r hpost
      (he ▸ Nat.le_trans (fillCallsG_depth (fun f g d h => (hσ' f g d h).1) a) hd)
      (he ▸ fillCallsG_allInstrs _ (fun f g d h => (hσ' f g d h).2.1) a hl1)
      (he ▸ fillCallsG_up (fun f g d h => (hσ' f g d h).2.2.1) a true hup)
      (by rw [he, tablesCall, fillCallsG_inames (fun f g d h => (hσ' f g d h).2.2.2)]; exact hic) hl
  | avx =>
    exact verifiedScrubbedAllFillG r .avx hpost (he ▸ fillG_of (hσc (by decide)) a) (Nat.le_refl _)
      (Nat.le_refl _) ts hn hb htb hac hl
  | evex =>
    exact verifiedScrubbedAllFillG r .evex hpost (he ▸ fillG_of (hσc (by decide)) a) (by decide)
      (Nat.le_refl _) ts hn hb htb hac hl

/-- `scrubAllOrUp`'s code writes the stack pointer only as `c` does. -/
theorem scrubAllOrUp_spSafe {c : Prog isa} (v : VecLevel) (rb n : Nat) (h : c.all (fun i => !isa.writesSp i) = true) :
    (scrubAllOrUp v rb n c).all (fun i => !isa.writesSp i) = true := by
  cases v <;> exact scrubKs_spSafe h

end VG.X86_64.Scrub
