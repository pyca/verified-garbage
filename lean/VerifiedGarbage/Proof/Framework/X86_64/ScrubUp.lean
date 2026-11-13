module

public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.UpperLock
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.X86_64.Call

/-!
# Returning without secret residue: the baseline ISA's callers of AVX code (x86-64)

`Verified.scrubU` is `Verified.scrub` with what it needs of the code's
vector instructions stated as two facts, rather than derived from their
level: below the level `evex`, the code's instructions are at most of level
1 (`hl1`), and the upper halves of the vector registers that the clearing
leaves agree at the end of two runs (`UpperOk`). For code of the baseline
ISA whose tables of functions may run functions with AVX instructions that
end with `vzeroupper`, `UpperLock.lock` gives `UpperOk` at the level `sse`
(`upperOk_lock`), so the clearing at that level, which needs no CPU
feature, leaves no residue (`scrubRegUp`, `withUp`). `withScrubAllUp` is
`withScrubAll`, with `withUp` where it would leave a registration
unscrubbed.

It is a module of its own, not part of `Scrub.lean`, so that the many
modules that import `Scrub.lean` are not rebuilt for it.
-/

@[expose] public section

open VG.Impl.Scrub.X86_64

namespace VG.X86_64.Scrub

open VG.X86_64 VG.X86_64.Residue

/-- The upper halves of the vector registers that the clearing at level `v`
leaves (all but those of `xs` above the level `sse`) agree after two runs of
`c` that may differ only in their buffers' secrets. -/
def UpperOk (v : VecLevel) (xs : List XReg) (c : Prog isa) (k : Contract isa) : Prop :=
  ∀ s₁ s₂ t₁ t₂ u₁ u₂, k.pre s₁ → k.pre s₂ → k.pub s₁ s₂ → Outside 0 s₁ s₂ →
    Exec isa c s₁ t₁ u₁ → Exec isa c s₂ t₂ u₂ →
    ∀ x, ¬ (v ≠ .sse ∧ x ∈ xs) → u₁.ymmHi x = u₂.ymmHi x ∧ u₁.zmmHi x = u₂.zmmHi x

section
variable {A : Abi isa} {sig : Sig} {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
  {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
  {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}

/-- Code verified against a contract that `Sig.contract` derives, whose
frames and calls use at most `stack` bytes, run by `scrub`, which clears
the granules `ks` of the `cs.sum = stack` bytes of stack below `rsp`:
verified against the same contract, and without secret residue, if the
postcondition reads the memory on return only within the buffers (`hpost`)
and the code leaves the same bytes in both runs in the rest of that stack
(`hres`, which `RTaint` derives from its analysis). -/
theorem Verified.scrubU {c : Prog isa} {v : VecLevel} {xs : List XReg} {ps gs : List Reg} {ks cs : List Nat}
    (hA : ScrubAbi A)
    (h : Verified target c (sig.contract A pre post wa stack leak))
    (hsp : SpSafe c) (hd : c.x86_64Depth ≤ stack) (hcs : cs.sum = stack) (hst : stack + 8 < 2 ^ 64)
    (hv : ∀ b ∈ cs, 0 < b ∧ b < 4096 ∧ b % 8 = 0)
    (hl1 : v ≠ .evex → ∀ i ∈ instrs c, i.vecLevel ≤ 1)
    (hup : UpperOk v xs c (sig.contract A pre post wa stack leak))
    (hrb : sig.retBits A.ptrBits ≤ 32 ∨ sig.retBits A.ptrBits = 64)
    (hpost : ∀ s u u', (sig.contract A pre post wa stack leak).pre s →
      (sig.contract A pre post wa stack leak).post s u →
      (∀ x, (∃ r ∈ s.rd ++ s.wr, r.Contains x 1) → u'.mem x = u.mem x) →
      (u'.gpr .rax).setWidth (sig.retBits A.ptrBits) = (u.gpr .rax).setWidth (sig.retBits A.ptrBits) →
      (sig.contract A pre post wa stack leak).post s u')
    (hres : ResOk c (sig.contract A pre post wa stack leak) stack ks cs)
    (ht : TailOk (sig.retBits A.ptrBits) xs ps gs ks)
    (hxs : (∀ x, x ∈ xs) ∨ ∀ i ∈ instrs c, writesVec i = false)
    (hxe : v = .evex → ∀ x, x ∈ xs) (hev : ∀ p : Addr, cs.sum ≤ p.toNat → EvexOk v ks cs p)
    (hgk : ∀ r ∈ scratchRegs, r ∉ gs → r ∉ ps → ∀ i ∈ instrs c, Taint.clobbers i r = false) :
    Verified target (Impl.Scrub.X86_64.scrub v (sig.retBits A.ptrBits) xs ps gs ks cs c)
        (sig.contract A pre post wa stack leak) ∧
      NoResidue (Impl.Scrub.X86_64.scrub v (sig.retBits A.ptrBits) xs ps gs ks cs c)
        (sig.contract A pre post wa stack leak) (sig.retBits A.ptrBits) := by
  have hnps : ∀ r, r ∉ scratchRegs → r ∉ ps := fun r h h' => h (ht.psOk r h')
  have hngs : ∀ r, r ∉ scratchRegs → r ∉ gs := fun r h h' => h (ht.gsOk r h')
  obtain ⟨hcor, hct, hsat⟩ := h
  -- What a run of `c`, then of the clearing, gives.
  have run : ∀ s t u, (sig.contract A pre post wa stack leak).pre s → Exec isa c s t u →
      abiPreserved s u ∧ (sig.contract A pre post wa stack leak).post s u ∧
      u.gpr .rsp = s.gpr .rsp ∧ cs.sum ≤ (u.gpr .rsp).toNat := by
    intro s t u hs he
    obtain ⟨t', u', he', ha, hp⟩ := hcor s hs
    obtain ⟨-, rfl⟩ := Exec.det he he'
    have hr : u.gpr .rsp = s.gpr .rsp := ha.1 .rsp (by decide)
    refine ⟨ha, hp, hr, ?_⟩
    rcases (contract_pre_scrub hA hs).1 with h0 | h0
    · rw [hcs, h0]; exact Nat.zero_le _
    · rw [hcs, hr]; exact h0
  -- The clearing's run.
  have tail : ∀ s t u s' t', (sig.contract A pre post wa stack leak).pre s → Exec isa c s t u →
      Exec isa (Impl.Scrub.X86_64.scrubTail v (sig.retBits A.ptrBits) xs ps gs ks cs) u t' s' →
      ∃ m', t' = tailTr v ks cs (s.gpr .rsp) ∧ s' = finState v (sig.retBits A.ptrBits) xs ps gs m' u ∧
        (∀ x, ¬ (⟨s.gpr .rsp - BitVec.ofNat 64 stack, stack⟩ : Region).Contains x 1 → m' x = u.mem x) ∧
        (∀ x, WCov ks cs (s.gpr .rsp) x → m' x = 0) ∧ (∀ x, ¬ WCov ks cs (s.gpr .rsp) x → m' x = u.mem x) := by
    intro s t u s' t' hs he het
    obtain ⟨-, -, hr, hl⟩ := run s t u hs he
    obtain ⟨m', e, hz, hu⟩ := tail_run v (sig.retBits A.ptrBits) cs ht u hv hl (hev _ hl)
    obtain ⟨rfl, rfl⟩ := Exec.det het e
    rw [hr] at hz hu
    have ho : ∀ x, ¬ (⟨s.gpr .rsp - BitVec.ofNat 64 stack, stack⟩ : Region).Contains x 1 → m' x = u.mem x :=
      fun x h => hu x fun hw => h (hcs ▸ hw.1)
    exact ⟨m', by rw [hr], rfl, ho, hz, hu⟩
  -- Buffers are not in the stack the clearing wipes.
  have outB : ∀ s, (sig.contract A pre post wa stack leak).pre s → ∀ x,
      (∃ r ∈ s.rd ++ s.wr, r.Contains x 1) →
        ¬ (⟨s.gpr .rsp - BitVec.ofNat 64 stack, stack⟩ : Region).Contains x 1 := by
    intro s hs x ⟨r, hr, hx⟩ hb
    by_cases h0 : stack = 0
    · subst h0; simp [Region.Contains] at hb
    · exact ((contract_pre_scrub hA hs).2 r hr).2 h0 x hb hx
  refine ⟨⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩,
    fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp ho hun e₁ e₂ => ?_⟩
  · -- Correctness.
    obtain ⟨t, u, he, -⟩ := hcor s hs
    obtain ⟨ha, hq, hr, hl⟩ := run s t u hs he
    obtain ⟨m', et, hz, hu⟩ := tail_run v (sig.retBits A.ptrBits) cs ht u hv hl (hev _ hl)
    rw [hr] at hz hu
    have hmo : ∀ x, ¬ (⟨s.gpr .rsp - BitVec.ofNat 64 stack, stack⟩ : Region).Contains x 1 → m' x = u.mem x :=
      fun x h => hu x fun hw => h (hcs ▸ hw.1)
    refine ⟨_, _, .seq he et, ⟨fun r hr' => ?_, ?_, ?_⟩, ?_⟩
    · have h1 : r ∉ scratchRegs := by revert hr'; revert r; decide
      have h2 : r ≠ .rax := by
        have : ∀ r ∈ calleeSaved, r ≠ Reg.rax := by decide
        exact this r hr'
      rw [finState_gpr (hnps r h1) (hngs r h1) h2]
      exact ha.1 r hr'
    · rw [← ha.2.1]
      apply Mem.readW_congr
      intro i hi
      rw [finState_other.1]
      exact hmo _ (slot_not_below hst (by
        simp only [Region.Contains]
        rw [show s.gpr .rsp + BitVec.ofNat 64 i - s.gpr .rsp = BitVec.ofNat 64 i by
          rw [BitVec.add_comm, BitVec.add_sub_cancel], BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        simp only [Nat.reduceDiv] at hi; omega))
    · rw [finState_other.2.2.2.2.2.1, fixMx_ctl]; exact ha.2.2
    · refine hpost s u _ hs hq (fun x hx => hmo x (outB s hs x hx)) ?_
      rw [finState_rax (hngs _ (by decide))]
      exact retVal_low hrb _
  · -- Constant time.
    cases e₁ with | seq a₁ b₁ =>
    cases e₂ with | seq a₂ b₂ =>
    obtain ⟨m₁, rfl, -⟩ := tail s₁ _ _ _ _ h₁ a₁ b₁
    obtain ⟨m₂, rfl, -⟩ := tail s₂ _ _ _ _ h₂ a₂ b₂
    rw [hct _ _ _ _ _ _ h₁ h₂ hp a₁ a₂, contract_pub_rsp hA hp]
  · -- No residue.
    cases e₁ with | seq a₁ b₁ =>
    cases e₂ with | seq a₂ b₂ =>
    rename_i u₁ _ _ u₂ _ _
    obtain ⟨m₁, -, rfl, hmo₁, hz₁, hu₁⟩ := tail s₁ _ _ _ _ h₁ a₁ b₁
    obtain ⟨m₂, -, rfl, hmo₂, hz₂, hu₂⟩ := tail s₂ _ _ _ _ h₂ a₂ b₂
    obtain ⟨ha₁, -, -, -⟩ := run s₁ _ _ h₁ a₁
    obtain ⟨ha₂, -, -, -⟩ := run s₂ _ _ h₂ a₂
    have ho' := ho
    obtain ⟨hrd, hwr, hg, -, -, -, -, -, hxm, hy, hz, hyH, hzH, hmx, hm⟩ := ho
    have hsp' : s₁.gpr .rsp = s₂.gpr .rsp := hg .rsp (by decide)
    have rw₁ := Exec.rdwr a₁
    have rw₂ := Exec.rdwr a₂
    -- Below the level `evex`, the code keeps `zmm16`–`zmm31` and MXCSR.
    have lv1 := hl1
    have k1 : v ≠ .evex → (u₁.ymmH = s₁.ymmH ∧ u₁.zmmHiH = s₁.zmmHiH ∧ u₁.mxcsr = s₁.mxcsr) ∧
        (u₂.ymmH = s₂.ymmH ∧ u₂.zmmHiH = s₂.zmmHiH ∧ u₂.mxcsr = s₂.mxcsr) := fun hne => by
      have k₁ := Exec.vecKeep1 (lv1 hne) a₁
      have k₂ := Exec.vecKeep1 (lv1 hne) a₂
      simp only [vk1, Prod.mk.injEq] at k₁ k₂
      exact ⟨k₁, k₂⟩
    have cH : v ≠ .evex → ∀ w : State, (clearedH v w).ymmH = w.ymmH ∧ (clearedH v w).zmmHiH = w.zmmHiH :=
      fun hne w => by cases v <;> first | exact ⟨rfl, rfl⟩ | exact absurd rfl hne
    have hdep : c.x86_64Depth < 2 ^ 64 := by omega
    have f₁ := Exec.stackFrame hsp a₁ hdep
    have f₂ := Exec.stackFrame hsp a₂ hdep
    have cs_ : ∀ r : Reg, r ∉ scratchRegs → r ≠ .rax → r ∈ calleeSaved := by intro r; cases r <;> decide
    have upper : ∀ x, ¬ (v ≠ .sse ∧ x ∈ xs) → u₁.ymmHi x = u₂.ymmHi x ∧ u₁.zmmHi x = u₂.zmmHi x :=
      hup _ _ _ _ _ _ h₁ h₂ hp ho' a₁ a₂
    refine ⟨?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_⟩
    · rw [finState_other.2.1, finState_other.2.1, rw₁.1, rw₂.1, hrd]
    · rw [finState_other.2.2.1, finState_other.2.2.1, rw₁.2, rw₂.2, hwr]
    · by_cases hs : r ∈ scratchRegs
      · have h11 : r ≠ .rax := hr
        by_cases hg' : r ∈ gs
        · simp [finState, clearedG, hg']
        · by_cases hp' : r ∈ ps
          · simp [finState, clearedG, State.setReg, clearedP_gpr, hg', hp', h11]
          · rw [finState_gpr hp' hg' h11, finState_gpr hp' hg' h11, Exec.gpr (hgk r hs hg' hp') a₁,
              Exec.gpr (hgk r hs hg' hp') a₂]
            exact hg r hr
      · rw [finState_gpr (hnps r hs) (hngs r hs) hr, finState_gpr (hnps r hs) (hngs r hs) hr,
          ha₁.1 r (cs_ r hs hr), ha₂.1 r (cs_ r hs hr)]
        exact hg r hr
    · rw [finState_rax (hngs _ (by decide)), finState_rax (hngs _ (by decide)), retVal_hi hrb, retVal_hi hrb]
    · rw [finState_other.2.2.2.2.2.2.1, finState_other.2.2.2.2.2.2.1]
    · rw [finState_other.2.2.2.2.2.2.2.1, finState_other.2.2.2.2.2.2.2.1]
    · rw [finState_other.2.2.2.2.2.2.2.2.1, finState_other.2.2.2.2.2.2.2.2.1]
    · rw [finState_other.2.2.2.2.2.2.2.2.2, finState_other.2.2.2.2.2.2.2.2.2]
    · rw [finState_xmm, finState_xmm]
      funext x
      split
      · rfl
      · rename_i hx
        rcases hxs with h | h
        · exact absurd (h x) hx
        · rw [Exec.xmmKeep h a₁, Exec.xmmKeep h a₂, hxm]
    · rw [finState_ymmHi, finState_ymmHi]
      funext x
      split
      · rfl
      · rename_i hn; exact (upper x hn).1
    · rw [finState_zmmHi, finState_zmmHi]
      funext x
      split
      · rfl
      · rename_i hn; exact (upper x hn).2
    · rw [finState_other.2.2.2.1, finState_other.2.2.2.1]
      by_cases he : v = .evex
      · subst he; rfl
      · rw [(cH he _).1, (cH he _).1, (k1 he).1.1, (k1 he).2.1, hyH]
    · rw [finState_other.2.2.2.2.1, finState_other.2.2.2.2.1]
      by_cases he : v = .evex
      · subst he; rfl
      · rw [(cH he _).2, (cH he _).2, (k1 he).1.2.1, (k1 he).2.2.1, hzH]
    · rw [finState_other.2.2.2.2.2.1, finState_other.2.2.2.2.2.1]
      by_cases he : v = .evex
      · exact fixMx_congr v he (by rw [ha₁.2.2, ha₂.2.2, hmx])
      · rw [(k1 he).1.2.2, (k1 he).2.2.2, hmx]
    · rw [finState_other.1, finState_other.1]
      have hx' : ∀ r ∈ s₁.rd ++ s₁.wr, ¬ r.Contains x 1 := by
        rw [finState_other.2.1, finState_other.2.2.1, rw₁.1, rw₁.2] at hx
        exact hx
      by_cases hb : (⟨s₁.gpr .rsp - BitVec.ofNat 64 stack, stack⟩ : Region).Contains x 1
      · by_cases hw : WCov ks cs (s₁.gpr .rsp) x
        · rw [hz₁ x hw, hz₂ x (hsp' ▸ hw)]
        · rw [hu₁ x hw, hu₂ x (hsp' ▸ hw)]
          exact hres _ _ _ _ _ _ h₁ h₂ hp ho' hun a₁ a₂ x hb hw
      · have nd : ∀ sp : Addr, sp = s₁.gpr .rsp →
            ¬ (⟨sp - BitVec.ofNat 64 c.x86_64Depth, c.x86_64Depth⟩ : Region).Contains x 1 := by
          rintro sp rfl hc; exact hb (below_sub hd (by omega) x hc)
        have nw : ∀ r ∈ s₁.wr, ¬ r.Contains x 1 := fun r hr => hx' r (List.mem_append_right _ hr)
        rw [hmo₁ x hb, hmo₂ x (hsp' ▸ hb),
          f₁ x (fun r hr => by
            rcases List.mem_append.mp hr with hr | hr
            · exact nw r hr
            · simp only [List.mem_singleton] at hr; subst hr; exact nd _ rfl),
          f₂ x (fun r hr => by
            rcases List.mem_append.mp hr with hr | hr
            · exact nw r (hwr ▸ hr)
            · simp only [List.mem_singleton] at hr; subst hr; exact nd _ hsp'.symm)]
        exact hm x hx'

end

/-! ## The baseline ISA's callers of functions with AVX instructions

Code of the baseline ISA (level `sse`) that may run, through a table of
functions, functions with AVX instructions that end with `vzeroupper`
(`UpperLock.up`): two runs that may differ only in secrets take the same
path (they are constant time, and the functions' addresses are public,
`Abi.withTables`), so the upper halves of the vector registers agree at the
end (`UpperLock.lock`), and the clearing at the level `sse`, which needs no
CPU feature, leaves no residue. -/

/-- The functions the tables `ts` name. -/
def tableFns (ts : List (String × List FnTable)) : List String := ts.flatMap fun t => t.2.flatMap (·.fns)

theorem contract_pub {A : Abi isa} {sig : Sig} {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))} {s₁ s₂ : State}
    (h : (sig.contract A pre post wa stack leak).pub s₁ s₂) : A.pub s₁ s₂ := by
  simp only [Sig.contract] at h
  split at h
  · exact h.elim
  · cases leak with
    | none => exact h.1
    | some f => exact h.1.1

/-- The functions of the tables have the same addresses in two runs that agree on what is public. -/
theorem tables_pub_syms {A : Abi isa} {sig : Sig} {ts : List (String × List FnTable)} {pm : Bool}
    {s₁ s₂ : State} (h : ((A.withTables sig ts).withMode pm).pub s₁ s₂) :
    ∀ f ∈ tableFns ts, s₁.syms f = s₂.syms f := by
  have h' : (A.withTables sig ts).pub s₁ s₂ := by
    cases pm
    · exact h
    · exact h.1
  intro f hf
  cases ts with
  | nil => simp [tableFns] at hf
  | cons t ts => exact h'.2.1 f hf

/-- `UpperOk` at the level `sse`, for constant-time code whose upper halves
agree at the end if they did at the start (`UpperLock.up`), and whose
functions called indirectly have public addresses. -/
theorem upperOk_lock {A : Abi isa} {sig : Sig} {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))} {xs : List XReg} {c : Prog isa}
    (hct : ConstantTime isa (sig.contract A pre post wa stack leak).pre (sig.contract A pre post wa stack leak).pub c)
    (hsy : ∀ s₁ s₂, A.pub s₁ s₂ → ∀ f ∈ UpperLock.inames c, s₁.syms f = s₂.syms f)
    (hup : UpperLock.up c true = true) : UpperOk .sse xs c (sig.contract A pre post wa stack leak) := by
  intro s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ hp ho a₁ a₂ x _
  have ht := hct s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ hp a₁ a₂
  obtain ⟨-, -, -, -, -, -, -, -, -, hy, hz, -, -, -, -⟩ := ho
  have hu := (UpperLock.lock a₁ a₂ (r₁ := []) (r₂ := []) (by rw [ht]) (hsy _ _ (contract_pub hp))).2 true hup
    fun _ => ⟨hy, hz⟩
  exact ⟨congrFun hu.1 x, congrFun hu.2 x⟩

/-- The side conditions of `scrubRegUp` that the emitter evaluates: the
code's instructions are below the level `evex`, its upper halves agree at
the end if they did at the start, and it calls indirectly only the
functions of its tables. -/
def UpOk (code : Prog isa) (tables : List (String × List FnTable)) : Bool :=
  code.all (fun i => decide (i.vecLevel ≤ 1)) && UpperLock.up code true &&
    (UpperLock.inames code).all (fun f => decide (f ∈ tableFns tables))

theorem upOk_spec {code : Prog isa} {tables : List (String × List FnTable)} (h : UpOk code tables = true) :
    (∀ i ∈ instrs code, i.vecLevel ≤ 1) ∧ UpperLock.up code true = true ∧
      ∀ f ∈ UpperLock.inames code, f ∈ tableFns tables := by
  simp only [UpOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨fun i hi => by simpa using Code.all_instrs h.1.1 i hi, h.1.2, h.2⟩

theorem scrubCodeU_verified {api : Api} (r : Registration api target)
    (hd : r.code.x86_64Depth ≤ r.stack) (hst : r.stack + 8 < 2 ^ 64) (h8 : r.stack % 8 = 0)
    (hok : UpOk r.code r.tables = true)
    (hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨ api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)) :
    Verified target (scrub .sse (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
        (xsOf r.code (allKs (chunks r.stack))) (psOf (allKs (chunks r.stack))) (gsOf Taint.clobbers r.code)
        (allKs (chunks r.stack)) (chunks r.stack) r.code) r.contract ∧
      NoResidue (scrub .sse (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
        (xsOf r.code (allKs (chunks r.stack))) (psOf (allKs (chunks r.stack))) (gsOf Taint.clobbers r.code)
        (allKs (chunks r.stack)) (chunks r.stack) r.code) r.contract
        (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits) := by
  obtain ⟨hl1, hup, hnames⟩ := upOk_spec hok
  obtain ⟨pre, post, leak, e⟩ := r.ofSig
  have hv := r.verified
  have hp := hpost
  rw [e] at hv hp ⊢
  have hrb' := hrb
  rw [← withMode_ptrBits ((abi.withConsts r.consts).withTables api.sig r.tables) api.pubMode] at hrb' hp ⊢
  have hr := resOk_all r.code (api.sig.contract (((abi.withConsts r.consts).withTables api.sig r.tables).withMode
    api.pubMode) pre post api.writeArgs r.stack leak) h8
  exact Verified.scrubU (ScrubAbi.of r.consts api.sig r.tables api.pubMode) hv (SpSafe.of_all r.spSafe) hd
    (chunks_sum r.stack) hst (chunks_valid h8) (fun _ => hl1)
    (upperOk_lock hv.2.1 (fun s₁ s₂ h f hf => tables_pub_syms h f (hnames f hf)) hup)
    hrb' hp hr (tailOk_of _ _ _) (xs_of _ _) (fun e => absurd e (by decide)) (evexReg_of_ne (c := r.code) (by decide)).2
    (gs_of _ _)

/-- `r`, scrubbed at the level `sse` with every granule of its stack wiped,
for code below the level `evex` whose functions with AVX instructions, run
through its tables, end with `vzeroupper` (`UpOk`). -/
def scrubRegUp {api : Api} (r : Registration api target)
    (hd : r.code.x86_64Depth ≤ r.stack) (hst : r.stack + 8 < 2 ^ 64) (h8 : r.stack % 8 = 0)
    (hok : UpOk r.code r.tables = true)
    (hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨ api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (hw : r.written = []) : Registration api target where
  suffix := r.suffix
  consts := r.consts
  tables := r.tables
  stack := r.stack
  code := scrub .sse (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
    (xsOf r.code (allKs (chunks r.stack))) (psOf (allKs (chunks r.stack))) (gsOf Taint.clobbers r.code)
    (allKs (chunks r.stack)) (chunks r.stack) r.code
  contract := r.contract
  verified := (scrubCodeU_verified r hd hst h8 hok hrb hpost).1
  ofApi := r.ofApi
  ofSig := r.ofSig
  spSafe := scrub_spSafe .sse _ _ _ _ _ _ (tailOk_of 0 r.code (allKs (chunks r.stack))).psOk
    (tailOk_of 0 r.code (allKs (chunks r.stack))).gsOk r.spSafe
  written := r.written
  writtenOk := by
    rw [hw]; exact fun _ _ _ _ _ => True.intro
  extra := r.extra
  vendor := r.vendor
  notWith := r.notWith
  residue := some ⟨(scrubCodeU_verified r hd hst h8 hok hrb hpost).2⟩

/-- `r`, scrubbed by `scrubRegUp` if its side conditions hold and the
clearing needs no CPU feature that `r`'s code does not; otherwise `r`. -/
def withUp {api : Api} (r : Registration api target)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)) :
    Registration api target :=
  if hd : r.code.x86_64Depth ≤ r.stack then
  if hst : r.stack + 8 < 2 ^ 64 then
  if h8 : r.stack % 8 = 0 then
  if hok : UpOk r.code r.tables = true then
  if hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨
      api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64 then
  if hw : r.written = [] then
    let r' := scrubRegUp r hd hst h8 hok hrb hpost hw
    if (Code.requiresDedup isa.requires r'.code).all
        (fun f => (Code.requiresDedup isa.requires r.code).contains f) then r' else r
  else r else r else r else r else r else r

/-- `withScrubAll`, but where it leaves `r` unscrubbed, `withUp`. -/
def withScrubAllUp {api : Api} (r : Registration api target)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)) :
    Registration api target :=
  if (withScrubAll r hpost).residue.isSome then withScrubAll r hpost else withUp r hpost

end VG.X86_64.Scrub
