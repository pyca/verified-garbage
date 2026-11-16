module

public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.KeepReg

/-!
# Clearing only the vector registers the code writes (x86-64)

`Scrub.scrubReg` clears every SSE register after code that may write one.
`RScrub.withScrubXs` scrubs code with no VEX or EVEX instruction, no frame
and no call, and clears only the SSE registers its instructions may write
(`xsW`, from `writesX`): the others hold what they held on entry
(`Exec.xmmKeepAt`), the same in two runs. Nothing of the stack is wiped:
such code leaves the stack below the stack pointer as it was
(`resOk_noStack`).

`Verified.scrubM` is used as it is, for the clearing of every SSE register:
the clearing of fewer runs along the same trace to the same state but for
the SSE registers (`tail_xs`), so it is verified, and returns without
secret residue, if that one does (`Verified.scrubXs`).

The registration may state how much of its arrays it writes
(`Registration.written`), and the scrubbed one states it too: the clearing
writes only the stack below the stack pointer, which no buffer of a
contract that `Sig.contract` derives overlaps (`writtenWithin_scrub`).
-/

@[expose] public section

open VG.Impl.Scrub.X86_64

namespace VG.X86_64.Scrub

/-! ## What the registration states it writes -/

/-- An array of the parameters is one of their buffers. -/
theorem arrays_bufs : ∀ {ps : List (String × Param)} {vs : List (BitVec 64)} {n : String} {r : Region},
    (n, r) ∈ Sig.arrays ps vs → ∃ w, (r, w) ∈ Sig.bufs ps vs
  | [], _, _, _, h => by simp [Sig.arrays] at h
  | (_, .int ..) :: _, [], _, _, h => by simp [Sig.arrays] at h
  | (_, .int ..) :: _, _ :: _, _, _, h => by
    simp only [Sig.arrays, Sig.bufs] at h ⊢; exact arrays_bufs h
  | (_, .array ..) :: _, [], _, _, h => by simp [Sig.arrays] at h
  | (_, .array m _ _) :: _, _ :: _, _, _, h => by
    simp only [Sig.arrays, Sig.bufs, List.mem_cons, Prod.mk.injEq] at h ⊢
    rcases h with ⟨-, rfl⟩ | h
    · exact ⟨m, .inl ⟨rfl, rfl⟩⟩
    · obtain ⟨w, hw⟩ := arrays_bufs h; exact ⟨w, .inr hw⟩
  | (_, .slice ..) :: _, [], _, _, h => by simp [Sig.arrays] at h
  | (_, .slice ..) :: _, [_], _, _, h => by simp [Sig.arrays] at h
  | (_, .slice ..) :: _, _ :: _ :: _, _, _, h => by
    simp only [Sig.arrays, Sig.bufs, List.mem_cons] at h ⊢
    obtain ⟨w, hw⟩ := arrays_bufs h; exact ⟨w, .inr hw⟩
  | (_, .slices ..) :: _, [], _, _, h => by simp [Sig.arrays] at h
  | (_, .slices ..) :: _, [_], _, _, h => by simp [Sig.arrays] at h
  | (_, .slices ..) :: _, _ :: _ :: _, _, _, h => by
    simp only [Sig.arrays, Sig.bufs] at h ⊢; exact arrays_bufs h
  | (_, .table _) :: _, [], _, _, h => by simp [Sig.arrays] at h
  | (_, .table _) :: _, _ :: _, _, _, h => by
    simp only [Sig.arrays, Sig.bufs] at h ⊢; exact arrays_bufs h

/-- The buffers of a contract that `Sig.contract` derives are apart from the
`stack` bytes below the stack pointer. -/
theorem bufs_stack {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))} {s : State}
    (h : (sig.contract A pre post wa stack leak).pre s) {vals : State → List (BitVec 64)}
    (hv : abi.args ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)) = some vals) (hst : stack ≠ 0) :
    ∀ b ∈ Sig.bufs sig.params (vals s),
      (⟨s.gpr .rsp - BitVec.ofNat 64 stack, stack⟩ : Region).Disjoint b.1 := by
  simp only [Sig.contract] at h
  split at h
  · exact h.elim
  rename_i vals' hv'
  rw [hA.args, hA.ptrBits] at hv'
  obtain rfl := Option.some.inj (hv'.symm.trans hv)
  obtain ⟨-, -, -, -, hres, -⟩ := h
  intro b hb
  rw [hA.reserved] at hres
  refine hres _ ?_ b (List.mem_append_left _ (List.mem_append_left _ hb))
  cases stack with
  | zero => exact absurd rfl hst
  | succ n => simp [abi, stackBelow]

/-- `scrub` of code that changes no byte of its arrays past the bounds `W`
changes none either: its clearing writes only the stack below the stack
pointer, apart from every buffer. -/
theorem writtenWithin_scrub {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}
    {c : Prog isa} {v f : VecLevel} {rb : Nat} {xs : List XReg} {ps gs : List Reg} {ks cs : List Nat}
    {W : List (String × Nat)}
    (h : Verified target c (sig.contract A pre post wa stack leak)) (hcs : cs.sum = stack)
    (hv : ∀ b ∈ cs, 0 < b ∧ b < 4096 ∧ b % 8 = 0) (ht : TailOk rb xs ps gs ks)
    (hev : ∀ p : Addr, cs.sum ≤ p.toNat → EvexOk f ks cs p)
    (hW : ∀ s t s', (sig.contract A pre post wa stack leak).pre s → Exec isa c s t s' →
      Sig.writtenWithin abi sig W s s') :
    ∀ s t s', (sig.contract A pre post wa stack leak).pre s →
      Exec isa (scrub v rb xs ps gs ks cs c f) s t s' → Sig.writtenWithin abi sig W s s' := by
  intro s t s' hs he
  cases he with
  | seq a b =>
  rename_i u _ _
  obtain ⟨_, u', he', ha, -⟩ := h.1 s hs
  obtain ⟨-, rfl⟩ := Exec.det a he'
  have hr : u.gpr .rsp = s.gpr .rsp := ha.1 .rsp (by decide)
  have hl : cs.sum ≤ (u.gpr .rsp).toNat := by
    rcases (contract_pre_scrub hA hs).1 with h0 | h0
    · rw [hcs, h0]; exact Nat.zero_le _
    · rw [hcs, hr]; exact h0
  obtain ⟨m', e, -, hu⟩ := tail_run v rb cs ht u hv hl (hev _ hl)
  obtain ⟨-, rfl⟩ := Exec.det b e
  have hw := hW s _ u hs a
  cases W with
  | nil => exact True.intro
  | cons w W =>
  simp only [Sig.writtenWithin] at hw ⊢
  revert hw
  cases hargs : abi.args ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)) with
  | none => exact fun _ => True.intro
  | some vals =>
  intro hw w' hw' b hb hn i hi hlt
  rw [← hw w' hw' b hb hn i hi hlt]
  show (finState v rb xs ps gs m' u f).mem _ = u.mem _
  rw [finState_other.1]
  refine hu _ fun hc => ?_
  have hc1 := hc.1
  rw [hr, hcs] at hc1
  have hst : stack ≠ 0 := by
    rintro rfl; simp [Region.Contains] at hc1
  obtain ⟨m, hm⟩ := arrays_bufs hb
  refine bufs_stack hA hs hargs hst _ hm _ hc1 ?_
  simp only [Region.Contains]
  rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat]
  have := Nat.mod_le i (2 ^ 64)
  omega

/-- Two runs of code with no frame and no call leave the same bytes in the
stack below the stack pointer, with none of it wiped: the code writes only
its buffers, which are apart from that stack. -/
theorem resOk_noStack {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))} {c : Prog isa} {cs : List Nat}
    (hsp : c.all (fun i => !isa.writesSp i) = true) (hd : c.x86_64Depth = 0) :
    ResOk c (sig.contract A pre post wa stack leak) stack [] cs := by
  intro s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ _ ho _ a₁ a₂ x hb _
  obtain ⟨hrd, hwr, hg, -, -, -, -, -, -, -, -, -, -, -, hm⟩ := ho
  have hst : stack ≠ 0 := by
    rintro rfl; simp [Region.Contains] at hb
  have out : ∀ s, (sig.contract A pre post wa stack leak).pre s → s.gpr .rsp = s₁.gpr .rsp →
      ∀ r ∈ s.rd ++ s.wr, ¬ r.Contains x 1 := fun s hs e r hr hx =>
    ((contract_pre_scrub hA hs).2 r hr).2 hst x (e ▸ hb) hx
  have keep : ∀ {s u : State} {t : List Leak}, Exec isa c s t u → (∀ r ∈ s.wr, ¬ r.Contains x 1) →
      u.mem x = s.mem x := fun {s u t} a hw =>
    Exec.stackFrame (SpSafe.of_all hsp) a (by rw [hd]; decide) x fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact hw r hr
      · simp only [List.mem_singleton] at hr; subst hr
        rw [hd]; simp [Region.Contains]
  rw [keep a₁ fun r hr => out s₁ h₁ rfl r (List.mem_append_right _ hr),
    keep a₂ fun r hr => out s₂ h₂ (hg .rsp (by decide)).symm r (List.mem_append_right _ hr)]
  exact hm x (out s₁ h₁ rfl)


/-! ## The SSE registers the code writes -/

/-- Whether an instruction may write the SSE register `x`: the register an
SSE load or binary operation writes, and for any other instruction, whether
it may write a vector register at all. -/
def writesX (x : XReg) : Instr → Bool
  | .movdquLoad d _ => d == x
  | .xop (.bin _ d _) => d == x
  | i => writesVec i

/-- The SSE registers `c` may write. -/
def xsW (c : Prog isa) : List XReg := xregs.filter fun x => !c.all (fun i => !writesX x i)

theorem writesX_of {x : XReg} {i : Instr} (h : writesX x i = false) :
    writesVec i = false ∨ (∃ d m, i = .movdquLoad d m ∧ ¬ x = d) ∨ ∃ o d r, i = .xop (.bin o d r) ∧ ¬ x = d := by
  cases i with
  | movdquLoad d m =>
    exact .inr (.inl ⟨d, m, rfl, fun e => by simp [writesX, e] at h⟩)
  | xop op =>
    cases op with
    | bin o d r => exact .inr (.inr ⟨o, d, r, rfl, fun e => by simp [writesX, e] at h⟩)
    | _ => exact .inl h
  | _ => exact .inl h

/-- An instruction that may not write `x` keeps it. -/
theorem exec_xmmAt {x : XReg} {i : Instr} (hw : writesX x i = false) {s s' : State}
    (h : exec i s = some s') : s'.xmm x = s.xmm x := by
  rcases writesX_of hw with hv | ⟨d, m, rfl, hx⟩ | ⟨o, d, r, rfl, hx⟩
  · exact congrFun (KeepReg.exec_xmm (by cases i <;> exact hv) h) x
  · simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨v, -, rfl⟩ := h
    exact RegUpd.xmm_setXmm_of_ne _ _ hx
  · simp only [exec, Option.some.injEq] at h
    subst h
    exact RegUpd.xmm_setXmm_of_ne _ _ hx

/-- Code none of whose instructions may write `x` keeps it. -/
theorem Exec.xmmKeepAt {x : XReg} {c : Prog isa} (hc : ∀ i ∈ instrs c, writesX x i = false)
    {s s' : State} {t : List Leak} (h : Exec isa c s t s') : s'.xmm x = s.xmm x :=
  Exec.keep (fun s : State => s.xmm x) (ok := fun i : Instr => writesX x i = false)
    (fun {i s s'} hi he => exec_xmmAt hi he)
    (fun {i j s s₁ s₂ s'} _ hp hq hb => by
      have e₁ : s₁.xmm = s.xmm := by
        cases i <;> simp only [isa, push, reduceCtorEq] at hp
        case push rs => split at hp <;> cases hp; exact Residue.pushRegs_xmm s rs
        case alloc => split at hp <;> cases hp; rfl
      have e₂ : s'.xmm = s₂.xmm := by
        cases j <;> simp only [isa, pop, reduceCtorEq] at hq
        case pop r k => split at hq <;> cases hq; exact Residue.popReg_xmm s₂ _ _
        case free => split at hq <;> cases hq; rfl
      show s'.xmm x = s.xmm x
      rw [e₂, show s₂.xmm x = s₁.xmm x from hb, e₁]) hc
    (.inr fun _ _ _ _ hc hr hb => by
      simp only [isa, call, Option.some.injEq] at hc; subst hc
      simp only [isa, ret] at hr; split at hr <;> cases hr
      exact hb) h

theorem xsW_keep (c : Prog isa) (x : XReg) (hx : x ∉ xsW c) : ∀ i ∈ instrs c, writesX x i = false := by
  have h : c.all (fun i => !writesX x i) = true := by
    by_contra hc
    exact hx (List.mem_filter.mpr ⟨mem_xregs x, by simpa using hc⟩)
  exact fun i hi => by simpa using Code.all_instrs h i hi

/-! ## Clearing fewer SSE registers -/

/-- The state the clearing leaves at the level `sse`, with nothing of the
stack wiped, given what it leaves in the SSE registers. -/
def finX (rb : Nat) (gs : List Reg) (m : Mem) (u : State) (X : XReg → BitVec 128) : State :=
  clearedG gs (({ u with xmm := X, mem := m, mxcsr := fixMx .sse u.mxcsr } : State).setReg .rax
    (retVal rb (u.gpr .rax)))

theorem finState_sse (rb : Nat) (xs : List XReg) (gs : List Reg) (m : Mem) (u : State) :
    finState .sse rb xs [] gs m u .sse = finX rb gs m u fun x => if x ∈ xs then 0 else u.xmm x := by
  simp [finState, finX, clearedP, clearedH, clearedV]

/-- What the clearing needs of what it clears, with nothing of the stack wiped. -/
theorem tailOk_nil (rb : Nat) (xs : List XReg) {gs : List Reg} (hgs : ∀ r ∈ gs, r ∈ scratchRegs)
    (hne : gs ≠ []) : TailOk rb xs [] gs [] :=
  ⟨fun h => absurd rfl h, fun h => absurd rfl h, fun _ h => (nomatch h), hgs, hne⟩

/-- The clearing of the SSE registers `xs`, and that of all of them, run
along the same trace, to states that differ only in the SSE registers. -/
theorem tail_xs (rb : Nat) (xs : List XReg) {gs : List Reg} (hgs : ∀ r ∈ gs, r ∈ scratchRegs)
    (hne : gs ≠ []) (cs : List Nat) (u : State) (hv : ∀ b ∈ cs, 0 < b ∧ b < 4096 ∧ b % 8 = 0)
    (hs : cs.sum ≤ (u.gpr .rsp).toNat) :
    ∃ m T, Exec isa (scrubTail .sse rb xs [] gs [] cs) u T
        (finX rb gs m u fun x => if x ∈ xs then 0 else u.xmm x) ∧
      Exec isa (scrubTail .sse rb xregs [] gs [] cs) u T (finX rb gs m u fun _ => 0) := by
  obtain ⟨m, e, hz, hu⟩ := tail_run (f := .sse) .sse rb cs (tailOk_nil rb xs hgs hne) u hv hs (fun h => nomatch h)
  obtain ⟨m', e', hz', hu'⟩ := tail_run (f := .sse) .sse rb cs (tailOk_nil rb xregs hgs hne) u hv hs (fun h => nomatch h)
  have hm : m' = m := by
    funext x
    by_cases hw : WCov [] cs (u.gpr .rsp) x
    · rw [hz x hw, hz' x hw]
    · rw [hu x hw, hu' x hw]
  rw [finState_sse] at e e'
  rw [hm] at e'
  simp only [mem_xregs, ↓reduceIte] at e'
  exact ⟨m, _, e, e'⟩

section
variable {A : Abi isa} {sig : Sig} {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
  {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
  {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}

/-- Code verified against a contract that `Sig.contract` derives, followed
by the clearing of the SSE registers `xs` at the level `sse`, with nothing
of the stack wiped: verified against the same contract and without secret
residue, if it is with every SSE register cleared (`hall`, as
`Verified.scrubM` gives it) and no instruction of the code may write an SSE
register that is not in `xs`. -/
theorem Verified.scrubXs {c : Prog isa} {xs : List XReg} {gs : List Reg} {cs : List Nat}
    (hA : ScrubAbi A)
    (h : Verified target c (sig.contract A pre post wa stack leak))
    (hcs : cs.sum = stack) (hv : ∀ b ∈ cs, 0 < b ∧ b < 4096 ∧ b % 8 = 0)
    (hpost : PostOut (sig.contract A pre post wa stack leak) (sig.retBits A.ptrBits))
    (hgs : ∀ r ∈ gs, r ∈ scratchRegs) (hne : gs ≠ [])
    (hk : ∀ x, x ∉ xs → ∀ i ∈ instrs c, writesX x i = false)
    (hall : Verified target (Impl.Scrub.X86_64.scrub .sse (sig.retBits A.ptrBits) xregs [] gs [] cs c)
        (sig.contract A pre post wa stack leak) ∧
      NoResidue (Impl.Scrub.X86_64.scrub .sse (sig.retBits A.ptrBits) xregs [] gs [] cs c)
        (sig.contract A pre post wa stack leak) (sig.retBits A.ptrBits)) :
    Verified target (Impl.Scrub.X86_64.scrub .sse (sig.retBits A.ptrBits) xs [] gs [] cs c)
        (sig.contract A pre post wa stack leak) ∧
      NoResidue (Impl.Scrub.X86_64.scrub .sse (sig.retBits A.ptrBits) xs [] gs [] cs c)
        (sig.contract A pre post wa stack leak) (sig.retBits A.ptrBits) := by
  obtain ⟨⟨acor, act, asat⟩, ares⟩ := hall
  -- Both clearings, after a run of `c`.
  have tails : ∀ s t u, (sig.contract A pre post wa stack leak).pre s → Exec isa c s t u →
      ∃ m T, Exec isa (scrubTail .sse (sig.retBits A.ptrBits) xs [] gs [] cs) u T
          (finX (sig.retBits A.ptrBits) gs m u fun x => if x ∈ xs then 0 else u.xmm x) ∧
        Exec isa (scrubTail .sse (sig.retBits A.ptrBits) xregs [] gs [] cs) u T
          (finX (sig.retBits A.ptrBits) gs m u fun _ => 0) := by
    intro s t u hs he
    obtain ⟨t', u', he', ha, -⟩ := h.1 s hs
    obtain ⟨-, rfl⟩ := Exec.det he he'
    have hr : u.gpr .rsp = s.gpr .rsp := ha.1 .rsp (by decide)
    refine tail_xs _ xs hgs hne cs u hv ?_
    rcases (contract_pre_scrub hA hs).1 with h0 | h0
    · rw [hcs, h0]; exact Nat.zero_le _
    · rw [hcs, hr]; exact h0
  refine ⟨⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, asat⟩,
    fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp ho hun e₁ e₂ => ?_⟩
  · -- Correctness.
    obtain ⟨t, w, he, ha, hq⟩ := acor s hs
    cases he with | seq a b =>
    obtain ⟨m, T, e, e'⟩ := tails s _ _ hs a
    obtain ⟨-, rfl⟩ := Exec.det b e'
    exact ⟨_, _, .seq a e, ha, hpost s _ _ hs hq (fun _ _ => rfl) rfl⟩
  · -- Constant time.
    cases e₁ with | seq a₁ b₁ =>
    cases e₂ with | seq a₂ b₂ =>
    obtain ⟨m₁, T₁, f₁, f₁'⟩ := tails s₁ _ _ h₁ a₁
    obtain ⟨m₂, T₂, f₂, f₂'⟩ := tails s₂ _ _ h₂ a₂
    obtain ⟨rfl, -⟩ := Exec.det b₁ f₁
    obtain ⟨rfl, -⟩ := Exec.det b₂ f₂
    exact act _ _ _ _ _ _ h₁ h₂ hp (.seq a₁ f₁') (.seq a₂ f₂')
  · -- No residue.
    cases e₁ with | seq a₁ b₁ =>
    cases e₂ with | seq a₂ b₂ =>
    rename_i u₁ _ _ u₂ _ _
    obtain ⟨m₁, T₁, f₁, f₁'⟩ := tails s₁ _ _ h₁ a₁
    obtain ⟨m₂, T₂, f₂, f₂'⟩ := tails s₂ _ _ h₂ a₂
    obtain ⟨-, rfl⟩ := Exec.det b₁ f₁
    obtain ⟨-, rfl⟩ := Exec.det b₂ f₂
    obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, -, o10, o11, o12, o13, o14, o15⟩ :=
      ares _ _ _ _ _ _ h₁ h₂ hp ho hun (.seq a₁ f₁') (.seq a₂ f₂')
    refine ⟨o1, o2, o3, o4, o5, o6, o7, o8, ?_, o10, o11, o12, o13, o14, o15⟩
    show (fun x => if x ∈ xs then 0 else u₁.xmm x) = fun x => if x ∈ xs then 0 else u₂.xmm x
    funext x
    by_cases hx : x ∈ xs
    · rw [ite_eq_left hx, ite_eq_left hx]
    · rw [ite_eq_right hx, ite_eq_right hx, Exec.xmmKeepAt (hk x hx) a₁, Exec.xmmKeepAt (hk x hx) a₂]
      exact congrFun ho.2.2.2.2.2.2.2.2.1 x

end

/-! ## Registrations -/

/-- `resOk_noStack`, for a registration. -/
theorem resOk_noStack_reg {api : Api} (r : Registration api target) (hd : r.code.x86_64Depth = 0) :
    ResOk r.code r.contract r.stack [] (chunks r.stack) := by
  obtain ⟨pre, post, leak, e⟩ := r.ofSig
  rw [e]
  exact resOk_noStack (ScrubAbi.of r.consts api.sig r.tables api.pubMode) r.spSafe hd

/-- `r`'s code, with no VEX or EVEX instruction, no frame and no call,
followed by the clearing of the SSE registers it may write, is verified and
returns without secret residue. -/
theorem scrubXs_ok {api : Api} (r : Registration api target)
    (hd : r.code.x86_64Depth = 0) (hst : r.stack + 8 < 2 ^ 64) (h8 : r.stack % 8 = 0)
    (hlv : r.code.all (fun i => decide (i.vecLevelR ≤ VecLevel.sse.level)) = true)
    (hmx : (mxClass r.code).isSome = true)
    (hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨ api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)) :
    Verified target (scrub .sse (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
        (xsW r.code) [] (gsOf Taint.clobbers r.code) [] (chunks r.stack) r.code) r.contract ∧
      NoResidue (scrub .sse (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
        (xsW r.code) [] (gsOf Taint.clobbers r.code) [] (chunks r.stack) r.code) r.contract
        (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits) := by
  have hr := resOk_noStack_reg r hd
  obtain ⟨pre, post, leak, e⟩ := r.ofSig
  have hv := r.verified
  have hp := hpost
  rw [e] at hv hp hr ⊢
  have hrb' := hrb
  rw [← withMode_ptrBits ((abi.withConsts r.consts).withTables api.sig r.tables) api.pubMode] at hrb' hp ⊢
  have hA := ScrubAbi.of r.consts api.sig r.tables api.pubMode
  have ht := tailOk_of 0 r.code []
  refine Verified.scrubXs hA hv (chunks_sum r.stack) (chunks_valid h8) hp ht.gsOk ht.gne (xsW_keep r.code) ?_
  exact Verified.scrubM (f := .sse) hA hv (SpSafe.of_all r.spSafe) (by rw [hd]; exact Nat.zero_le _)
    (chunks_sum r.stack) hst (chunks_valid h8)
    (fun i hi => by simpa using Code.all_instrs hlv i hi) (fun _ => MxSame.of_fun (mxFun_of hmx)) hrb' hp hr
    (tailOk_nil _ xregs ht.gsOk ht.gne) (.inl mem_xregs) (fun h => nomatch h) (fun _ _ h => nomatch h)
    (fun r hr hg _ => gs_of _ [] r hr hg (fun h => nomatch h))

/-- `r`, scrubbed: its code, with no VEX or EVEX instruction, no frame and
no call, followed by the clearing of the SSE registers it may write and of
the caller-saved general-purpose registers. It states what `r` does of how
much of its arrays it writes. -/
def scrubRegXs {api : Api} (r : Registration api target)
    (hd : r.code.x86_64Depth = 0) (hst : r.stack + 8 < 2 ^ 64) (h8 : r.stack % 8 = 0)
    (hlv : r.code.all (fun i => decide (i.vecLevelR ≤ VecLevel.sse.level)) = true)
    (hmx : (mxClass r.code).isSome = true)
    (hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨ api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)) :
    Registration api target where
  suffix := r.suffix
  consts := r.consts
  tables := r.tables
  stack := r.stack
  code := scrub .sse (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
    (xsW r.code) [] (gsOf Taint.clobbers r.code) [] (chunks r.stack) r.code
  contract := r.contract
  verified := (scrubXs_ok r hd hst h8 hlv hmx hrb hpost).1
  ofApi := r.ofApi
  ofSig := r.ofSig
  spSafe := scrub_spSafe .sse _ _ _ _ _ _ (fun _ h => nomatch h) (tailOk_of 0 r.code []).gsOk r.spSafe
  written := r.written
  writtenOk := by
    obtain ⟨pre, post, leak, e⟩ := r.ofSig
    have hv := r.verified
    have hW := r.writtenOk
    intro s t s' hs he
    have hs : r.contract.pre s := hs
    rw [e] at hv hW hs
    exact writtenWithin_scrub (v := .sse) (f := .sse) (ScrubAbi.of r.consts api.sig r.tables api.pubMode) hv (chunks_sum r.stack)
      (chunks_valid h8) (tailOk_nil _ _ (tailOk_of 0 r.code []).gsOk (tailOk_of 0 r.code []).gne)
      (fun _ _ h => nomatch h) hW s t s' hs he
  extra := r.extra
  vendor := r.vendor
  notWith := r.notWith
  residue := some ⟨(scrubXs_ok r hd hst h8 hlv hmx hrb hpost).2⟩

end VG.X86_64.Scrub

namespace VG.X86_64.RScrub

open VG.X86_64.Scrub

/-- `r`, returning without secret residue with only the SSE registers its
code may write cleared (`Scrub.scrubRegXs`), if its code has no VEX or EVEX
instruction, no frame and no call, and `scrub`'s side conditions hold;
otherwise `r` itself, which then has no proof (`Registration.residue`), as
the emitter allows only of what `ci/residue_allowlist.txt` lists. -/
def withScrubXs {api : Api} (r : Registration api target)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)) :
    Registration api target :=
  if hd : r.code.x86_64Depth = 0 then
  if hst : r.stack + 8 < 2 ^ 64 then
  if h8 : r.stack % 8 = 0 then
  if hlv : r.code.allOnce (fun i => decide (i.vecLevelR ≤ VecLevel.sse.level)) = true then
  if hmx : (mxClassOnce r.code).isSome = true then
  if hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨
      api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64 then
    scrubRegXs r hd hst h8 ((Code.allOnce_eq _ r.code).symm.trans hlv) (mxClassOnce_eq r.code ▸ hmx) hrb hpost
  else r else r else r else r else r else r

end VG.X86_64.RScrub
