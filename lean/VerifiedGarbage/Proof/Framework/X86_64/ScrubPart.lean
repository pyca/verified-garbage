module

public import VerifiedGarbage.Proof.Framework.X86_64.ScrubChunks
import VerifiedGarbage.Proof.Framework.Semantics

/-!
# x86-64 residue: clearing only the registers that may hold secrets

`scrub v rb xs ps gs ks cs c` clears the SSE registers `xs` and the
general-purpose registers `ps` and `gs` (and the upper bits of `rax`).
`Verified.scrubM` takes those from the code's instructions: every SSE
register if any instruction may write one, every caller-saved register any
instruction may write (`xsOf`, `gsOf`). Code that calls a function using the
vector registers on one path only, and clears them itself at the end of that
path, needs none of them cleared on return; nor the general-purpose registers
it leaves public on every path.

`Verified.scrubPart` clears the registers `xs` and `gs` given, any of them,
if two runs end agreeing on every register the clearing keeps (`RegsOk`):
the clearing of fewer registers runs along the same trace to the same state
but for the registers it keeps, so it is verified, and returns without
secret residue, if the clearing of those `Verified.scrubM` chooses does
(`hall`). The clearing of the stack and of MXCSR is the same in both.
`RegsOk` follows from what each run leaves in those registers, as
`resOk_of_leaves` gives the stack's `ResOk` (`RegLeaves`, `regsOk_of_leaves`).
`withScrubResCR` is `RScrub.withScrubResC` with the registers cleared given.

It is a module of its own, not part of `Scrub.lean`, so that the many
modules that import `Scrub.lean` are not rebuilt for it.
-/

@[expose] public section

open VG.Impl.Scrub.X86_64

namespace VG.X86_64.Scrub

open VG.X86_64 VG.X86_64.Residue

/-- Two runs of `c` from states that `NoResidue` relates end agreeing on the
registers that the clearing of `xs`, `ps` and `gs` keeps: the caller-saved
general-purpose registers but `rax` outside `ps` and `gs`, and the vector
registers `zmm0`–`zmm15` outside `xs`, all their bits. -/
def RegsOk (c : Prog isa) (k : Contract isa) (xs : List XReg) (ps gs : List Reg) : Prop :=
  ∀ s₁ s₂ t₁ t₂ u₁ u₂, k.pre s₁ → k.pre s₂ → k.pub s₁ s₂ → Outside 0 s₁ s₂ → s₁.unknowns = s₂.unknowns →
    Exec isa c s₁ t₁ u₁ → Exec isa c s₂ t₂ u₂ →
    (∀ r ∈ scratchRegs, r ∉ ps → r ∉ gs → u₁.gpr r = u₂.gpr r) ∧
    ∀ x, x ∉ xs → u₁.xmm x = u₂.xmm x ∧ u₁.ymmHi x = u₂.ymmHi x ∧ u₁.zmmHi x = u₂.zmmHi x

/-- What `c` leaves in the registers the clearing keeps, run by run: a run
from `s` that meets `k.pre`, with the trace `t`, leaves in each caller-saved
register `r` outside `ps` and `gs` the value `G t s r` if that is `some w`
(zero, or a public value), and the one it found if it is `none`; and so in
each vector register outside `xs`, its low 128 bits as `X` says and the
others as `Y` does. The trace tells the paths apart: code that clears the
vector registers at the end of the one path that uses them leaves `some 0`
after that path and `none` after the others. -/
def RegLeaves (c : Prog isa) (k : Contract isa) (xs : List XReg) (ps gs : List Reg)
    (G : List Leak → State → Reg → Option (BitVec 64)) (X : List Leak → State → XReg → Option (BitVec 128))
    (Y : List Leak → State → XReg → Option (BitVec 128 × BitVec 256)) : Prop :=
  ∀ s t u, k.pre s → Exec isa c s t u →
    (∀ r ∈ scratchRegs, r ∉ ps → r ∉ gs → u.gpr r = (G t s r).getD (s.gpr r)) ∧
    ∀ x, x ∉ xs → u.xmm x = (X t s x).getD (s.xmm x) ∧
      (u.ymmHi x, u.zmmHi x) = (Y t s x).getD (s.ymmHi x, s.zmmHi x)

/-- What `G`, `X` and `Y` say code leaves, along any one trace, depends only
on what two runs agree on (as `LeavesPub`). -/
def RegLeavesPub (k : Contract isa) (G : List Leak → State → Reg → Option (BitVec 64))
    (X : List Leak → State → XReg → Option (BitVec 128))
    (Y : List Leak → State → XReg → Option (BitVec 128 × BitVec 256)) : Prop :=
  ∀ t s₁ s₂, k.pre s₁ → k.pre s₂ → k.pub s₁ s₂ → Outside 0 s₁ s₂ → s₁.unknowns = s₂.unknowns →
    G t s₁ = G t s₂ ∧ X t s₁ = X t s₂ ∧ Y t s₁ = Y t s₂

theorem ne_rax_of_scratch : ∀ r ∈ scratchRegs, r ≠ Reg.rax := by decide

/-- Constant-time code whose registers each run leaves as `G`, `X` and `Y`
say (`RegLeaves`), which depend only on what two runs agree on
(`RegLeavesPub`), ends two runs agreeing on them (`RegsOk`): the two runs
have the same trace, and what it leaves as it found it was the same on entry
(`Outside 0`). -/
theorem regsOk_of_leaves {c : Prog isa} {k : Contract isa} {xs : List XReg} {ps gs : List Reg}
    {G : List Leak → State → Reg → Option (BitVec 64)} {X : List Leak → State → XReg → Option (BitVec 128)}
    {Y : List Leak → State → XReg → Option (BitVec 128 × BitVec 256)}
    (hct : ConstantTime isa k.pre k.pub c)
    (hl : RegLeaves c k xs ps gs G X Y) (hp : RegLeavesPub k G X Y) : RegsOk c k xs ps gs := by
  intro s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ hpu ho hu e₁ e₂
  obtain rfl := hct s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ hpu e₁ e₂
  obtain ⟨g₁, x₁⟩ := hl s₁ t₁ u₁ h₁ e₁
  obtain ⟨g₂, x₂⟩ := hl s₂ t₁ u₂ h₂ e₂
  obtain ⟨eG, eX, eY⟩ := hp t₁ s₁ s₂ h₁ h₂ hpu ho hu
  obtain ⟨-, -, hg, -, -, -, -, -, hxm, hy, hz, -⟩ := ho
  refine ⟨fun r hr hp' hg' => ?_, fun x hx => ?_⟩
  · rw [g₁ r hr hp' hg', g₂ r hr hp' hg', eG, hg r (ne_rax_of_scratch r hr)]
  · have a := (x₁ x hx).2
    rw [eY, hy, hz, ← (x₂ x hx).2] at a
    exact ⟨by rw [(x₁ x hx).1, (x₂ x hx).1, eX, hxm], congrArg Prod.fst a, congrArg Prod.snd a⟩

/-- The clearing of `xs`, `ps` and `gs`, and that of `xs'`, `ps` and `gs'`,
run along the same trace, to states that differ only in the registers. -/
theorem tail_part (v : VecLevel) (rb : Nat) {xs xs' : List XReg} {ps gs gs' : List Reg} {ks : List Nat}
    (cs : List Nat) {f : VecLevel} (ht : TailOk rb xs ps gs ks) (ht' : TailOk rb xs' ps gs' ks) (u : State)
    (hv : ∀ b ∈ cs, 0 < b ∧ b < 4096 ∧ b % 8 = 0) (hs : cs.sum ≤ (u.gpr .rsp).toNat)
    (hev : EvexOk f ks cs (u.gpr .rsp)) :
    ∃ m, Exec isa (scrubTail v rb xs ps gs ks cs f) u (tailTr v ks cs (u.gpr .rsp) f)
        (finState v rb xs ps gs m u f) ∧
      Exec isa (scrubTail v rb xs' ps gs' ks cs f) u (tailTr v ks cs (u.gpr .rsp) f)
        (finState v rb xs' ps gs' m u f) := by
  obtain ⟨m, e, hz, hu⟩ := tail_run v rb cs ht u hv hs hev
  obtain ⟨m', e', hz', hu'⟩ := tail_run v rb cs ht' u hv hs hev
  have hm : m' = m := by
    funext x
    by_cases hw : WCov ks cs (u.gpr .rsp) x
    · rw [hz x hw, hz' x hw]
    · rw [hu x hw, hu' x hw]
  rw [hm] at e'
  exact ⟨m, e, e'⟩

/-- Outside the caller-saved registers but `rax`, the two clearings leave the
same general-purpose registers. -/
theorem finState_gpr_out {v : VecLevel} {rb : Nat} {xs xs' : List XReg} {ps gs gs' : List Reg}
    {ks : List Nat} {m : Mem} {u : State} {f : VecLevel}
    (ht : TailOk rb xs ps gs ks) (ht' : TailOk rb xs' ps gs' ks) {r : Reg} (hr : r ∉ scratchRegs) :
    (finState v rb xs ps gs m u f).gpr r = (finState v rb xs' ps gs' m u f).gpr r := by
  have hg : r ∉ gs := fun h => hr (ht.gsOk r h)
  have hg' : r ∉ gs' := fun h => hr (ht'.gsOk r h)
  have hp : r ∉ ps := fun h => hr (ht.psOk r h)
  by_cases h : r = .rax
  · subst h; rw [finState_rax hg, finState_rax hg']
  · rw [finState_gpr hp hg h, finState_gpr hp hg' h]

/-- A postcondition that `Sig.contract` derives reads, of the state on
return, only its memory and `rax`. -/
theorem contract_post_congr {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))} {s u u' : State}
    (h : (sig.contract A pre post wa stack leak).post s u) (hm : u'.mem = u.mem)
    (hr : u'.gpr .rax = u.gpr .rax) : (sig.contract A pre post wa stack leak).post s u' := by
  have e1 : A.mem u' = A.mem u := by rw [hA.mem, hA.mem, hm]
  have e2 : A.ret u' = A.ret u := by rw [hA.ret, hA.ret, hr]
  simp only [Sig.contract] at h ⊢
  rw [e1, e2]
  exact h

section
variable {A : Abi isa} {sig : Sig} {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
  {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
  {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}

/-- Code verified against a contract that `Sig.contract` derives, followed
by the clearing of the registers `xs`, `ps` and `gs`: verified against the
same contract and without secret residue, if it is with the registers `xs'`
and `gs'` cleared instead (`hall`, as `Verified.scrubM` gives it with those
the code's instructions may write, `xsOf` and `gsOf`), and two runs end
agreeing on the registers the clearing keeps (`hregs`). -/
theorem Verified.scrubPart {c : Prog isa} {v f : VecLevel} {rb : Nat} {xs xs' : List XReg}
    {ps gs gs' : List Reg} {ks cs : List Nat} (hA : ScrubAbi A)
    (h : Verified target c (sig.contract A pre post wa stack leak))
    (hcs : cs.sum = stack) (hv : ∀ b ∈ cs, 0 < b ∧ b < 4096 ∧ b % 8 = 0)
    (hev : ∀ p : Addr, cs.sum ≤ p.toNat → EvexOk f ks cs p)
    (ht : TailOk rb xs ps gs ks) (ht' : TailOk rb xs' ps gs' ks)
    (hregs : RegsOk c (sig.contract A pre post wa stack leak) xs ps gs)
    (hall : Verified target (Impl.Scrub.X86_64.scrub v rb xs' ps gs' ks cs c f) (sig.contract A pre post wa stack leak) ∧
      NoResidue (Impl.Scrub.X86_64.scrub v rb xs' ps gs' ks cs c f) (sig.contract A pre post wa stack leak) rb) :
    Verified target (Impl.Scrub.X86_64.scrub v rb xs ps gs ks cs c f) (sig.contract A pre post wa stack leak) ∧
      NoResidue (Impl.Scrub.X86_64.scrub v rb xs ps gs ks cs c f) (sig.contract A pre post wa stack leak) rb := by
  obtain ⟨⟨acor, act, asat⟩, ares⟩ := hall
  -- Both clearings, after a run of `c`.
  have tails : ∀ s t u, (sig.contract A pre post wa stack leak).pre s → Exec isa c s t u →
      ∃ m T, Exec isa (scrubTail v rb xs ps gs ks cs f) u T (finState v rb xs ps gs m u f) ∧
        Exec isa (scrubTail v rb xs' ps gs' ks cs f) u T (finState v rb xs' ps gs' m u f) := by
    intro s t u hs he
    obtain ⟨t', u', he', ha, -⟩ := h.1 s hs
    obtain ⟨-, rfl⟩ := Exec.det he he'
    have hr : u.gpr .rsp = s.gpr .rsp := ha.1 .rsp (by decide)
    have hl : cs.sum ≤ (u.gpr .rsp).toNat := by
      rcases (contract_pre_scrub hA hs).1 with h0 | h0
      · rw [hcs, h0]; exact Nat.zero_le _
      · rw [hcs, hr]; exact h0
    obtain ⟨m, e, e'⟩ := tail_part v rb cs ht ht' u hv hl (hev _ hl)
    exact ⟨m, _, e, e'⟩
  have hax : Reg.rax ∉ scratchRegs := by decide
  refine ⟨⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, asat⟩,
    fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp ho hun e₁ e₂ => ?_⟩
  · -- Correctness.
    obtain ⟨t, w, he, ha, hq⟩ := acor s hs
    cases he with | seq a b =>
    obtain ⟨m, T, e, e'⟩ := tails s _ _ hs a
    obtain ⟨-, rfl⟩ := Exec.det b e'
    obtain ⟨hcs', hrs, hmx⟩ := ha
    refine ⟨_, _, .seq a e, ⟨fun r hr => ?_, ?_, ?_⟩, contract_post_congr hA hq ?_ (finState_gpr_out ht ht' hax)⟩
    · have hs' : r ∉ scratchRegs := by revert hr; revert r; decide
      rw [finState_gpr_out ht ht' hs']; exact hcs' r hr
    · simpa only [finState_other] using hrs
    · simpa only [finState_other] using hmx
    · simp only [finState_other]
  · -- Constant time: the same trace as the other clearing's.
    cases e₁ with | seq a₁ b₁ =>
    cases e₂ with | seq a₂ b₂ =>
    obtain ⟨m₁, T₁, f₁, f₁'⟩ := tails s₁ _ _ h₁ a₁
    obtain ⟨m₂, T₂, f₂, f₂'⟩ := tails s₂ _ _ h₂ a₂
    obtain ⟨rfl, -⟩ := Exec.det b₁ f₁
    obtain ⟨rfl, -⟩ := Exec.det b₂ f₂
    exact act _ _ _ _ _ _ h₁ h₂ hp (.seq a₁ f₁') (.seq a₂ f₂')
  · -- No residue: the other clearing's, but for the registers this one keeps.
    cases e₁ with | seq a₁ b₁ =>
    cases e₂ with | seq a₂ b₂ =>
    rename_i u₁ _ _ u₂ _ _
    obtain ⟨m₁, T₁, f₁, f₁'⟩ := tails s₁ _ _ h₁ a₁
    obtain ⟨m₂, T₂, f₂, f₂'⟩ := tails s₂ _ _ h₂ a₂
    obtain ⟨-, rfl⟩ := Exec.det b₁ f₁
    obtain ⟨-, rfl⟩ := Exec.det b₂ f₂
    obtain ⟨o1, o2, o3, o4, -, -, -, -, -, o10, o11, o12, o13, o14, o15⟩ :=
      ares _ _ _ _ _ _ h₁ h₂ hp ho hun (.seq a₁ f₁') (.seq a₂ f₂')
    obtain ⟨rg, rx⟩ := hregs _ _ _ _ _ _ h₁ h₂ hp ho hun a₁ a₂
    refine ⟨by simpa only [finState_other] using o1, by simpa only [finState_other] using o2,
      fun r hr => ?_, ?_, by simp only [finState_other], by simp only [finState_other],
      by simp only [finState_other], by simp only [finState_other], ?_, ?_, ?_,
      by simpa only [finState_other] using o12, by simpa only [finState_other] using o13,
      by simpa only [finState_other] using o14, fun x hx => ?_⟩
    · by_cases hs : r ∈ scratchRegs
      · by_cases hg : r ∈ gs
        · simp [finState, clearedG, hg]
        · by_cases hp' : r ∈ ps
          · simp [finState, clearedG, State.setReg, clearedP_gpr, hg, hp', hr]
          · rw [finState_gpr hp' hg hr, finState_gpr hp' hg hr]; exact rg r hs hp' hg
      · rw [finState_gpr_out ht ht' hs, finState_gpr_out ht ht' hs]; exact o3 r hr
    · rw [finState_gpr_out ht ht' hax, finState_gpr_out ht ht' hax]; exact o4
    · rw [finState_xmm, finState_xmm]
      funext x
      split
      · rfl
      · rename_i hx; exact (rx x hx).1
    · rw [finState_ymmHi, finState_ymmHi]
      funext x
      split
      · rfl
      · rename_i hn
        by_cases hx : x ∈ xs
        · have hs : v = .sse := Classical.byContradiction fun h => hn ⟨h, hx⟩
          subst hs
          rw [finState_ymmHi, finState_ymmHi] at o10
          simpa using congrFun o10 x
        · exact (rx x hx).2.1
    · rw [finState_zmmHi, finState_zmmHi]
      funext x
      split
      · rfl
      · rename_i hn
        by_cases hx : x ∈ xs
        · have hs : v = .sse := Classical.byContradiction fun h => hn ⟨h, hx⟩
          subst hs
          rw [finState_zmmHi, finState_zmmHi] at o11
          simpa using congrFun o11 x
        · exact (rx x hx).2.2
    · have := o15 x (by simpa only [finState_other] using hx)
      simpa only [finState_other] using this

end

/-! ## Registrations -/

/-- What `scrub` needs of the registers it is given to clear, as a check:
`xmm0` if the stack is wiped (from it), and some of the caller-saved
registers but `rax`. -/
def tailOkB (xs : List XReg) (gs : List Reg) (ks : List Nat) : Bool :=
  (ks.isEmpty || xs.contains .xmm0) && gs.all (scratchRegs.contains ·) && !gs.isEmpty

theorem tailOk_ofB (rb : Nat) {xs : List XReg} {gs : List Reg} {ks : List Nat} (h : tailOkB xs gs ks = true) :
    TailOk rb xs (psOf ks) gs ks := by
  simp only [tailOkB, Bool.and_eq_true, Bool.or_eq_true, List.isEmpty_iff, List.contains_iff_mem,
    List.all_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
  obtain ⟨⟨hx, hg⟩, hne⟩ := h
  refine ⟨fun hk => ?_, fun hk => by simp [psOf, hk], fun r hr => ?_, fun r hr => by simpa using hg r hr, hne⟩
  · rcases hx with h | h
    · exact absurd h hk
    · exact h
  · unfold psOf at hr; split at hr <;> simp_all [scratchRegs]

/-- `scrubCodeMC_noResidue`, with the registers `xs` and `gs` cleared,
those two runs may not agree on (`RegsOk`): verified, and without secret
residue. -/
theorem scrubCodeMCR_ok {api : Api} (r : Registration api target) (v : VecLevel) (ks cs : List Nat)
    (xs : List XReg) (gs : List Reg)
    (hcs : cs.sum = r.stack) (hcv : ∀ b ∈ cs, 0 < b ∧ b < 4096 ∧ b % 8 = 0)
    (hd : r.code.x86_64Depth ≤ r.stack) (hst : r.stack + 8 < 2 ^ 64)
    (hlv : r.code.all (fun i => decide (i.vecLevelR ≤ v.level)) = true)
    (hmx : (mxClass r.code).isSome = true)
    (hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨ api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (hres : ResOk r.code r.contract r.stack ks cs) (hw : r.written = []) (hne : v ≠ .evex)
    (ht : TailOk (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits) xs (psOf ks) gs ks)
    (hregs : RegsOk r.code r.contract xs (psOf ks) gs) :
    Verified target (scrub v (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
        xs (psOf ks) gs ks cs r.code) r.contract ∧
      NoResidue (scrub v (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
        xs (psOf ks) gs ks cs r.code) r.contract
        (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits) := by
  have hall : Verified target (scrub v (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
        (xsOf r.code ks) (psOf ks) (gsOf Taint.clobbers r.code) ks cs r.code) r.contract ∧
      NoResidue (scrub v (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
        (xsOf r.code ks) (psOf ks) (gsOf Taint.clobbers r.code) ks cs r.code) r.contract
        (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits) :=
    ⟨(scrubRegMC r v ks cs hcs hcv hd hst hlv hmx hrb hpost hres hw hne).verified,
      scrubCodeMC_noResidue r v ks cs hcs hcv hd hst hlv hmx hrb hpost hres hne⟩
  obtain ⟨pre, post, leak, e⟩ := r.ofSig
  have hv := r.verified
  rw [e] at hv hall hregs ⊢
  exact Verified.scrubPart (ScrubAbi.of r.consts api.sig r.tables api.pubMode) hv hcs hcv
    (fun _ _ h => absurd h hne) ht (tailOk_of _ _ _) hregs hall

/-- `scrubRegMC`, with the registers `xs` and `gs` cleared (`scrubCodeMCR_ok`). -/
def scrubRegMCR {api : Api} (r : Registration api target) (v : VecLevel) (ks cs : List Nat)
    (xs : List XReg) (gs : List Reg)
    (hcs : cs.sum = r.stack) (hcv : ∀ b ∈ cs, 0 < b ∧ b < 4096 ∧ b % 8 = 0)
    (hd : r.code.x86_64Depth ≤ r.stack) (hst : r.stack + 8 < 2 ^ 64)
    (hlv : r.code.all (fun i => decide (i.vecLevelR ≤ v.level)) = true)
    (hmx : (mxClass r.code).isSome = true)
    (hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨ api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (hres : ResOk r.code r.contract r.stack ks cs) (hw : r.written = []) (hne : v ≠ .evex)
    (ht : TailOk (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits) xs (psOf ks) gs ks)
    (hregs : RegsOk r.code r.contract xs (psOf ks) gs) : Registration api target where
  suffix := r.suffix
  consts := r.consts
  tables := r.tables
  stack := r.stack
  code := scrub v (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
    xs (psOf ks) gs ks cs r.code
  contract := r.contract
  verified := (scrubCodeMCR_ok r v ks cs xs gs hcs hcv hd hst hlv hmx hrb hpost hres hw hne ht hregs).1
  ofApi := r.ofApi
  ofSig := r.ofSig
  spSafe := scrub_spSafe v _ _ _ _ _ _ ht.psOk ht.gsOk r.spSafe
  written := r.written
  writtenOk := by
    rw [hw]; exact fun _ _ _ _ _ => True.intro
  extra := r.extra
  vendor := r.vendor
  notWith := r.notWith
  residue := some ⟨(scrubCodeMCR_ok r v ks cs xs gs hcs hcv hd hst hlv hmx hrb hpost hres hw hne ht hregs).2⟩

end VG.X86_64.Scrub

namespace VG.X86_64.RScrub

open VG.X86_64 VG.X86_64.Scrub VG.Impl.Scrub.X86_64

/-- `withScrubResC`, clearing only the SSE registers `xs` and the
caller-saved registers `gs` (and `r11` if the stack is wiped, and the upper
bits of `rax`), those two runs may not agree on at the end (`hregs`): for
code that clears the registers it leaves secrets in on its own paths.
`r` itself where a side condition fails. -/
def withScrubResCR {api : Api} (r : Registration api target)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (ks cs : List Nat) (hres : ResOk r.code r.contract r.stack ks cs)
    (xs : List XReg) (gs : List Reg) (hregs : RegsOk r.code r.contract xs (psOf ks) gs) : Registration api target :=
  let v := levelFor r.code
  if hcs : cs.sum = r.stack then
  if hcv : cs.all (fun b => decide (0 < b ∧ b < 4096 ∧ b % 8 = 0)) = true then
  if hd : r.code.x86_64Depth ≤ r.stack then
  if hst : r.stack + 8 < 2 ^ 64 then
  if hlv : r.code.allOnce (fun i => decide (i.vecLevelR ≤ v.level)) = true then
  if hmx : (mxClassOnce r.code).isSome = true then
  if hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨
      api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64 then
  if hw : r.written = [] then
  if ht : tailOkB xs gs ks = true then
    scrubRegMCR r v ks cs xs gs hcs (fun b hb => of_decide_eq_true (List.all_eq_true.mp hcv b hb)) hd hst
      ((Code.allOnce_eq _ r.code).symm.trans hlv) (mxClassOnce_eq r.code ▸ hmx) hrb hpost hres hw (levelFor_ne _)
      (tailOk_ofB _ ht) hregs
  else r else r else r else r else r else r else r else r else r

end VG.X86_64.RScrub
