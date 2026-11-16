module

public import VerifiedGarbage.Proof.Framework.X86_64.ScrubChunks
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubPaths
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.X86_64.UpperLock
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.X86_64.CallInline
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.ResidueKeep

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

Code that clears what it leaves need not wipe the stack either, but for
the return addresses its calls leave below the stack pointer: which of the
state's `unknowns` each is depends on the path, and on how many calls the
functions it calls make. Two runs that agree on them on entry, along the
same trace, leave the same ones (`StackLock.lock`): their traces split
alike (`UpperLock.lock`), so their calls are the same calls, from the same
stack pointer, and push the same unknowns. So, too, with the vector
registers of code that clears them after the calls that use them
(`VecLock.step`, `VecLock.lock`, `regsOk_of_vec`): what they hold after
each piece of the code is either what they held before it or zero, as the
path says.

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

/-- `RegsOk` from its two halves: the general-purpose registers (as the
residue analysis may give them, `gprsOk_of_check`) and the vector ones (as
`RegLeaves` may, with `G` empty). -/
theorem regsOk_of_parts {c : Prog isa} {k : Contract isa} {xs : List XReg} {ps gs : List Reg}
    (hg : RegsOk c k xregs ps gs) (hx : RegsOk c k xs scratchRegs scratchRegs) : RegsOk c k xs ps gs :=
  fun s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ hp ho hu e₁ e₂ =>
    ⟨(hg s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ hp ho hu e₁ e₂).1, (hx s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ hp ho hu e₁ e₂).2⟩

/-- Whether the residue analysis's last taint knows public every
caller-saved register outside `ps` and `gs`. -/
def gprsPubB (τ : RTaint.FT) (ps gs : List Reg) : Bool :=
  τ.ok && scratchRegs.all fun r => ps.contains r || gs.contains r || τ.t.regs.mem r

/-- The residue analysis of the code, from `RScrub.init`, ending with every
caller-saved register outside `ps` and `gs` public, proves those the same
at the end of two runs (the general-purpose half of `RegsOk`). -/
theorem gprsOk_of_check {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))} {c : Prog isa} {ps gs : List Reg}
    {pubs : List (Nat × Nat × Nat)} {h : VG.Taint.Hint RTaint.FT}
    (hfit : RScrub.pubsFit sig pubs = true) (hpub : RScrub.PubOk (sig.contract A pre post wa stack leak) pubs)
    (hc : (VG.Taint.check RTaint.rtaint (RScrub.init sig stack pubs) c h).any (gprsPubB · ps gs) = true) :
    RegsOk c (sig.contract A pre post wa stack leak) xregs ps gs := by
  obtain ⟨τf, hτ, hb⟩ : ∃ τf, VG.Taint.check RTaint.rtaint (RScrub.init sig stack pubs) c h = some τf ∧
      gprsPubB τf ps gs = true := by
    cases h' : VG.Taint.check RTaint.rtaint (RScrub.init sig stack pubs) c h with
    | none => rw [h'] at hc; cases hc
    | some τf => rw [h'] at hc; exact ⟨τf, rfl, hc⟩
  simp only [gprsPubB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, List.contains_iff_mem] at hb
  obtain ⟨hok, hall⟩ := hb
  intro s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ hp ho hu e₁ e₂
  obtain ⟨-, ha⟩ := VG.Taint.check_sound (A := RTaint.rtaint) hτ (RScrub.init_agree hA hfit hpub h₁ h₂ ho hp hu) e₁ e₂
  refine ⟨fun r hr hp' hg' => ?_, fun x hx => absurd (mem_xregs x) hx⟩
  rcases hall r hr with (h | h) | h
  · exact absurd h hp'
  · exact absurd h hg'
  · exact (ha hok).base.rf.1 r h

theorem cov_nil : ∀ (cs : List Nat) (i : Nat), cov [] cs i = false
  | [], _ => rfl
  | b :: bs, i => by
    simp only [cov]
    split
    · exact cov_nil bs i
    · simp [covC]

/-- The wipes of the chunks `cs` and `cs'` zero the same bytes if they are
the same chunks or wipe no granule. -/
def SameWipe (ks cs cs' : List Nat) : Prop := cs = cs' ∨ ks = []

theorem wcov_same {ks cs cs' : List Nat} (h : SameWipe ks cs cs') (p x : Addr) :
    WCov ks cs p x ↔ WCov ks cs' p x := by
  rcases h with rfl | rfl
  · exact Iff.rfl
  · simp [WCov, cov_nil]

/-- The clearing of `xs`, `ps` and `gs` with the stack wiped in the chunks
`cs`, and that of `xs'`, `ps` and `gs'` in the chunks `cs'`, which wipe the
same bytes (`SameWipe`): states that differ only in the registers. -/
theorem tail_part (v : VecLevel) (rb : Nat) {xs xs' : List XReg} {ps gs gs' : List Reg} {ks : List Nat}
    {cs cs' : List Nat} {f : VecLevel} (ht : TailOk rb xs ps gs ks) (ht' : TailOk rb xs' ps gs' ks)
    (hcc : SameWipe ks cs cs') (u : State)
    (hv : ∀ b ∈ cs, 0 < b ∧ b < 4096 ∧ b % 8 = 0) (hs : cs.sum ≤ (u.gpr .rsp).toNat)
    (hev : EvexOk f ks cs (u.gpr .rsp))
    (hv' : ∀ b ∈ cs', 0 < b ∧ b < 4096 ∧ b % 8 = 0) (hs' : cs'.sum ≤ (u.gpr .rsp).toNat)
    (hev' : EvexOk f ks cs' (u.gpr .rsp)) :
    ∃ m T', Exec isa (scrubTail v rb xs ps gs ks cs f) u (tailTr v ks cs (u.gpr .rsp) f)
        (finState v rb xs ps gs m u f) ∧
      Exec isa (scrubTail v rb xs' ps gs' ks cs' f) u T' (finState v rb xs' ps gs' m u f) := by
  obtain ⟨m, e, hz, hu⟩ := tail_run v rb cs ht u hv hs hev
  obtain ⟨m', e', hz', hu'⟩ := tail_run v rb cs' ht' u hv' hs' hev'
  have hm : m' = m := by
    funext x
    by_cases hw : WCov ks cs (u.gpr .rsp) x
    · rw [hz x hw, hz' x ((wcov_same hcc _ _).mp hw)]
    · rw [hu x hw, hu' x (fun h => hw ((wcov_same hcc _ _).mpr h))]
  rw [hm] at e'
  exact ⟨m, _, e, e'⟩

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
by the clearing of the registers `xs`, `ps` and `gs` and the stack wiped in
the chunks `cs`: verified against the same contract and without secret
residue, if it is with the registers `xs'` and `gs'` cleared instead and the
chunks `cs'`, which wipe the same bytes (`hall`, as `Verified.scrubM` gives
it with the registers the code's instructions may write, `xsOf` and `gsOf`),
and two runs end agreeing on the registers the clearing keeps (`hregs`).
With no granule wiped, `cs` may be `[]`: no frame at all. -/
theorem Verified.scrubPart {c : Prog isa} {v f : VecLevel} {rb : Nat} {xs xs' : List XReg}
    {ps gs gs' : List Reg} {ks cs cs' : List Nat} (hA : ScrubAbi A)
    (h : Verified target c (sig.contract A pre post wa stack leak))
    (hcs : cs.sum ≤ stack) (hv : ∀ b ∈ cs, 0 < b ∧ b < 4096 ∧ b % 8 = 0)
    (hev : ∀ p : Addr, cs.sum ≤ p.toNat → EvexOk f ks cs p)
    (hcs' : cs'.sum ≤ stack) (hv' : ∀ b ∈ cs', 0 < b ∧ b < 4096 ∧ b % 8 = 0)
    (hev' : ∀ p : Addr, cs'.sum ≤ p.toNat → EvexOk f ks cs' p) (hcc : SameWipe ks cs cs')
    (ht : TailOk rb xs ps gs ks) (ht' : TailOk rb xs' ps gs' ks)
    (hregs : RegsOk c (sig.contract A pre post wa stack leak) xs ps gs)
    (hall : Verified target (Impl.Scrub.X86_64.scrub v rb xs' ps gs' ks cs' c f) (sig.contract A pre post wa stack leak) ∧
      NoResidue (Impl.Scrub.X86_64.scrub v rb xs' ps gs' ks cs' c f) (sig.contract A pre post wa stack leak) rb) :
    Verified target (Impl.Scrub.X86_64.scrub v rb xs ps gs ks cs c f) (sig.contract A pre post wa stack leak) ∧
      NoResidue (Impl.Scrub.X86_64.scrub v rb xs ps gs ks cs c f) (sig.contract A pre post wa stack leak) rb := by
  obtain ⟨⟨acor, -, asat⟩, ares⟩ := hall
  -- Both clearings, after a run of `c`.
  have tails : ∀ s t u, (sig.contract A pre post wa stack leak).pre s → Exec isa c s t u →
      ∃ m T', Exec isa (scrubTail v rb xs ps gs ks cs f) u (tailTr v ks cs (s.gpr .rsp) f)
          (finState v rb xs ps gs m u f) ∧
        Exec isa (scrubTail v rb xs' ps gs' ks cs' f) u T' (finState v rb xs' ps gs' m u f) := by
    intro s t u hs he
    obtain ⟨t', u', he', ha, -⟩ := h.1 s hs
    obtain ⟨-, rfl⟩ := Exec.det he he'
    have hr : u.gpr .rsp = s.gpr .rsp := ha.1 .rsp (by decide)
    have hl : ∀ {n : Nat}, n ≤ stack → n ≤ (u.gpr .rsp).toNat := fun {n} hn => by
      rcases (contract_pre_scrub hA hs).1 with h0 | h0
      · rw [h0] at hn; omega_using [hn]
      · rw [hr]; omega_using [hn, h0]
    obtain ⟨m, T', e, e'⟩ := tail_part v rb ht ht' hcc u hv (hl hcs) (hev _ (hl hcs)) hv' (hl hcs')
      (hev' _ (hl hcs'))
    rw [hr] at e
    exact ⟨m, T', e, e'⟩
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
  · -- Constant time: the code's, then a trace of the stack pointer.
    cases e₁ with | seq a₁ b₁ =>
    cases e₂ with | seq a₂ b₂ =>
    obtain ⟨m₁, T₁, f₁, -⟩ := tails s₁ _ _ h₁ a₁
    obtain ⟨m₂, T₂, f₂, -⟩ := tails s₂ _ _ h₂ a₂
    obtain ⟨rfl, -⟩ := Exec.det b₁ f₁
    obtain ⟨rfl, -⟩ := Exec.det b₂ f₂
    rw [h.2.1 _ _ _ _ _ _ h₁ h₂ hp a₁ a₂, contract_pub_rsp hA hp]
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

/-- The chunks the clearing wipes the stack in: none if it wipes no granule
(no frame, no instruction), else `cs`. -/
def wipeCs (ks cs : List Nat) : List Nat := if ks = [] then [] else cs

theorem wipeCs_same (ks cs : List Nat) : SameWipe ks (wipeCs ks cs) cs := by
  unfold wipeCs SameWipe; split
  · exact .inr ‹_›
  · exact .inl rfl

theorem wipeCs_sum (ks cs : List Nat) : (wipeCs ks cs).sum ≤ cs.sum := by
  unfold wipeCs; split
  · exact Nat.zero_le _
  · exact Nat.le_refl _

theorem wipeCs_valid {ks cs : List Nat} (h : ∀ b ∈ cs, 0 < b ∧ b < 4096 ∧ b % 8 = 0) :
    ∀ b ∈ wipeCs ks cs, 0 < b ∧ b < 4096 ∧ b % 8 = 0 := by
  unfold wipeCs; split
  · exact fun _ h => nomatch h
  · exact h

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
        xs (psOf ks) gs ks (wipeCs ks cs) r.code) r.contract ∧
      NoResidue (scrub v (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
        xs (psOf ks) gs ks (wipeCs ks cs) r.code) r.contract
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
  exact Verified.scrubPart (ScrubAbi.of r.consts api.sig r.tables api.pubMode) hv
    (by rw [← hcs]; exact wipeCs_sum ks cs) (wipeCs_valid hcv) (fun _ _ h => absurd h hne)
    (Nat.le_of_eq hcs) hcv (fun _ _ h => absurd h hne) (wipeCs_same ks cs) ht (tailOk_of _ _ _) hregs hall

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
    xs (psOf ks) gs ks (wipeCs ks cs) r.code
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

/-! ## Return addresses, in two runs along the same path -/

namespace VG.X86_64.StackLock

open VG VG.X86_64 VG.X86_64.UpperLock

/-- Two states agree on the stack pointer, on the return addresses calls
will push (`State.unknowns`), and on the bytes `S`, which neither may
write. -/
structure Same (S : Addr → Prop) (s₁ s₂ : State) : Prop where
  rsp : s₁.gpr .rsp = s₂.gpr .rsp
  unk : s₁.unknowns = s₂.unknowns
  out₁ : ∀ x, S x → ∀ r ∈ s₁.wr, ¬ r.Contains x 1
  out₂ : ∀ x, S x → ∀ r ∈ s₂.wr, ¬ r.Contains x 1
  mem : ∀ x, S x → s₁.mem x = s₂.mem x

theorem writeW_congr {m₁ m₂ : Mem} {x : Addr} (h : m₁ x = m₂ x) (a : Addr) {w : Nat} (v : BitVec w) :
    m₁.writeW a v x = m₂.writeW a v x := by
  simp only [Mem.writeW, Mem.write]; split
  · rfl
  · exact h

theorem block_same {S : Addr → Prop} {is : List Instr} {s₁ s₂ u₁ u₂ : State} {t₁ t₂ : List Leak}
    (hb : ∀ i ∈ is, Taint.clobbers i .rsp = false) (e₁ : execBlock isa is s₁ = some (u₁, t₁))
    (e₂ : execBlock isa is s₂ = some (u₂, t₂)) (h : Same S s₁ s₂) : Same S u₁ u₂ := by
  obtain ⟨-, w₁, f₁⟩ := execBlock_regions e₁
  obtain ⟨-, w₂, f₂⟩ := execBlock_regions e₂
  have k₁ := execBlock_keep (M := isa) (fun s : State => s.unknowns) (ok := fun _ => True)
    (fun _ he => RTaint.exec_unknowns he) (fun _ _ => trivial) e₁
  have k₂ := execBlock_keep (M := isa) (fun s : State => s.unknowns) (ok := fun _ => True)
    (fun _ he => RTaint.exec_unknowns he) (fun _ _ => trivial) e₂
  refine ⟨by rw [execBlock_gpr hb e₁, execBlock_gpr hb e₂, h.rsp], by rw [k₁, k₂, h.unk],
    fun x hx => w₁ ▸ h.out₁ x hx, fun x hx => w₂ ▸ h.out₂ x hx, fun x hx => ?_⟩
  rw [f₁ x (h.out₁ x hx), f₂ x (h.out₂ x hx), h.mem x hx]

/-- A call, from states that agree: the same return address, at the same
place. -/
theorem call_same {S : Addr → Prop} {s₁ s₂ u₁ u₂ : State} (c₁ : isa.call s₁ = some u₁)
    (c₂ : isa.call s₂ = some u₂) (h : Same S s₁ s₂) : Same S u₁ u₂ := by
  simp only [isa, call, Option.some.injEq] at c₁ c₂
  subst c₁ c₂
  exact ⟨by simp only [RegUpd.gpr_setReg_self, h.rsp], by rw [h.unk], h.out₁, h.out₂,
    fun x hx => by rw [h.rsp, h.unk]; exact writeW_congr (h.mem x hx) _ _⟩

/-- A return, to states that agree. -/
theorem ret_same {S : Addr → Prop} {a₁ a₂ s₁ s₂ u₁ u₂ : State} (r₁ : isa.ret a₁ s₁ = some u₁)
    (r₂ : isa.ret a₂ s₂ = some u₂) (h : Same S s₁ s₂) : Same S u₁ u₂ := by
  simp only [isa, ret] at r₁ r₂
  split at r₁ <;> cases r₁
  split at r₂ <;> cases r₂
  exact ⟨by simp only [RegUpd.gpr_setReg_self, h.rsp], h.unk, h.out₁, h.out₂, h.mem⟩

theorem nosp_frame {i j : Instr} {b : Prog isa} {s s₁ : State} (hc : NoSp (.frame i b j))
    (hp : isa.push i s = some s₁) : False := by
  have hi := hc i (List.mem_cons_self ..)
  cases i <;> simp only [isa, push, reduceCtorEq] at hp
  all_goals simp [Taint.clobbers] at hi

/-- Two runs of code that never writes `rsp` (`NoSp`, so with no frame),
whose traces agree, extended by `r₁` and `r₂`, from states whose functions
called indirectly are at the same addresses and that agree on the stack
pointer, the unknowns and the bytes `S` they may not write (`Same`), end
agreeing on them: they take the same path (`UpperLock.lock`), so make the
same calls, each from the same stack pointer, with the same unknown as its
return address. -/
theorem lock {S : Addr → Prop} {c : Prog isa} {s₁ s₁' : State} {t₁ : List Leak} (e₁ : Exec isa c s₁ t₁ s₁') :
    NoSp c → ∀ {s₂ s₂' : State} {t₂ r₁ r₂ : List Leak}, Exec isa c s₂ t₂ s₂' → t₁ ++ r₁ = t₂ ++ r₂ →
      (∀ n ∈ inames c, s₁.syms n = s₂.syms n) → Same S s₁ s₂ → Same S s₁' s₂' := by
  induction e₁ with
  | block h₁ =>
    intro hc s₂ s₂' t₂ r₁ r₂ e₂ _ _ hs
    cases e₂ with
    | block h₂ => exact block_same hc h₁ h₂ hs
  | seq x₁ y₁ ihx ihy =>
    intro hc s₂ s₂' t₂ r₁ r₂ e₂ ht hf hs
    cases e₂ with
    | seq x₂ y₂ =>
      have hca : NoSp _ := fun i hi => hc i (List.mem_append_left _ hi)
      have hcb : NoSp _ := fun i hi => hc i (List.mem_append_right _ hi)
      simp only [List.append_assoc] at ht
      simp only [inames, List.mem_append] at hf
      obtain ⟨hx, -⟩ := UpperLock.lock x₁ x₂ ht fun n hn => hf n (.inl hn)
      subst hx
      exact ihy hcb y₂ (List.append_cancel_left ht) (fun n hn => by
        rw [Exec.syms x₁, Exec.syms x₂]; exact hf n (.inr hn)) (ihx hca x₂ ht (fun n hn => hf n (.inl hn)) hs)
  | iteT _ x₁ ih =>
    intro hc s₂ s₂' t₂ r₁ r₂ e₂ ht hf hs
    cases e₂ with
    | iteT _ x₂ =>
      simp only [List.cons_append, List.cons.injEq, true_and] at ht
      simp only [inames, List.mem_append] at hf
      exact ih (fun i hi => hc i (List.mem_append_left _ hi)) x₂ ht (fun n hn => hf n (.inl hn)) hs
    | iteF _ _ => exact (branch_ne ht).elim
  | iteF _ x₁ ih =>
    intro hc s₂ s₂' t₂ r₁ r₂ e₂ ht hf hs
    cases e₂ with
    | iteF _ x₂ =>
      simp only [List.cons_append, List.cons.injEq, true_and] at ht
      simp only [inames, List.mem_append] at hf
      exact ih (fun i hi => hc i (List.mem_append_right _ hi)) x₂ ht (fun n hn => hf n (.inr hn)) hs
    | iteT _ _ => exact (branch_ne ht.symm).elim
  | loopExit x₁ _ ih =>
    intro hc s₂ s₂' t₂ r₁ r₂ e₂ ht hf hs
    cases e₂ with
    | loopExit x₂ _ =>
      simp only [List.append_assoc] at ht
      exact ih hc x₂ ht hf hs
    | loopNext x₂ _ _ =>
      simp only [List.append_assoc] at ht
      obtain ⟨h, -⟩ := UpperLock.lock x₁ x₂ ht hf
      subst h
      simp at ht
  | loopNext x₁ _ _ ihx ihl =>
    intro hc s₂ s₂' t₂ r₁ r₂ e₂ ht hf hs
    cases e₂ with
    | loopExit x₂ _ =>
      simp only [List.append_assoc] at ht
      obtain ⟨h, -⟩ := UpperLock.lock x₁ x₂ ht hf
      subst h
      simp at ht
    | loopNext x₂ _ l₂ =>
      simp only [List.append_assoc] at ht
      obtain ⟨h, -⟩ := UpperLock.lock x₁ x₂ ht hf
      subst h
      have ht' := List.append_cancel_left ht
      simp only [List.cons_append, List.cons.injEq, true_and] at ht'
      exact ihl hc l₂ ht' (fun n hn => by rw [Exec.syms x₁, Exec.syms x₂]; exact hf n hn) (ihx hc x₂ ht hf hs)
  | call hc₁ x₁ hr₁ ih =>
    intro hc s₂ s₂' t₂ r₁ r₂ e₂ ht hf hs
    cases e₂ with
    | call hc₂ x₂ hr₂ =>
      simp only [List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.cons.injEq] at ht
      exact ret_same hr₁ hr₂ (ih hc x₂ ht.2 (fun n hn => by rw [call_syms hc₁, call_syms hc₂]; exact hf n hn)
        (call_same hc₁ hc₂ hs))
  | frame hp₁ => exact fun hc => (nosp_frame hc hp₁).elim
  | icall hi₁ hc₁ x₁ hr₁ ih =>
    intro hc s₂ s₂' t₂ r₁ r₂ e₂ ht hf hs
    have hn := hf _ (List.mem_cons_self ..)
    have hcb : NoSp _ := fun i hi => hc i (List.mem_cons_of_mem _ (List.mem_append_left _ hi))
    cases e₂ with
    | icall hi₂ hc₂ x₂ hr₂ =>
      simp only [List.append_assoc, List.cons_append] at ht
      obtain ⟨-, ht⟩ := append_cancel (by simp only [List.length_map]; exact addrs_length _ _ _) ht
      simp only [List.map_cons, List.map_nil, List.cons_append, List.cons.injEq] at ht
      exact ret_same hr₁ hr₂ (ih hcb x₂ ht.2.2 (fun m hm => by
        rw [call_syms hc₁, call_syms hc₂]; exact hf m (by simp [inames, hm])) (call_same hc₁ hc₂ hs))
    | icallNext hi₂ hne₂ x₂ =>
      exfalso
      obtain ⟨a₂, rest, hi₂', ht₂⟩ := icall_trace x₂
      rw [hi₂] at hi₂'; cases hi₂'
      rw [ht₂] at ht
      simp only [List.append_assoc, List.cons_append] at ht
      obtain ⟨-, ht⟩ := append_cancel (by simp only [List.length_map]; exact addrs_length _ _ _) ht
      simp only [List.cons.injEq, Leak.addr.injEq] at ht
      apply hne₂
      rw [← ht.1, hn]
  | icallNext hi₁ hne₁ x₁ ih =>
    intro hc s₂ s₂' t₂ r₁ r₂ e₂ ht hf hs
    cases e₂ with
    | icallNext hi₂ hne₂ x₂ =>
      exact ih (fun i hi => hc i (List.mem_cons_of_mem _ (List.mem_append_right _ hi))) x₂ ht
        (fun m hm => hf m (List.mem_cons_of_mem _ (List.mem_append_right _ hm))) hs
    | icall hi₂ hc₂ x₂ hr₂ =>
      exfalso
      obtain ⟨a₁, rest, hi₁', ht₁⟩ := icall_trace x₁
      rw [hi₁] at hi₁'; cases hi₁'
      rw [ht₁] at ht
      simp only [List.append_assoc, List.cons_append] at ht
      obtain ⟨-, ht⟩ := append_cancel (by simp only [List.length_map]; exact addrs_length _ _ _) ht
      simp only [List.cons.injEq, Leak.addr.injEq] at ht
      apply hne₁
      rw [ht.1]; exact (hf _ (List.mem_cons_self ..)).symm

/-- `lock`, for two runs with the same trace. -/
theorem lock_eq {S : Addr → Prop} {c : Prog isa} (hc : NoSp c) {s₁ s₂ s₁' s₂' : State} {t : List Leak}
    (e₁ : Exec isa c s₁ t s₁') (e₂ : Exec isa c s₂ t s₂') (hf : ∀ n ∈ inames c, s₁.syms n = s₂.syms n)
    (h : Same S s₁ s₂) : Same S s₁' s₂' :=
  lock e₁ hc e₂ (r₁ := []) (r₂ := []) rfl hf h

end VG.X86_64.StackLock

/-! ## The vector registers, in two runs along the same path -/

namespace VG.X86_64.VecLock

open VG VG.X86_64 VG.X86_64.UpperLock VG.Impl.Scrub.X86_64

/-- The SSE registers agree if `lo`, and their bits above 127 if `hi`. -/
def VA (a : Bool × Bool) (s₁ s₂ : State) : Prop :=
  (a.1 = true → s₁.xmm = s₂.xmm) ∧ (a.2 = true → s₁.ymmHi = s₂.ymmHi ∧ s₁.zmmHi = s₂.zmmHi)

/-- An instruction that keeps every vector register. -/
def plainI (i : Instr) : Bool := i.vecLevel == 0 && !writesVec i

/-- A block that zeroes the SSE registers at the level `lv` (`clearVec`),
then keeps them. -/
def clrB (lv : VecLevel) (is : List Instr) : Bool := is.take 16 == clearVec lv && (is.drop 16).all plainI

/-- What two runs along the same path agree on after `c`, from `a`: a block
that keeps the vector registers keeps the agreement; one that clears them
makes the SSE registers agree (zero), and the bits above too at a level
above `sse` (`vpxor`'s VEX encoding zeroes them); a call of code that may
write them keeps only the agreement of the bits above, if that code keeps
them (`UpperLock.up`). A loop agrees on what its body keeps from what it
agrees on. -/
def step (lv : VecLevel) : Prog isa → Bool × Bool → Bool × Bool
  | .block is, a => if clrB lv is then (true, lv != .sse || a.2) else if is.all plainI then a else (false, false)
  | .seq x y, a => step lv y (step lv x a)
  | .ite _ t e, a => ((step lv t a).1 && (step lv e a).1, (step lv t a).2 && (step lv e a).2)
  | .loop b _, a =>
    let a₁ := (a.1 && (step lv b a).1, a.2 && (step lv b a).2)
    if (!a₁.1 || (step lv b a₁).1) && (!a₁.2 || (step lv b a₁).2) then a₁ else (false, false)
  | .call _ b, a => if (instrs b).all plainI then a else (false, a.2 && up b true)
  | .frame _ b _, a => step lv b a
  | .icall .., _ => (false, false)

theorem va_mono {a b : Bool × Bool} {s₁ s₂ : State} (h : VA b s₁ s₂) (h₁ : a.1 = true → b.1 = true)
    (h₂ : a.2 = true → b.2 = true) : VA a s₁ s₂ :=
  ⟨fun e => h.1 (h₁ e), fun e => h.2 (h₂ e)⟩

theorem va_none {s₁ s₂ : State} : VA (false, false) s₁ s₂ := ⟨nofun, nofun⟩

theorem plain_keep {c : Prog isa} (hc : ∀ i ∈ instrs c, plainI i = true) {s s' : State} {t : List Leak}
    (e : Exec isa c s t s') : s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi ∧ s'.zmmHi = s.zmmHi := by
  have hx := Residue.Exec.xmmKeep (fun i hi => by
    have := hc i hi; simp only [plainI, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at this; exact this.2) e
  have hv := Residue.Exec.vecKeep0 (fun i hi => by
    have := hc i hi; simp only [plainI, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at this; exact this.1) e
  simp only [Residue.vk0, Prod.mk.injEq] at hv
  exact ⟨hx, hv.2.2.2.1, hv.2.2.2.2⟩

theorem keep_va {a : Bool × Bool} {s₁ s₂ u₁ u₂ : State}
    (k₁ : u₁.xmm = s₁.xmm ∧ u₁.ymmHi = s₁.ymmHi ∧ u₁.zmmHi = s₁.zmmHi)
    (k₂ : u₂.xmm = s₂.xmm ∧ u₂.ymmHi = s₂.ymmHi ∧ u₂.zmmHi = s₂.zmmHi) (h : VA a s₁ s₂) : VA a u₁ u₂ :=
  ⟨fun e => by rw [k₁.1, k₂.1, h.1 e], fun e => by rw [k₁.2.1, k₂.2.1, k₁.2.2, k₂.2.2]; exact h.2 e⟩

/-- A block that clears: zero SSE registers, and the bits above zero too at
a level above `sse`, or kept. -/
theorem clr_run {lv : VecLevel} {is : List Instr} (h : clrB lv is = true) {s u : State} {t : List Leak}
    (e : execBlock isa is s = some (u, t)) :
    u.xmm = (fun _ => 0) ∧ (lv ≠ .sse → u.ymmHi = (fun _ => 0) ∧ u.zmmHi = (fun _ => 0)) ∧
      (lv = .sse → u.ymmHi = s.ymmHi ∧ u.zmmHi = s.zmmHi) := by
  simp only [clrB, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h₁, h₂⟩ := h
  rw [← List.take_append_drop 16 is, execBlock_append, h₁, clearVec, Scrub.execBlock_vecs] at e
  simp only [Option.bind_some, Option.map_eq_some_iff, Prod.mk.injEq] at e
  obtain ⟨⟨u', t'⟩, e', rfl, -⟩ := e
  have k := plain_keep (c := .block (is.drop 16)) (fun i hi => List.all_eq_true.mp h₂ i hi) (Exec.block e')
  rw [k.1, k.2.1, k.2.2]
  refine ⟨funext fun x => by simp [Scrub.clearedV, Scrub.mem_xregs x], fun hv => ⟨funext fun x => ?_,
    funext fun x => ?_⟩, fun hv => ⟨funext fun x => ?_, funext fun x => ?_⟩⟩
  all_goals simp [Scrub.clearedV, Scrub.mem_xregs x, hv]

theorem push_xmm {i : Instr} {s s₁ : State} (hp : isa.push i s = some s₁) : s₁.xmm = s.xmm := by
  cases i <;> simp only [isa, push, reduceCtorEq] at hp
  case push rs => split at hp <;> cases hp; exact Residue.pushRegs_xmm s rs
  case alloc => split at hp <;> cases hp; rfl

theorem pop_xmm {j : Instr} {s₁ s₂ s' : State} (hq : isa.pop j s₁ s₂ = some s') : s'.xmm = s₂.xmm := by
  cases j <;> simp only [isa, pop, reduceCtorEq] at hq
  case pop r k => split at hq <;> cases hq; exact Residue.popReg_xmm s₂ _ _
  case free => split at hq <;> cases hq; rfl

theorem pushpop_keep {i : Instr} {s s₁ : State} (hp : isa.push i s = some s₁) :
    s₁.xmm = s.xmm ∧ s₁.ymmHi = s.ymmHi ∧ s₁.zmmHi = s.zmmHi := by
  have := Residue.push_vk0 hp
  simp only [Residue.vk0, Prod.mk.injEq] at this
  exact ⟨push_xmm hp, this.2.2.2.1, this.2.2.2.2⟩

theorem pop_keep {j : Instr} {s₁ s₂ s' : State} (hq : isa.pop j s₁ s₂ = some s') :
    s'.xmm = s₂.xmm ∧ s'.ymmHi = s₂.ymmHi ∧ s'.zmmHi = s₂.zmmHi := by
  have := Residue.pop_vk0 hq
  simp only [Residue.vk0, Prod.mk.injEq] at this
  exact ⟨pop_xmm hq, this.2.2.2.1, this.2.2.2.2⟩

theorem step_loop_fix {lv : VecLevel} {b : Prog isa} {c : Cond} {a : Bool × Bool}
    (h : (!a.1 || (step lv b a).1) && (!a.2 || (step lv b a).2) = true) : step lv (.loop b c) a = a := by
  rcases a with ⟨x, y⟩
  simp only [step]
  generalize hs : step lv b (x, y) = p at h ⊢
  rcases p with ⟨p₁, p₂⟩
  cases x <;> cases y <;> cases p₁ <;> cases p₂ <;> simp_all

/-- Two runs of `c` whose traces agree, extended by `r₁` and `r₂`, from
states whose functions called indirectly are at the same addresses and that
agree on the vector registers as `a` says, agree on them at the end as
`step lv c a` says. -/
theorem lock {lv : VecLevel} {c : Prog isa} {s₁ s₁' : State} {t₁ : List Leak} (e₁ : Exec isa c s₁ t₁ s₁') :
    ∀ {s₂ s₂' : State} {t₂ r₁ r₂ : List Leak} {a : Bool × Bool}, Exec isa c s₂ t₂ s₂' → t₁ ++ r₁ = t₂ ++ r₂ →
      (∀ n ∈ inames c, s₁.syms n = s₂.syms n) → VA a s₁ s₂ → VA (step lv c a) s₁' s₂' := by
  induction e₁ with
  | @block is _ _ _ h₁ =>
    intro s₂ s₂' t₂ r₁ r₂ a e₂ _ _ hs
    cases e₂ with
    | block h₂ =>
      simp only [step]
      split
      · rename_i hc
        obtain ⟨x₁, y₁, z₁⟩ := clr_run hc h₁
        obtain ⟨x₂, y₂, z₂⟩ := clr_run hc h₂
        refine ⟨fun _ => by rw [x₁, x₂], fun hh => ?_⟩
        by_cases hv : lv = .sse
        · subst hv
          simp only [bne_self_eq_false, Bool.false_or] at hh
          rw [(z₁ rfl).1, (z₂ rfl).1, (z₁ rfl).2, (z₂ rfl).2]; exact hs.2 hh
        · rw [(y₁ hv).1, (y₂ hv).1, (y₁ hv).2, (y₂ hv).2]; exact ⟨rfl, rfl⟩
      · split
        · rename_i _ hp
          exact keep_va (plain_keep (c := .block is) (fun i hi => List.all_eq_true.mp hp i hi) (Exec.block h₁))
            (plain_keep (c := .block is) (fun i hi => List.all_eq_true.mp hp i hi) (Exec.block h₂)) hs
        · exact va_none
  | seq x₁ y₁ ihx ihy =>
    intro s₂ s₂' t₂ r₁ r₂ a e₂ ht hf hs
    cases e₂ with
    | seq x₂ y₂ =>
      simp only [List.append_assoc] at ht
      simp only [inames, List.mem_append] at hf
      obtain ⟨hx, -⟩ := UpperLock.lock x₁ x₂ ht fun n hn => hf n (.inl hn)
      subst hx
      exact ihy y₂ (List.append_cancel_left ht) (fun n hn => by
        rw [Exec.syms x₁, Exec.syms x₂]; exact hf n (.inr hn)) (ihx x₂ ht (fun n hn => hf n (.inl hn)) hs)
  | iteT _ x₁ ih =>
    intro s₂ s₂' t₂ r₁ r₂ a e₂ ht hf hs
    cases e₂ with
    | iteT _ x₂ =>
      simp only [List.cons_append, List.cons.injEq, true_and] at ht
      simp only [inames, List.mem_append] at hf
      exact va_mono (ih x₂ ht (fun n hn => hf n (.inl hn)) hs) (fun e => by simp only [step, Bool.and_eq_true] at e; exact e.1)
        (fun e => by simp only [step, Bool.and_eq_true] at e; exact e.1)
    | iteF _ _ => exact (branch_ne ht).elim
  | iteF _ x₁ ih =>
    intro s₂ s₂' t₂ r₁ r₂ a e₂ ht hf hs
    cases e₂ with
    | iteF _ x₂ =>
      simp only [List.cons_append, List.cons.injEq, true_and] at ht
      simp only [inames, List.mem_append] at hf
      exact va_mono (ih x₂ ht (fun n hn => hf n (.inr hn)) hs) (fun e => by simp only [step, Bool.and_eq_true] at e; exact e.2)
        (fun e => by simp only [step, Bool.and_eq_true] at e; exact e.2)
    | iteT _ _ => exact (branch_ne ht.symm).elim
  | @loopExit b c _ _ _ x₁ _ ih =>
    intro s₂ s₂' t₂ r₁ r₂ a e₂ ht hf hs
    cases e₂ with
    | loopExit x₂ _ =>
      simp only [List.append_assoc] at ht
      have hb := ih x₂ ht hf hs
      simp only [step]
      split
      · exact va_mono hb (fun e => by simp only [Bool.and_eq_true] at e; exact e.2)
          (fun e => by simp only [Bool.and_eq_true] at e; exact e.2)
      · exact va_none
    | loopNext x₂ _ _ =>
      simp only [List.append_assoc] at ht
      obtain ⟨h, -⟩ := UpperLock.lock x₁ x₂ ht hf
      subst h
      simp at ht
  | @loopNext b c _ _ _ _ _ x₁ _ _ ihx ihl =>
    intro s₂ s₂' t₂ r₁ r₂ a e₂ ht hf hs
    cases e₂ with
    | loopExit x₂ _ =>
      simp only [List.append_assoc] at ht
      obtain ⟨h, -⟩ := UpperLock.lock x₁ x₂ ht hf
      subst h
      simp at ht
    | loopNext x₂ _ l₂ =>
      simp only [List.append_assoc] at ht
      obtain ⟨h, -⟩ := UpperLock.lock x₁ x₂ ht hf
      subst h
      have ht' := List.append_cancel_left ht
      simp only [List.cons_append, List.cons.injEq, true_and] at ht'
      have hb := ihx x₂ ht hf hs
      simp only [step]
      split
      · rename_i hfix
        have a₁ := va_mono hb (a := ((a.1 && (step lv b a).1), (a.2 && (step lv b a).2)))
          (fun e => by simp only [Bool.and_eq_true] at e; exact e.2)
          (fun e => by simp only [Bool.and_eq_true] at e; exact e.2)
        have := ihl l₂ ht' (fun n hn => by rw [Exec.syms x₁, Exec.syms x₂]; exact hf n hn) a₁
        rwa [step_loop_fix hfix] at this
      · exact va_none
  | @call nm b _ _ _ _ _ hc₁ x₁ hr₁ _ =>
    intro s₂ s₂' t₂ r₁ r₂ a e₂ ht hf hs
    have e₁ : Exec isa (.call nm b) _ _ _ := .call hc₁ x₁ hr₁
    simp only [step]
    split
    · rename_i hp
      exact keep_va (plain_keep (c := .call nm b) (fun i hi => List.all_eq_true.mp hp i hi) e₁)
        (plain_keep (c := .call nm b) (fun i hi => List.all_eq_true.mp hp i hi) e₂) hs
    · refine ⟨nofun, fun e => ?_⟩
      simp only [Bool.and_eq_true] at e
      exact (UpperLock.lock e₁ e₂ ht hf).2 true e.2 fun _ => hs.2 e.1
  | frame hp₁ x₁ hq₁ ih =>
    intro s₂ s₂' t₂ r₁ r₂ a e₂ ht hf hs
    cases e₂ with
    | frame hp₂ x₂ hq₂ =>
      simp only [List.append_assoc] at ht
      obtain ⟨-, ht⟩ := append_cancel (by simp only [List.length_map]; exact addrs_length _ _ _) ht
      have hb := ih x₂ ht (fun n hn => by rw [push_syms hp₁, push_syms hp₂]; exact hf n hn)
        (keep_va (pushpop_keep hp₁) (pushpop_keep hp₂) hs)
      exact keep_va (pop_keep hq₁) (pop_keep hq₂) hb
  | icall => intros; exact va_none
  | icallNext => intros; exact va_none

/-- Constant-time code that leaves the vector registers agreeing in two runs
along the same path, from registers that agree (`step lv c (true, true)`),
and calls no function indirectly: two runs end agreeing on every vector
register, so its clearing need clear none of them, and only its
general-purpose registers (all of them but `rax`, here). -/
theorem regsOk_of_vec {c : Prog isa} {k : Contract isa} {lv : VecLevel} {xs : List XReg} {ps : List Reg}
    (hct : ConstantTime isa k.pre k.pub c) (hn : inames c = []) (hv : step lv c (true, true) = (true, true)) :
    Scrub.RegsOk c k xs ps scratchRegs := by
  intro s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ hp ho _ e₁ e₂
  obtain rfl := hct s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ hp e₁ e₂
  obtain ⟨-, -, -, -, -, -, -, -, hxm, hy, hz, -⟩ := ho
  have h := lock (lv := lv) e₁ e₂ (r₁ := []) (r₂ := []) rfl (by rw [hn]; nofun) (a := (true, true))
    ⟨fun _ => hxm, fun _ => ⟨hy, hz⟩⟩
  rw [hv] at h
  refine ⟨fun r _ _ hg => absurd ‹r ∈ scratchRegs› hg, fun x _ => ?_⟩
  exact ⟨congrFun (h.1 rfl) x, congrFun (h.2 rfl).1 x, congrFun (h.2 rfl).2 x⟩

end VG.X86_64.VecLock

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
