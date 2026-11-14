module

public import VerifiedGarbage.Impl.Scrub.X86_64Sel
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.X86_64.Call

/-!
# Returning without secret residue, the wipe chosen by a public argument (x86-64)

`Verified.scrubSel`: `Verified.scrubM` for `scrubSel`, whose wipe is that of
`ksT` or `ksF` by whether a word `L` of the state on entry (a stack
argument, which two runs the contract relates agree on, and which the code
leaves where it found it) is below `lim`. Its correctness and constant time
need nothing of what the code leaves in the stack; without secret residue,
it needs `ResOkSel`: that two runs leave the same bytes in the rest of the
stack but the wipe chosen.
-/

@[expose] public section

open VG.Impl.Scrub.X86_64

namespace VG.X86_64.Scrub

open VG.X86_64 VG.X86_64.Residue

/-- The granules `scrubSelTail` wipes, given the word `l` it compares with `lim`. -/
def selKs (ksT ksF : List Nat) (lim : BitVec 32) (l : BitVec 64) : List Nat :=
  if l.toNat < (lim.signExtend 64).toNat then ksT else ksF

/-- The trace of `scrubSelTail` from `rsp = p`, given the word `l` it reads at `p + off`. -/
def selTr (v : VecLevel) (ksT ksF cs : List Nat) (off : Nat) (lim : BitVec 32) (p : Addr) (l : BitVec 64)
    (f : VecLevel := v) : List Leak :=
  .addr (p + BitVec.ofInt 64 (off : Int)) ::
    .branch (decide (l.toNat < (lim.signExtend 64).toNat)) :: tailTr v (selKs ksT ksF lim l) cs p f

/-- The state after `selHead`. -/
def headState (lim : BitVec 32) (l : BitVec 64) (u : State) : State :=
  arithFlags (u.setReg .r11 l) (l - lim.signExtend 64) (l.toNat < (lim.signExtend 64).toNat)
    (subOverflow l (lim.signExtend 64) (l - lim.signExtend 64))

theorem head_run (off : Nat) (lim : BitVec 32) (u : State) {l : BitVec 64}
    (hl : u.load64 (u.gpr .rsp + BitVec.ofInt 64 (off : Int)) = some l) :
    execBlock isa (selHead off lim) u = some (headState lim l u, [.addr (u.gpr .rsp + BitVec.ofInt 64 (off : Int))]) := by
  simp only [selHead, execBlock, isa, reduceExec, addrs, srcAddrs, readSrc, State.ea, hl]
  simp [execAlu, readSrc, headState, State.setReg]

theorem headState_rsp (lim : BitVec 32) (l : BitVec 64) (u : State) :
    (headState lim l u).gpr .rsp = u.gpr .rsp := by
  simp [headState, arithFlags, State.setFlags, State.setReg]

theorem headState_mem (lim : BitVec 32) (l : BitVec 64) (u : State) :
    (headState lim l u).mem = u.mem := rfl

theorem headState_mxcsr (lim : BitVec 32) (l : BitVec 64) (u : State) :
    (headState lim l u).mxcsr = u.mxcsr := rfl

theorem headState_eval (lim : BitVec 32) (l : BitVec 64) (u : State) :
    isa.eval .b (headState lim l u) = some (decide (l.toNat < (lim.signExtend 64).toNat)) := rfl

/-- What `selHead` writes, `r11` and the flags, the clearing overwrites. -/
theorem finState_head {v : VecLevel} {rb : Nat} {xs : List XReg} {ps gs : List Reg} {m' : Mem} {f : VecLevel}
    (h11 : Reg.r11 ∈ ps) (lim : BitVec 32) (l : BitVec 64) (u : State) :
    finState v rb xs ps gs m' (headState lim l u) f = finState v rb xs ps gs m' u f := by
  have hp : ps ≠ [] := fun e => by rw [e] at h11; cases h11
  have hax : (headState lim l u).gpr .rax = u.gpr .rax := by
    simp [headState, arithFlags, State.setFlags, State.setReg]
  simp only [finState, hax, clearedP, hp, ↓reduceIte]
  cases v <;>
    simp only [clearedG, clearedH, clearedV, headState, arithFlags, State.setFlags, State.setReg,
      State.mk.injEq] <;>
    refine ⟨funext fun r => ?_, by simp only [and_self]⟩ <;>
    by_cases h1 : r ∈ gs <;> by_cases h2 : r ∈ ps <;> by_cases h3 : r = .rax <;> by_cases h4 : r = .r11 <;>
    simp_all

/-- `scrubSelTail`'s run: `tail_run` of the wipe its head chooses. -/
theorem selTail_run (v : VecLevel) (rb : Nat) {xs : List XReg} {ps gs : List Reg} {ksT ksF : List Nat}
    (cs : List Nat) {f : VecLevel} (off : Nat) (lim : BitVec 32)
    (htT : TailOk rb xs ps gs ksT) (htF : TailOk rb xs ps gs ksF) (h11 : Reg.r11 ∈ ps) (u : State)
    (hv : ∀ b ∈ cs, 0 < b ∧ b < 4096 ∧ b % 8 = 0) (hs : cs.sum ≤ (u.gpr .rsp).toNat)
    (hevT : EvexOk f ksT cs (u.gpr .rsp)) (hevF : EvexOk f ksF cs (u.gpr .rsp)) {l : BitVec 64}
    (hl : u.load64 (u.gpr .rsp + BitVec.ofInt 64 (off : Int)) = some l) :
    ∃ m', Exec isa (scrubSelTail v rb xs ps gs ksT ksF cs off lim f) u
        (selTr v ksT ksF cs off lim (u.gpr .rsp) l f) (finState v rb xs ps gs m' u f) ∧
      (∀ x, WCov (selKs ksT ksF lim l) cs (u.gpr .rsp) x → m' x = 0) ∧
      (∀ x, ¬ WCov (selKs ksT ksF lim l) cs (u.gpr .rsp) x → m' x = u.mem x) := by
  have hh := head_run off lim u hl
  have hsp := headState_rsp lim l u
  by_cases hb : l.toNat < (lim.signExtend 64).toNat
  · obtain ⟨m', he, hz, hu⟩ := tail_run v rb cs (f := f) htT (headState lim l u) hv (by rw [hsp]; exact hs)
      (by rw [hsp]; exact hevT)
    rw [hsp, finState_head h11] at he
    rw [hsp] at hz hu; rw [headState_mem] at hu
    have e : Exec isa (scrubSelTail v rb xs ps gs ksT ksF cs off lim f) u _ _ :=
      Exec.seq (M := isa) (.block hh) (.iteT (by rw [headState_eval]; simp [hb]) he)
    refine ⟨m', ?_, ?_, ?_⟩
    · simpa only [selTr, selKs, hb, decide_true, ↓reduceIte, List.cons_append, List.nil_append] using e
    · simpa only [selKs, hb, ↓reduceIte] using hz
    · simpa only [selKs, hb, ↓reduceIte, headState_mem] using hu
  · obtain ⟨m', he, hz, hu⟩ := tail_run v rb cs (f := f) htF (headState lim l u) hv (by rw [hsp]; exact hs)
      (by rw [hsp]; exact hevF)
    rw [hsp, finState_head h11] at he
    rw [hsp] at hz hu; rw [headState_mem] at hu
    have e : Exec isa (scrubSelTail v rb xs ps gs ksT ksF cs off lim f) u _ _ :=
      Exec.seq (M := isa) (.block hh) (.iteF (by rw [headState_eval]; simp [hb]) he)
    refine ⟨m', ?_, ?_, ?_⟩
    · simpa only [selTr, selKs, hb, decide_false, ↓reduceIte, List.cons_append, List.nil_append] using e
    · simpa only [selKs, hb, ↓reduceIte] using hz
    · simpa only [selKs, hb, ↓reduceIte, headState_mem] using hu

/-- Two runs of `c` leave the same bytes in the `stack` bytes below the stack
pointer on entry but those the wipe `scrubSelTail` chooses, by the word `L`
of the entry state, zeroes. -/
def ResOkSel (c : Prog isa) (k : Contract isa) (stack : Nat) (ksT ksF cs : List Nat) (lim : BitVec 32)
    (L : State → BitVec 64) : Prop :=
  ∀ s₁ s₂ t₁ t₂ u₁ u₂, k.pre s₁ → k.pre s₂ → k.pub s₁ s₂ → Outside 0 s₁ s₂ → s₁.unknowns = s₂.unknowns →
    Exec isa c s₁ t₁ u₁ → Exec isa c s₂ t₂ u₂ →
    ∀ x, (⟨s₁.gpr .rsp - BitVec.ofNat 64 stack, stack⟩ : Region).Contains x 1 →
      ¬ WCov (selKs ksT ksF lim (L s₁)) cs (s₁.gpr .rsp) x → u₁.mem x = u₂.mem x

section
variable {A : Abi isa} {sig : Sig} {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
  {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
  {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}

/-- `Verified.scrubM`, for `scrubSel`: the word `L` its head reads on return
is one of the state on entry (`hL`) that two related runs agree on (`hLp`).
Correctness and constant time need nothing more; without secret residue,
that two runs leave the same bytes in the stack but the wipe chosen
(`ResOkSel`). -/
theorem Verified.scrubSel {c : Prog isa} {v f : VecLevel} {xs : List XReg} {ps gs : List Reg}
    {ksT ksF cs : List Nat} {off : Nat} {lim : BitVec 32} {L : State → BitVec 64}
    (hA : ScrubAbi A)
    (h : Verified target c (sig.contract A pre post wa stack leak))
    (hsp : SpSafe c) (hd : c.x86_64Depth ≤ stack) (hcs : cs.sum = stack) (hst : stack + 8 < 2 ^ 64)
    (hv : ∀ b ∈ cs, 0 < b ∧ b < 4096 ∧ b % 8 = 0)
    (hlv : ∀ i ∈ instrs c, i.vecLevelR ≤ v.level)
    (hmx : f ≠ .evex → MxSame c)
    (hrb : sig.retBits A.ptrBits ≤ 32 ∨ sig.retBits A.ptrBits = 64)
    (hpost : ∀ s u u', (sig.contract A pre post wa stack leak).pre s →
      (sig.contract A pre post wa stack leak).post s u →
      (∀ x, (∃ r ∈ s.rd ++ s.wr, r.Contains x 1) → u'.mem x = u.mem x) →
      (u'.gpr .rax).setWidth (sig.retBits A.ptrBits) = (u.gpr .rax).setWidth (sig.retBits A.ptrBits) →
      (sig.contract A pre post wa stack leak).post s u')
    (hL : ∀ s t u, (sig.contract A pre post wa stack leak).pre s → Exec isa c s t u →
      u.load64 (u.gpr .rsp + BitVec.ofInt 64 (off : Int)) = some (L s))
    (hLp : ∀ s₁ s₂, (sig.contract A pre post wa stack leak).pre s₁ → (sig.contract A pre post wa stack leak).pre s₂ →
      (sig.contract A pre post wa stack leak).pub s₁ s₂ → L s₁ = L s₂)
    (htT : TailOk (sig.retBits A.ptrBits) xs ps gs ksT) (htF : TailOk (sig.retBits A.ptrBits) xs ps gs ksF)
    (h11 : Reg.r11 ∈ ps)
    (hxs : (∀ x, x ∈ xs) ∨ ∀ i ∈ instrs c, writesVec i = false)
    (hxe : v = .evex → ∀ x, x ∈ xs) (hevT : ∀ p : Addr, cs.sum ≤ p.toNat → EvexOk f ksT cs p)
    (hevF : ∀ p : Addr, cs.sum ≤ p.toNat → EvexOk f ksF cs p)
    (hgk : ∀ r ∈ scratchRegs, r ∉ gs → r ∉ ps → ∀ i ∈ instrs c, Taint.clobbers i r = false) :
    Verified target (scrubSel v (sig.retBits A.ptrBits) xs ps gs ksT ksF cs off lim c f)
        (sig.contract A pre post wa stack leak) ∧
      (ResOkSel c (sig.contract A pre post wa stack leak) stack ksT ksF cs lim L →
        NoResidue (scrubSel v (sig.retBits A.ptrBits) xs ps gs ksT ksF cs off lim c f)
          (sig.contract A pre post wa stack leak) (sig.retBits A.ptrBits)) := by
  have hnps : ∀ r, r ∉ scratchRegs → r ∉ ps := fun r h h' => h (htT.psOk r h')
  have hngs : ∀ r, r ∉ scratchRegs → r ∉ gs := fun r h h' => h (htT.gsOk r h')
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
      Exec isa (scrubSelTail v (sig.retBits A.ptrBits) xs ps gs ksT ksF cs off lim f) u t' s' →
      ∃ m', t' = selTr v ksT ksF cs off lim (s.gpr .rsp) (L s) f ∧
        s' = finState v (sig.retBits A.ptrBits) xs ps gs m' u f ∧
        (∀ x, ¬ (⟨s.gpr .rsp - BitVec.ofNat 64 stack, stack⟩ : Region).Contains x 1 → m' x = u.mem x) ∧
        (∀ x, WCov (selKs ksT ksF lim (L s)) cs (s.gpr .rsp) x → m' x = 0) ∧
        (∀ x, ¬ WCov (selKs ksT ksF lim (L s)) cs (s.gpr .rsp) x → m' x = u.mem x) := by
    intro s t u s' t' hs he het
    obtain ⟨-, -, hr, hl⟩ := run s t u hs he
    obtain ⟨m', e, hz, hu⟩ := selTail_run v (sig.retBits A.ptrBits) cs off lim htT htF h11 u hv hl
      (hevT _ hl) (hevF _ hl) (hL s t u hs he)
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
    fun hres s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp ho hun e₁ e₂ => ?_⟩
  · -- Correctness.
    obtain ⟨t, u, he, -⟩ := hcor s hs
    obtain ⟨ha, hq, hr, hl⟩ := run s t u hs he
    obtain ⟨m', et, hz, hu⟩ := selTail_run v (sig.retBits A.ptrBits) cs off lim htT htF h11 u hv hl
      (hevT _ hl) (hevF _ hl) (hL s t u hs he)
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
    rw [hct _ _ _ _ _ _ h₁ h₂ hp a₁ a₂, contract_pub_rsp hA hp, hLp _ _ h₁ h₂ hp]
  · -- No residue.
    cases e₁ with | seq a₁ b₁ =>
    cases e₂ with | seq a₂ b₂ =>
    rename_i u₁ _ _ u₂ _ _
    obtain ⟨m₁, -, rfl, hmo₁, hz₁, hu₁⟩ := tail s₁ _ _ _ _ h₁ a₁ b₁
    obtain ⟨m₂, -, rfl, hmo₂, hz₂, hu₂⟩ := tail s₂ _ _ _ _ h₂ a₂ b₂
    rw [← hLp _ _ h₁ h₂ hp] at hz₂ hu₂
    obtain ⟨ha₁, -, -, -⟩ := run s₁ _ _ h₁ a₁
    obtain ⟨ha₂, -, -, -⟩ := run s₂ _ _ h₂ a₂
    have ho' := ho
    obtain ⟨hrd, hwr, hg, -, -, -, -, -, hxm, hy, hz, hyH, hzH, hmx', hm⟩ := ho
    have hsp' : s₁.gpr .rsp = s₂.gpr .rsp := hg .rsp (by decide)
    have rw₁ := Exec.rdwr a₁
    have rw₂ := Exec.rdwr a₂
    -- Below the level `evex`, the code keeps `zmm16`–`zmm31`, and leaves in
    -- MXCSR a function of MXCSR on entry, which is the same in both runs.
    have lv1 : v ≠ .evex → ∀ i ∈ instrs c, i.vecLevelR ≤ 1 := fun hne i hi => by
      have := hlv i hi
      cases v
      · simp only [VecLevel.level] at this; omega
      · exact this
      · exact absurd rfl hne
    have k1 : v ≠ .evex → (u₁.ymmH = s₁.ymmH ∧ u₁.zmmHiH = s₁.zmmHiH) ∧
        (u₂.ymmH = s₂.ymmH ∧ u₂.zmmHiH = s₂.zmmHiH) := fun hne => by
      have k₁ := Exec.vecKeep1R (lv1 hne) a₁
      have k₂ := Exec.vecKeep1R (lv1 hne) a₂
      simp only [vk1R, Prod.mk.injEq] at k₁ k₂
      exact ⟨k₁, k₂⟩
    have kmx : f ≠ .evex → u₁.mxcsr = u₂.mxcsr := fun hne =>
      hmx hne _ _ _ _ _ a₁ (hct _ _ _ _ _ _ h₁ h₂ hp a₁ a₂ ▸ a₂) hmx'
    have cH : v ≠ .evex → ∀ w : State, (clearedH v w).ymmH = w.ymmH ∧ (clearedH v w).zmmHiH = w.zmmHiH :=
      fun hne w => by cases v <;> first | exact ⟨rfl, rfl⟩ | exact absurd rfl hne
    have hdep : c.x86_64Depth < 2 ^ 64 := by omega
    have f₁ := Exec.stackFrame hsp a₁ hdep
    have f₂ := Exec.stackFrame hsp a₂ hdep
    have cs_ : ∀ r : Reg, r ∉ scratchRegs → r ≠ .rax → r ∈ calleeSaved := by intro r; cases r <;> decide
    -- With the vector registers' upper halves kept: code of level 0, or that writes none.
    have l0 : (∃ x, x ∉ xs ∧ v ≠ .sse) → ∀ i ∈ instrs c, i.vecLevelR = 0 := by
      rintro ⟨x, hx, -⟩ i hi
      by_cases he : v = .evex
      · exact absurd (hxe he x) hx
      · rcases hxs with h | h
        · exact absurd (h x) hx
        · exact vecLevelR_of_writesVec (h i hi) (lv1 he i hi)
    have upper : ∀ x, ¬ (v ≠ .sse ∧ x ∈ xs) → u₁.ymmHi x = u₂.ymmHi x ∧ u₁.zmmHi x = u₂.zmmHi x := by
      intro x hn
      have hl : ∀ i ∈ instrs c, i.vecLevelR = 0 := by
        by_cases hs : v = .sse
        · subst hs; exact fun i hi => by simpa [VecLevel.level] using hlv i hi
        · exact l0 ⟨x, fun h => hn ⟨hs, h⟩, hs⟩
      have k₁ := Exec.vecKeep0R hl a₁
      have k₂ := Exec.vecKeep0R hl a₂
      simp only [vk0R, Prod.mk.injEq] at k₁ k₂
      rw [k₁.2.2.1, k₂.2.2.1, k₁.2.2.2, k₂.2.2.2, hy, hz]
      exact ⟨rfl, rfl⟩
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
      · rw [(cH he _).2, (cH he _).2, (k1 he).1.2, (k1 he).2.2, hzH]
    · rw [finState_other.2.2.2.2.2.1, finState_other.2.2.2.2.2.1]
      by_cases he : f = .evex
      · exact fixMx_congr f he (by rw [ha₁.2.2, ha₂.2.2, hmx'])
      · cases f
        · exact kmx he
        · exact kmx he
        · exact absurd rfl he
    · rw [finState_other.1, finState_other.1]
      have hx' : ∀ r ∈ s₁.rd ++ s₁.wr, ¬ r.Contains x 1 := by
        rw [finState_other.2.1, finState_other.2.2.1, rw₁.1, rw₁.2] at hx
        exact hx
      by_cases hb : (⟨s₁.gpr .rsp - BitVec.ofNat 64 stack, stack⟩ : Region).Contains x 1
      · by_cases hw : WCov (selKs ksT ksF lim (L s₁)) cs (s₁.gpr .rsp) x
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

/-! ## The stack argument the head reads -/

section
variable {A : Abi isa} {sig : Sig} {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
  {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
  {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}

open VG.X86_64.RScrub in
/-- The argument area is readable. -/
theorem pre_argRd (hA : ScrubAbi A) {s : State} (h : (sig.contract A pre post wa stack leak).pre s)
    (hn : 0 < nStack sig) : (⟨stackArgAddr s 0, 8 * nStack sig⟩ : Region) ∈ s.rd := by
  simp only [Sig.contract] at h
  split at h
  · exact h.elim
  obtain ⟨-, hrd, -⟩ := h
  apply hA.rdSub
  rw [hrd, widths_eq hA, hA.argArea, nStack_argArea sig s hn]
  refine List.mem_map.mpr ⟨(_, false), List.mem_filter.mpr ⟨List.mem_append_right _ ?_, rfl⟩, rfl⟩
  simp

open VG.X86_64.RScrub in
/-- Code verified against a contract that `Sig.contract` derives, whose
frames and calls stay within its stack, leaves its stack argument `j` where
its caller put it, readable at the same offset from the stack pointer. -/
theorem load_stackArg (hA : ScrubAbi A) {c : Prog isa}
    (h : Verified target c (sig.contract A pre post wa stack leak))
    (hsp : SpSafe c) (hd : c.x86_64Depth ≤ stack) (hst : stack + 8 < 2 ^ 64) (hs0 : 0 < stack) {j : Nat} (hj : j < nStack sig) {off : Nat} (hoff : off = 8 * (j + 1)) :
    ∀ s t u, (sig.contract A pre post wa stack leak).pre s → Exec isa c s t u →
      u.load64 (u.gpr .rsp + BitVec.ofInt 64 (off : Int)) = some (stackArg s j) := by
  intro s t u hs he
  obtain ⟨t', u', he', ha, -⟩ := h.1 s hs
  obtain ⟨-, rfl⟩ := Exec.det he he'
  have hr : u.gpr .rsp = s.gpr .rsp := ha.1 .rsp (by decide)
  obtain ⟨hrd, hwr⟩ := Exec.rdwr he
  have hn : 0 < nStack sig := by omega
  obtain ⟨htop, hnw⟩ := pre_argArea hA hs
  have htop := htop hn
  have hrs : stack ≤ (s.gpr .rsp).toNat := by
    rcases (contract_pre_scrub hA hs).1 with h0 | h0
    · omega
    · exact h0
  have hofs : BitVec.ofInt 64 (off : Int) = BitVec.ofNat 64 (8 * (j + 1)) := by
    rw [BitVec.ofInt_natCast, hoff]
  rw [hr, hofs]
  have hc : (⟨stackArgAddr s 0, 8 * nStack sig⟩ : Region).Contains (s.gpr .rsp + BitVec.ofNat 64 (8 * (j + 1))) 8 := by
    simp only [stackArgAddr]
    exact VG.Offset.contains _ (by omega) (by omega) (by omega)
  simp only [State.load64]
  rw [ite_eq_left ⟨_, List.mem_append_left _ (hrd ▸ pre_argRd hA hs hn), hc⟩]
  refine congrArg some (Mem.readW_congr fun i hi => ?_)
  have hfr := Exec.stackFrame hsp he (by omega)
  have hk : 8 * (j + 1) + i = 8 + (8 * j + i) := by omega
  have hx : s.gpr .rsp + BitVec.ofNat 64 (8 * (j + 1)) + BitVec.ofNat 64 i =
      s.gpr .rsp + BitVec.ofNat 64 (8 + (8 * j + i)) := by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, hk]
  rw [hx]
  refine hfr _ fun r hr' => ?_
  rcases List.mem_append.mp hr' with hr' | hr'
  · exact hnw _ (by simp only [Nat.reduceDiv] at hi; omega) r hr'
  · simp only [List.mem_singleton] at hr'; subst hr'
    have hx := (s.gpr .rsp).isLt
    simp only [Region.Contains, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    simp only [Nat.reduceDiv] at hi
    have hkn : 8 * j + i < 8 * nStack sig := by omega
    generalize (s.gpr .rsp).toNat = P at *
    rw [Nat.mod_eq_of_lt (a := c.x86_64Depth) (by omega)]
    omega

end


section
variable {A : Abi isa} {sig : Sig} {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
  {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
  {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}

/-- `Verified.scrubM`, with its residue hypothesis (`ResOk`) moved into the
conclusion: correctness and constant time need nothing of what the code
leaves in the stack. -/
theorem Verified.scrubMV {c : Prog isa} {v f : VecLevel} {xs : List XReg} {ps gs : List Reg} {ks cs : List Nat}
    (hA : ScrubAbi A)
    (h : Verified target c (sig.contract A pre post wa stack leak))
    (hsp : SpSafe c) (hd : c.x86_64Depth ≤ stack) (hcs : cs.sum = stack) (hst : stack + 8 < 2 ^ 64)
    (hv : ∀ b ∈ cs, 0 < b ∧ b < 4096 ∧ b % 8 = 0)
    (hlv : ∀ i ∈ instrs c, i.vecLevelR ≤ v.level)
    (hmx : f ≠ .evex → MxSame c)
    (hrb : sig.retBits A.ptrBits ≤ 32 ∨ sig.retBits A.ptrBits = 64)
    (hpost : ∀ s u u', (sig.contract A pre post wa stack leak).pre s →
      (sig.contract A pre post wa stack leak).post s u →
      (∀ x, (∃ r ∈ s.rd ++ s.wr, r.Contains x 1) → u'.mem x = u.mem x) →
      (u'.gpr .rax).setWidth (sig.retBits A.ptrBits) = (u.gpr .rax).setWidth (sig.retBits A.ptrBits) →
      (sig.contract A pre post wa stack leak).post s u')
    (ht : TailOk (sig.retBits A.ptrBits) xs ps gs ks)
    (hxs : (∀ x, x ∈ xs) ∨ ∀ i ∈ instrs c, writesVec i = false)
    (hxe : v = .evex → ∀ x, x ∈ xs) (hev : ∀ p : Addr, cs.sum ≤ p.toNat → EvexOk f ks cs p)
    (hgk : ∀ r ∈ scratchRegs, r ∉ gs → r ∉ ps → ∀ i ∈ instrs c, Taint.clobbers i r = false) :
    Verified target (Impl.Scrub.X86_64.scrub v (sig.retBits A.ptrBits) xs ps gs ks cs c f)
        (sig.contract A pre post wa stack leak) ∧
      (ResOk c (sig.contract A pre post wa stack leak) stack ks cs →
        NoResidue (Impl.Scrub.X86_64.scrub v (sig.retBits A.ptrBits) xs ps gs ks cs c f)
          (sig.contract A pre post wa stack leak) (sig.retBits A.ptrBits)) := by
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
      Exec isa (Impl.Scrub.X86_64.scrubTail v (sig.retBits A.ptrBits) xs ps gs ks cs f) u t' s' →
      ∃ m', t' = tailTr v ks cs (s.gpr .rsp) f ∧ s' = finState v (sig.retBits A.ptrBits) xs ps gs m' u f ∧
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
    fun hres s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp ho hun e₁ e₂ => ?_⟩
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
    obtain ⟨hrd, hwr, hg, -, -, -, -, -, hxm, hy, hz, hyH, hzH, hmx', hm⟩ := ho
    have hsp' : s₁.gpr .rsp = s₂.gpr .rsp := hg .rsp (by decide)
    have rw₁ := Exec.rdwr a₁
    have rw₂ := Exec.rdwr a₂
    -- Below the level `evex`, the code keeps `zmm16`–`zmm31`, and leaves in
    -- MXCSR a function of MXCSR on entry, which is the same in both runs.
    have lv1 : v ≠ .evex → ∀ i ∈ instrs c, i.vecLevelR ≤ 1 := fun hne i hi => by
      have := hlv i hi
      cases v
      · simp only [VecLevel.level] at this; omega
      · exact this
      · exact absurd rfl hne
    have k1 : v ≠ .evex → (u₁.ymmH = s₁.ymmH ∧ u₁.zmmHiH = s₁.zmmHiH) ∧
        (u₂.ymmH = s₂.ymmH ∧ u₂.zmmHiH = s₂.zmmHiH) := fun hne => by
      have k₁ := Exec.vecKeep1R (lv1 hne) a₁
      have k₂ := Exec.vecKeep1R (lv1 hne) a₂
      simp only [vk1R, Prod.mk.injEq] at k₁ k₂
      exact ⟨k₁, k₂⟩
    have kmx : f ≠ .evex → u₁.mxcsr = u₂.mxcsr := fun hne =>
      hmx hne _ _ _ _ _ a₁ (hct _ _ _ _ _ _ h₁ h₂ hp a₁ a₂ ▸ a₂) hmx'
    have cH : v ≠ .evex → ∀ w : State, (clearedH v w).ymmH = w.ymmH ∧ (clearedH v w).zmmHiH = w.zmmHiH :=
      fun hne w => by cases v <;> first | exact ⟨rfl, rfl⟩ | exact absurd rfl hne
    have hdep : c.x86_64Depth < 2 ^ 64 := by omega
    have f₁ := Exec.stackFrame hsp a₁ hdep
    have f₂ := Exec.stackFrame hsp a₂ hdep
    have cs_ : ∀ r : Reg, r ∉ scratchRegs → r ≠ .rax → r ∈ calleeSaved := by intro r; cases r <;> decide
    -- With the vector registers' upper halves kept: code of level 0, or that writes none.
    have l0 : (∃ x, x ∉ xs ∧ v ≠ .sse) → ∀ i ∈ instrs c, i.vecLevelR = 0 := by
      rintro ⟨x, hx, -⟩ i hi
      by_cases he : v = .evex
      · exact absurd (hxe he x) hx
      · rcases hxs with h | h
        · exact absurd (h x) hx
        · exact vecLevelR_of_writesVec (h i hi) (lv1 he i hi)
    have upper : ∀ x, ¬ (v ≠ .sse ∧ x ∈ xs) → u₁.ymmHi x = u₂.ymmHi x ∧ u₁.zmmHi x = u₂.zmmHi x := by
      intro x hn
      have hl : ∀ i ∈ instrs c, i.vecLevelR = 0 := by
        by_cases hs : v = .sse
        · subst hs; exact fun i hi => by simpa [VecLevel.level] using hlv i hi
        · exact l0 ⟨x, fun h => hn ⟨hs, h⟩, hs⟩
      have k₁ := Exec.vecKeep0R hl a₁
      have k₂ := Exec.vecKeep0R hl a₂
      simp only [vk0R, Prod.mk.injEq] at k₁ k₂
      rw [k₁.2.2.1, k₂.2.2.1, k₁.2.2.2, k₂.2.2.2, hy, hz]
      exact ⟨rfl, rfl⟩
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
      · rw [(cH he _).2, (cH he _).2, (k1 he).1.2, (k1 he).2.2, hzH]
    · rw [finState_other.2.2.2.2.2.1, finState_other.2.2.2.2.2.1]
      by_cases he : f = .evex
      · exact fixMx_congr f he (by rw [ha₁.2.2, ha₂.2.2, hmx'])
      · cases f
        · exact kmx he
        · exact kmx he
        · exact absurd rfl he
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

/-! ## Registering code scrubbed by `scrubSel` -/

theorem xsOf_ne {c : Prog isa} {ks ks' : List Nat} (h : ks ≠ []) (h' : ks' ≠ []) : xsOf c ks = xsOf c ks' := by
  unfold xsOf; simp [h, h']

theorem psOf_ne {ks ks' : List Nat} (h : ks ≠ []) (h' : ks' ≠ []) : psOf ks = psOf ks' := by
  simp [psOf, h, h']

theorem scrubSel_spSafe {c : Prog isa} (v : VecLevel) (rb : Nat) (xs : List XReg) (ps gs : List Reg)
    (ksT ksF cs : List Nat) (off : Nat) (lim : BitVec 32) {f : VecLevel} (hps : ∀ r ∈ ps, r ∈ scratchRegs)
    (hgs : ∀ r ∈ gs, r ∈ scratchRegs) (h : c.all (fun i => !isa.writesSp i) = true) :
    (scrubSel v rb xs ps gs ksT ksF cs off lim c f).all (fun i => !isa.writesSp i) = true := by
  have hT := scrub_spSafe (c := .block []) v rb xs ps gs ksT cs (f := f) hps hgs rfl
  have hF := scrub_spSafe (c := .block []) v rb xs ps gs ksF cs (f := f) hps hgs rfl
  simp only [scrub, Code.all, List.all_nil, Bool.true_and] at hT hF
  simp only [scrubSel, scrubSelTail, Code.all, h, hT, hF, Bool.true_and, Bool.and_true]
  rfl

/-- `r`'s code, scrubbed as `scrubRegSel` does: verified, and without secret
residue if it leaves the same bytes in two runs in the stack but the wipe
chosen. -/
theorem scrubSelCode {api : Api} (r : Registration api target) (v : VecLevel) {ksT ksF : List Nat} {off : Nat}
    {lim : BitVec 32} {L : State → BitVec 64} (hT : ksT ≠ []) (hF : ksF ≠ [])
    (hd : r.code.x86_64Depth ≤ r.stack) (hst : r.stack + 8 < 2 ^ 64) (h8 : r.stack % 8 = 0)
    (hlv : r.code.all (fun i => decide (i.vecLevel ≤ v.level)) = true)
    (hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨ api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (hL : ∀ s t u, r.contract.pre s → Exec isa r.code s t u →
      u.load64 (u.gpr .rsp + BitVec.ofInt 64 (off : Int)) = some (L s))
    (hLp : ∀ s₁ s₂, r.contract.pre s₁ → r.contract.pre s₂ → r.contract.pub s₁ s₂ → L s₁ = L s₂)
    (hne : v ≠ .evex) :
    Verified target (scrubSel v (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
        (xsOf r.code ksF) (psOf ksF) (gsOf Taint.clobbers r.code) ksT ksF (chunks r.stack) off lim r.code)
        r.contract ∧
      (ResOkSel r.code r.contract r.stack ksT ksF (chunks r.stack) lim L →
        NoResidue (scrubSel v (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
          (xsOf r.code ksF) (psOf ksF) (gsOf Taint.clobbers r.code) ksT ksF (chunks r.stack) off lim r.code)
          r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)) := by
  obtain ⟨pre, post, leak, e⟩ := r.ofSig
  have hv := r.verified
  have hp := hpost
  have hL' := hL
  have hLp' := hLp
  rw [e] at hv hp hL' hLp' ⊢
  have hrb' := hrb
  rw [← withMode_ptrBits ((abi.withConsts r.consts).withTables api.sig r.tables) api.pubMode] at hrb' hp ⊢
  have htF := tailOk_of (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits) r.code ksF
  have htT := tailOk_of (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits) r.code ksT
  rw [xsOf_ne hT hF, psOf_ne hT hF] at htT
  rw [← withMode_ptrBits ((abi.withConsts r.consts).withTables api.sig r.tables) api.pubMode] at htF htT
  exact Verified.scrubSel (ScrubAbi.of r.consts api.sig r.tables api.pubMode) hv (SpSafe.of_all r.spSafe) hd
    (chunks_sum r.stack) hst (chunks_valid h8)
    (fun i hi => by simpa using Code.all_instrs (allR_of_all hlv) i hi)
    (fun hne => MxSame.of_fun (mxFun_of (mxOk_of_all hlv hne))) hrb' hp hL' hLp' htT htF
    (by simp [psOf, hF]) (xs_of _ _) (evexReg_of_ne (c := r.code) (ks := ksF) (stack := r.stack) hne).1
    (evexReg_of_ne (c := r.code) (stack := r.stack) hne).2
    (evexReg_of_ne (c := r.code) (stack := r.stack) hne).2 (gs_of _ _)

/-- `r`, scrubbed by `scrubSel` below the level `evex`: its code followed by
the clearing, with the granules `ksT` of its `r.stack` bytes of stack wiped
if the word at `[rsp + off]` on return, `L` of the state on entry, is below
`lim`, and `ksF` otherwise; without secret residue if `hres` is given. -/
def scrubRegSel {api : Api} (r : Registration api target) (v : VecLevel) (ksT ksF : List Nat) (off : Nat)
    (lim : BitVec 32) (L : State → BitVec 64) (hT : ksT ≠ []) (hF : ksF ≠ [])
    (hd : r.code.x86_64Depth ≤ r.stack) (hst : r.stack + 8 < 2 ^ 64) (h8 : r.stack % 8 = 0)
    (hlv : r.code.all (fun i => decide (i.vecLevel ≤ v.level)) = true)
    (hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨ api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (hL : ∀ s t u, r.contract.pre s → Exec isa r.code s t u →
      u.load64 (u.gpr .rsp + BitVec.ofInt 64 (off : Int)) = some (L s))
    (hLp : ∀ s₁ s₂, r.contract.pre s₁ → r.contract.pre s₂ → r.contract.pub s₁ s₂ → L s₁ = L s₂)
    (hres : Option (PLift (ResOkSel r.code r.contract r.stack ksT ksF (chunks r.stack) lim L)))
    (hw : r.written = []) (hne : v ≠ .evex := by decide) : Registration api target where
  suffix := r.suffix
  consts := r.consts
  tables := r.tables
  stack := r.stack
  code := scrubSel v (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
    (xsOf r.code ksF) (psOf ksF) (gsOf Taint.clobbers r.code) ksT ksF (chunks r.stack) off lim r.code
  contract := r.contract
  verified := (scrubSelCode r v hT hF hd hst h8 hlv hrb hpost hL hLp hne).1
  ofApi := r.ofApi
  ofSig := r.ofSig
  spSafe := scrubSel_spSafe v _ _ _ _ _ _ _ _ _ (tailOk_of 0 r.code ksF).psOk (tailOk_of 0 r.code ksF).gsOk r.spSafe
  written := r.written
  writtenOk := by
    rw [hw]; exact fun _ _ _ _ _ => True.intro
  extra := r.extra
  vendor := r.vendor
  notWith := r.notWith
  residue := hres.map fun h => ⟨(scrubSelCode r v hT hF hd hst h8 hlv hrb hpost hL hLp hne).2 h.down⟩

open VG.X86_64.RScrub in
/-- `load_stackArg`, of a registration. -/
theorem reg_load_stackArg {api : Api} (r : Registration api target) (hd : r.code.x86_64Depth ≤ r.stack)
    (hst : r.stack + 8 < 2 ^ 64) (hs0 : 0 < r.stack) {j : Nat} (hj : j < nStack api.sig) {off : Nat}
    (hoff : off = 8 * (j + 1)) :
    ∀ s t u, r.contract.pre s → Exec isa r.code s t u →
      u.load64 (u.gpr .rsp + BitVec.ofInt 64 (off : Int)) = some (stackArg s j) := by
  obtain ⟨pre, post, leak, e⟩ := r.ofSig
  have hv := r.verified
  rw [e] at hv ⊢
  exact load_stackArg (ScrubAbi.of r.consts api.sig r.tables api.pubMode) hv (SpSafe.of_all r.spSafe) hd hst hs0
    hj hoff

open VG.X86_64.RScrub in
/-- A public 64-bit stack argument is the same in two runs the contract relates. -/
theorem reg_pub_stackArg {api : Api} (r : Registration api target) {j : Nat} (hj : j < nStack api.sig)
    (hpk : (api.sig.params.flatMap (·.2.pubs)).getD (argRegs.length + j) false = true)
    (h64 : (widths api.sig).getD (argRegs.length + j) 64 = 64) :
    ∀ s₁ s₂, r.contract.pre s₁ → r.contract.pre s₂ → r.contract.pub s₁ s₂ → stackArg s₁ j = stackArg s₂ j := by
  obtain ⟨pre, post, leak, e⟩ := r.ofSig
  rw [e]
  intro s₁ s₂ _ _ hp
  have := pub_stack (ScrubAbi.of r.consts api.sig r.tables api.pubMode) hp hj hpk
  rw [h64, BitVec.setWidth_eq, BitVec.setWidth_eq] at this
  exact this

open VG.X86_64.RScrub in
/-- `r`, scrubbed by `scrubSel` (`scrubRegSel`) at the level of its code,
which must be below `evex`: with the granules `ksT` wiped if its 64-bit
public stack argument `j` is below `lim`, and every granule of its stack
otherwise; without secret residue if `hres` is given. If a side condition
fails, or the clearing would need a CPU feature `r`'s code does not, `r`
itself. -/
def withScrubSel {api : Api} (r : Registration api target)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (ksT : List Nat) (j : Nat) (lim : BitVec 32)
    (hres : Option (PLift (ResOkSel r.code r.contract r.stack ksT (allKs (chunks r.stack)) (chunks r.stack) lim
      (fun s => stackArg s j)))) :
    Registration api target :=
  let v := levelAll r.code
  if hne : v = .evex then r else
  if hT : ksT = [] then r else
  if hF : allKs (chunks r.stack) = [] then r else
  if hd : r.code.x86_64Depth ≤ r.stack then
  if hst : r.stack + 8 < 2 ^ 64 then
  if hs0 : 0 < r.stack then
  if h8 : r.stack % 8 = 0 then
  if hlv : r.code.all (fun i => decide (i.vecLevel ≤ v.level)) = true then
  if hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨
      api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64 then
  if hw : r.written = [] then
  if hj : j < nStack api.sig then
  if hpk : (api.sig.params.flatMap (·.2.pubs)).getD (argRegs.length + j) false = true then
  if h64 : (widths api.sig).getD (argRegs.length + j) 64 = 64 then
    let r' := scrubRegSel r v ksT (allKs (chunks r.stack)) (8 * (j + 1)) lim (fun s => stackArg s j) hT hF hd hst h8
      hlv hrb hpost (reg_load_stackArg r hd hst hs0 hj rfl) (reg_pub_stackArg r hj hpk h64) hres hw hne
    if (Code.requiresDedup isa.requires r'.code).all
        (fun f => (Code.requiresDedup isa.requires r.code).contains f) then r' else r
  else r else r else r else r else r else r else r else r else r else r

/-- `r`'s code, scrubbed with the granules `ks` wiped: verified, and without
secret residue if two runs leave the same bytes in the rest of its stack. -/
theorem scrubKsCode {api : Api} (r : Registration api target) (v : VecLevel) {ks : List Nat}
    (hd : r.code.x86_64Depth ≤ r.stack) (hst : r.stack + 8 < 2 ^ 64) (h8 : r.stack % 8 = 0)
    (hlv : r.code.all (fun i => decide (i.vecLevel ≤ v.level)) = true)
    (hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨ api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (hne : v ≠ .evex) :
    Verified target (scrub v (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
        (xsOf r.code ks) (psOf ks) (gsOf Taint.clobbers r.code) ks (chunks r.stack) r.code) r.contract ∧
      (ResOk r.code r.contract r.stack ks (chunks r.stack) →
        NoResidue (scrub v (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
          (xsOf r.code ks) (psOf ks) (gsOf Taint.clobbers r.code) ks (chunks r.stack) r.code)
          r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)) := by
  obtain ⟨pre, post, leak, e⟩ := r.ofSig
  have hv := r.verified
  have hp := hpost
  rw [e] at hv hp ⊢
  have hrb' := hrb
  rw [← withMode_ptrBits ((abi.withConsts r.consts).withTables api.sig r.tables) api.pubMode] at hrb' hp ⊢
  exact Verified.scrubMV (ScrubAbi.of r.consts api.sig r.tables api.pubMode) hv (SpSafe.of_all r.spSafe) hd
    (chunks_sum r.stack) hst (chunks_valid h8)
    (fun i hi => by simpa using Code.all_instrs (allR_of_all hlv) i hi)
    (fun hne => MxSame.of_fun (mxFun_of (mxOk_of_all hlv hne))) hrb' hp (tailOk_of _ _ _) (xs_of _ _)
    (evexReg_of_ne (c := r.code) (ks := ks) (stack := r.stack) hne).1
    (evexReg_of_ne (c := r.code) (stack := r.stack) hne).2 (gs_of _ _)

/-- `r`, scrubbed below the level `evex` with the granules `ks` of its stack
wiped (`scrub`), at the level of its code; without secret residue if `hres`
is given. If a side condition fails, or the clearing would need a CPU
feature `r`'s code does not, `r` itself. -/
def withScrubKs {api : Api} (r : Registration api target)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (ks : List Nat) (hres : Option (PLift (ResOk r.code r.contract r.stack ks (chunks r.stack)))) :
    Registration api target :=
  let v := levelAll r.code
  if hne : v = .evex then r else
  if hd : r.code.x86_64Depth ≤ r.stack then
  if hst : r.stack + 8 < 2 ^ 64 then
  if h8 : r.stack % 8 = 0 then
  if hlv : r.code.all (fun i => decide (i.vecLevel ≤ v.level)) = true then
  if hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨
      api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64 then
  if hw : r.written = [] then
    let r' : Registration api target := {
      suffix := r.suffix
      consts := r.consts
      tables := r.tables
      stack := r.stack
      code := scrub v (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
        (xsOf r.code ks) (psOf ks) (gsOf Taint.clobbers r.code) ks (chunks r.stack) r.code
      contract := r.contract
      verified := (scrubKsCode r v hd hst h8 hlv hrb hpost hne).1
      ofApi := r.ofApi
      ofSig := r.ofSig
      spSafe := scrub_spSafe v _ _ _ _ _ _ (tailOk_of 0 r.code ks).psOk (tailOk_of 0 r.code ks).gsOk r.spSafe
      written := r.written
      writtenOk := by rw [hw]; exact fun _ _ _ _ _ => True.intro
      extra := r.extra
      vendor := r.vendor
      notWith := r.notWith
      residue := hres.map fun h => ⟨(scrubKsCode r v hd hst h8 hlv hrb hpost hne).2 h.down⟩ }
    if (Code.requiresDedup isa.requires r'.code).all
        (fun f => (Code.requiresDedup isa.requires r.code).contains f) then r' else r
  else r else r else r else r else r else r

end VG.X86_64.Scrub
