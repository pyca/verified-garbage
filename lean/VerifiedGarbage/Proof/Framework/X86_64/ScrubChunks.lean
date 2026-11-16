module

public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
import VerifiedGarbage.Proof.Framework.CodeOnce

/-!
# x86-64 residue: wiping the stack in chosen chunks

`Scrub.scrubRegM` and `RScrub.withScrubRes` wipe the stack in
`chunks r.stack`, whose 16-byte granules end at the stack pointer on entry,
which is 8 off 16: every 16-byte store of the wipe is unaligned, and one in
four of them splits a cache line. The same, for any chunks `cs` summing to
the stack: a chunk of 8 bytes at the top puts the granules of the chunk
below it 16 bytes aligned (`scrubRegMC`, `withScrubResC`).

At every level but `sse` the wipe stores two adjacent granules of a chunk
with one 32-byte store, which, the stack pointer being known only 8 off 16,
splits a cache line one time in two. `scrubW` is `scrub` with that
choice its own argument `w` (`Verified.scrubMW`, a copy of
`Verified.scrubM` and `tail_run` for it), so that a wipe of aligned
granules can store 16 bytes at a time (`withScrubResC` with `wide` false).
It is here, not in `Scrub.lean`, so that the many modules that import
`Scrub.lean` are not rebuilt for it.
-/

@[expose] public section

open VG.Impl.Scrub.X86_64

namespace VG.X86_64.Scrub

open VG.X86_64 VG.X86_64.Residue

/-- `scrubTail`, with the wipe's stores chosen by `w` rather than by the
level: with `w` false, 16 bytes at a time (`zero16`) at every level, so
that each store of a granule 16 bytes aligned stays within a cache line. -/
def scrubTailW (v : VecLevel) (w : Bool) (retBits : Nat) (xs : List XReg) (ps gs : List Reg) (ks cs : List Nat)
    (f : VecLevel := v) : Prog isa :=
  .seq (.block (xs.map (zeroX v) ++ clearHigh v ++ ps.map zeroR))
    (.seq (mxFix f) (.seq (wipe w ks cs) (.block (retFix retBits ++ gs.map zeroR))))

/-- `c`, then `scrubTailW`. -/
def scrubW (v : VecLevel) (w : Bool) (retBits : Nat) (xs : List XReg) (ps gs : List Reg) (ks cs : List Nat)
    (c : Prog isa) (f : VecLevel := v) : Prog isa :=
  .seq c (scrubTailW v w retBits xs ps gs ks cs f)

/-- The trace of `scrubTailW` from `rsp = p`. -/
def tailTrW (v : VecLevel) (w : Bool) (ks cs : List Nat) (p : Addr) (f : VecLevel := v) : List Leak :=
  mxTr f p ++ wipeTr w ks cs p

/-- `tail_run`, for `scrubTailW`. -/
theorem tail_runW (v : VecLevel) (w : Bool) (rb : Nat) {xs : List XReg} {ps gs : List Reg} {ks : List Nat}
    (cs : List Nat) (hw : w = true → v ≠ .sse) {f : VecLevel} (ht : TailOk rb xs ps gs ks) (u : State)
    (hv : ∀ b ∈ cs, 0 < b ∧ b < 4096 ∧ b % 8 = 0) (hs : cs.sum ≤ (u.gpr .rsp).toNat)
    (hev : EvexOk f ks cs (u.gpr .rsp)) :
    ∃ m', Exec isa (scrubTailW v w rb xs ps gs ks cs f) u (tailTrW v w ks cs (u.gpr .rsp) f)
        (finState v rb xs ps gs m' u f) ∧
      (∀ x, WCov ks cs (u.gpr .rsp) x → m' x = 0) ∧ (∀ x, ¬ WCov ks cs (u.gpr .rsp) x → m' x = u.mem x) := by
  let u₁ := clearedP ps (clearedH v (clearedV v xs u))
  have h₁ : execBlock isa (xs.map (zeroX v) ++ clearHigh v ++ ps.map zeroR) u = some (u₁, []) := by
    rw [execBlock_append, execBlock_append, execBlock_vecs]
    simp only [Option.bind_some]
    rw [execBlock_high]
    simp only [Option.bind_some, Option.map_some]
    rw [execBlock_gprsP]
    rfl
  have hcH : ∀ w : State, (clearedH v w).gpr = w.gpr ∧ (clearedH v w).xmm = w.xmm ∧ (clearedH v w).mem = w.mem ∧
      (clearedH v w).mxcsr = w.mxcsr ∧ (clearedH v w).ymmHi = w.ymmHi := fun w => by
    cases v <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hsp : u₁.gpr .rsp = u.gpr .rsp := by
    simp only [u₁, clearedP]; split
    · rw [(hcH _).1]; rfl
    · simp only [clearedG, show Reg.rsp ∉ ps from fun h => absurd (ht.psOk _ h) (by decide : Reg.rsp ∉ scratchRegs),
        ↓reduceIte]
      rw [(hcH _).1]; rfl
  have hx0 : ks ≠ [] → u₁.xmm .xmm0 = 0 := fun h => by
    simp only [u₁, clearedP]; split
    · rw [(hcH _).2.1]; simp [clearedV, ht.x0 h]
    · show (clearedH v (clearedV v xs u)).xmm .xmm0 = 0
      rw [(hcH _).2.1]; simp [clearedV, ht.x0 h]
  have hy0 : w = true → ks ≠ [] → u₁.ymmHi .xmm0 = 0 := fun hw' h => by
    have hv' : v ≠ .sse := hw hw'
    simp only [u₁, clearedP]; split
    · rw [(hcH _).2.2.2.2]; simp [clearedV, ht.x0 h, hv']
    · show (clearedH v (clearedV v xs u)).ymmHi .xmm0 = 0
      rw [(hcH _).2.2.2.2]; simp [clearedV, ht.x0 h, hv']
  have hr11 : ks ≠ [] → u₁.gpr .r11 = 0 := fun h => by
    simp only [u₁, clearedP]; split
    · rename_i hp; exact absurd (ht.r11 h) (by rw [hp]; simp)
    · simp [clearedG, ht.r11 h]
  have hmem : u₁.mem = u.mem := by
    simp only [u₁, clearedP]; split
    · rw [(hcH _).2.2.1]; rfl
    · show (clearedH v (clearedV v xs u)).mem = u.mem
      rw [(hcH _).2.2.1]; rfl
  have hmx : u₁.mxcsr = u.mxcsr := by
    simp only [u₁, clearedP]; split
    · rw [(hcH _).2.2.2.1]; rfl
    · show (clearedH v (clearedV v xs u)).mxcsr = u.mxcsr
      rw [(hcH _).2.2.2.1]; rfl
  -- `mxFix`.
  obtain ⟨m₁, hem, hm₁⟩ := mxFix_run f u₁ (fun h => by rw [hsp]; have := (hev h).2.1; omega_using [hs, this]) (fun h => by
    have hp : ps ≠ [] := fun e => absurd (ht.r11 (hev h).1) (by rw [e]; simp)
    refine ⟨hr11 (hev h).1, ?_, ?_, ?_, ?_⟩ <;> simp only [u₁, clearedP, hp, ↓reduceIte, clearedG])
  rw [hsp, hmx] at hem
  rw [hsp, hmem] at hm₁
  let u₂ : State := { u₁ with mem := m₁, mxcsr := fixMx f u.mxcsr }
  obtain ⟨m', he, ho, hi⟩ := wipe_run w ks cs u₂ hv (by show cs.sum ≤ (u₁.gpr .rsp).toNat; rw [hsp]; exact hs)
    hx0 hy0 hr11
  rw [show u₂.gpr .rsp = u.gpr .rsp from hsp] at he ho hi
  refine ⟨m', ?_, ho, fun x hx => ?_⟩
  · have h₃ := execBlock_clearGpr rb gs ht.gne
      (fun h => absurd (ht.gsOk _ h) (by decide : Reg.rax ∉ scratchRegs)) { u₂ with mem := m' }
    have e := Exec.seq (M := isa) (.block h₁) (.seq hem (.seq he (.block h₃)))
    simp only [List.nil_append, List.append_nil] at e
    have hax : u₁.gpr .rax = u.gpr .rax := by
      simp only [u₁, clearedP]; split
      · rw [(hcH _).1]; rfl
      · simp only [clearedG, show Reg.rax ∉ ps from fun h => absurd (ht.psOk _ h) (by decide : Reg.rax ∉ scratchRegs),
          ↓reduceIte]
        rw [(hcH _).1]; rfl
    have hf : finState v rb xs ps gs m' u f =
        clearedG gs (({ u₂ with mem := m' } : State).setReg .rax (retVal rb (u₂.gpr .rax))) := by
      rw [show u₂.gpr .rax = u.gpr .rax from hax]; rfl
    rw [hf]
    exact e
  · rw [hi x hx]
    exact hm₁ x fun ⟨h, hs4⟩ => hx ((hev h).2.2 x hs4)


section
variable {A : Abi isa} {sig : Sig} {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
  {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
  {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}

/-- `Verified.scrubM`, for `scrubW`: the wipe stores 32 bytes at a time only
if `w`, which needs a level above `sse`. -/
theorem Verified.scrubMW {c : Prog isa} {v f : VecLevel} {w : Bool} {xs : List XReg} {ps gs : List Reg} {ks cs : List Nat}
    (hw : w = true → v ≠ .sse) (hA : ScrubAbi A)
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
    (hres : ResOk c (sig.contract A pre post wa stack leak) stack ks cs)
    (ht : TailOk (sig.retBits A.ptrBits) xs ps gs ks)
    (hxs : (∀ x, x ∈ xs) ∨ ∀ i ∈ instrs c, writesVec i = false)
    (hxe : v = .evex → ∀ x, x ∈ xs) (hev : ∀ p : Addr, cs.sum ≤ p.toNat → EvexOk f ks cs p)
    (hgk : ∀ r ∈ scratchRegs, r ∉ gs → r ∉ ps → ∀ i ∈ instrs c, Taint.clobbers i r = false) :
    Verified target (scrubW v w (sig.retBits A.ptrBits) xs ps gs ks cs c f)
        (sig.contract A pre post wa stack leak) ∧
      NoResidue (scrubW v w (sig.retBits A.ptrBits) xs ps gs ks cs c f)
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
      Exec isa (scrubTailW v w (sig.retBits A.ptrBits) xs ps gs ks cs f) u t' s' →
      ∃ m', t' = tailTrW v w ks cs (s.gpr .rsp) f ∧ s' = finState v (sig.retBits A.ptrBits) xs ps gs m' u f ∧
        (∀ x, ¬ (⟨s.gpr .rsp - BitVec.ofNat 64 stack, stack⟩ : Region).Contains x 1 → m' x = u.mem x) ∧
        (∀ x, WCov ks cs (s.gpr .rsp) x → m' x = 0) ∧ (∀ x, ¬ WCov ks cs (s.gpr .rsp) x → m' x = u.mem x) := by
    intro s t u s' t' hs he het
    obtain ⟨-, -, hr, hl⟩ := run s t u hs he
    obtain ⟨m', e, hz, hu⟩ := tail_runW v w (sig.retBits A.ptrBits) cs hw ht u hv hl (hev _ hl)
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
    obtain ⟨m', et, hz, hu⟩ := tail_runW v w (sig.retBits A.ptrBits) cs hw ht u hv hl (hev _ hl)
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
          rw [BitVec.add_comm, BitVec.add_sub_cancel], BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hi])]
        simp only [Nat.reduceDiv] at hi; omega_using [hi]))
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
      · simp only [VecLevel.level] at this; omega_using [this]
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
    have hdep : c.x86_64Depth < 2 ^ 64 := by omega_using [hd, hst]
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
          rintro sp rfl hc; exact hb (below_sub hd (by omega_using [hst]) x hc)
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

theorem scrubW_spSafe {c : Prog isa} (v : VecLevel) (w : Bool) (rb : Nat) (xs : List XReg) (ps gs : List Reg)
    (ks cs : List Nat) {f : VecLevel} (hps : ∀ r ∈ ps, r ∈ scratchRegs) (hgs : ∀ r ∈ gs, r ∈ scratchRegs)
    (h : c.all (fun i => !isa.writesSp i) = true) :
    (scrubW v w rb xs ps gs ks cs c f).all (fun i => !isa.writesSp i) = true := by
  have hx : (xs.map (zeroX v)).all (fun i => !isa.writesSp i) = true := by
    simp only [List.all_map, List.all_eq_true]
    exact fun x _ => by cases v <;> rfl
  have hp : (ps.map zeroR).all (fun i => !isa.writesSp i) = true := by
    simp only [List.all_map, List.all_eq_true]
    exact fun r hr => zeroR_spSafe r (hps r hr)
  have hh : (clearHigh v).all (fun i => !isa.writesSp i) = true := by cases v <;> rfl
  have hm : (mxFix f).all (fun i => !isa.writesSp i) = true := by cases f <;> rfl
  have hv : (xs.map (zeroX v) ++ clearHigh v ++ ps.map zeroR).all (fun i => !isa.writesSp i) = true := by
    rw [List.all_append, List.all_append, hx, hh, hp]; rfl
  have hg : (retFix rb ++ gs.map zeroR).all (fun i => !isa.writesSp i) = true := by
    simp only [List.all_append, List.all_map, Bool.and_eq_true, List.all_eq_true]
    refine ⟨?_, fun r hr => zeroR_spSafe r (hgs r hr)⟩
    unfold retFix
    split
    · intro i hi; simp at hi; subst hi; rfl
    · split
      · intro i hi; simp at hi; subst hi; rfl
      · split
        · intro i hi; simp at hi; subst hi; rfl
        · intro i hi; simp at hi
  rw [scrubW, scrubTailW]
  simp only [Code.all]
  rw [h, hv, hm, wipe_spSafe w ks cs, hg]
  rfl

/-- `scrubCodeE_noResidue`, below the level `evex`, with the stack wiped in
the chunks `cs` (from the top) rather than `chunks r.stack`: each chunk's
16-byte granules end at its top, so a chunk of 8 bytes at the top puts
those of the chunks below it 16 bytes aligned, the stack pointer on entry
being 8 off 16. -/
theorem scrubCodeMC_noResidue {api : Api} (r : Registration api target) (v : VecLevel) (ks cs : List Nat)
    (hcs : cs.sum = r.stack) (hcv : ∀ b ∈ cs, 0 < b ∧ b < 4096 ∧ b % 8 = 0)
    (hd : r.code.x86_64Depth ≤ r.stack) (hst : r.stack + 8 < 2 ^ 64)
    (hlv : r.code.all (fun i => decide (i.vecLevelR ≤ v.level)) = true)
    (hmx : (mxClass r.code).isSome = true)
    (hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨ api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (hres : ResOk r.code r.contract r.stack ks cs) (hne : v ≠ .evex) :
    NoResidue (scrub v (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
      (xsOf r.code ks) (psOf ks) (gsOf Taint.clobbers r.code) ks cs r.code) r.contract
      (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits) := by
  obtain ⟨pre, post, leak, e⟩ := r.ofSig
  have hv := r.verified
  have hp := hpost
  have hr := hres
  rw [e] at hv hp hr ⊢
  have hrb' := hrb
  rw [← withMode_ptrBits ((abi.withConsts r.consts).withTables api.sig r.tables) api.pubMode] at hrb' hp ⊢
  exact (Verified.scrubM (ScrubAbi.of r.consts api.sig r.tables api.pubMode) hv (SpSafe.of_all r.spSafe) hd
    hcs hst hcv
    (fun i hi => by simpa using Code.all_instrs hlv i hi) (fun _ => MxSame.of_fun (mxFun_of hmx)) hrb' hp hr
    (tailOk_of _ _ _) (xs_of _ _) (fun e => absurd e hne) (fun _ _ e => absurd e hne) (gs_of _ _)).2

/-- `scrubRegM`, with the stack wiped in the chunks `cs` (`scrubCodeMC_noResidue`). -/
def scrubRegMC {api : Api} (r : Registration api target) (v : VecLevel) (ks cs : List Nat)
    (hcs : cs.sum = r.stack) (hcv : ∀ b ∈ cs, 0 < b ∧ b < 4096 ∧ b % 8 = 0)
    (hd : r.code.x86_64Depth ≤ r.stack) (hst : r.stack + 8 < 2 ^ 64)
    (hlv : r.code.all (fun i => decide (i.vecLevelR ≤ v.level)) = true)
    (hmx : (mxClass r.code).isSome = true)
    (hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨ api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (hres : ResOk r.code r.contract r.stack ks cs)
    (hw : r.written = []) (hne : v ≠ .evex) : Registration api target where
  suffix := r.suffix
  consts := r.consts
  tables := r.tables
  stack := r.stack
  code := scrub v (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
    (xsOf r.code ks) (psOf ks) (gsOf Taint.clobbers r.code) ks cs r.code
  contract := r.contract
  verified := by
    obtain ⟨pre, post, leak, e⟩ := r.ofSig
    have hv := r.verified
    have hp := hpost
    have hr := hres
    rw [e] at hv hp hr ⊢
    have hrb' := hrb
    rw [← withMode_ptrBits ((abi.withConsts r.consts).withTables api.sig r.tables) api.pubMode] at hrb' hp ⊢
    exact (Verified.scrubM (ScrubAbi.of r.consts api.sig r.tables api.pubMode) hv (SpSafe.of_all r.spSafe) hd
      hcs hst hcv
      (fun i hi => by simpa using Code.all_instrs hlv i hi) (fun _ => MxSame.of_fun (mxFun_of hmx)) hrb' hp hr
      (tailOk_of _ _ _) (xs_of _ _) (fun e => absurd e hne) (fun _ _ e => absurd e hne) (gs_of _ _)).1
  ofApi := r.ofApi
  ofSig := r.ofSig
  spSafe := scrub_spSafe v _ _ _ _ _ _ (tailOk_of 0 r.code ks).psOk (tailOk_of 0 r.code ks).gsOk r.spSafe
  written := r.written
  writtenOk := by
    rw [hw]; exact fun _ _ _ _ _ => True.intro
  extra := r.extra
  vendor := r.vendor
  notWith := r.notWith
  residue := some ⟨scrubCodeMC_noResidue r v ks cs hcs hcv hd hst hlv hmx hrb hpost hres hne⟩

/-- `scrubCodeMC_noResidue`, with the wipe's stores chosen by `w` (`scrubW`). -/
theorem scrubCodeMCW_noResidue {api : Api} (r : Registration api target) (v : VecLevel) (w : Bool)
    (hwd : w = true → v ≠ .sse) (ks cs : List Nat)
    (hcs : cs.sum = r.stack) (hcv : ∀ b ∈ cs, 0 < b ∧ b < 4096 ∧ b % 8 = 0)
    (hd : r.code.x86_64Depth ≤ r.stack) (hst : r.stack + 8 < 2 ^ 64)
    (hlv : r.code.all (fun i => decide (i.vecLevelR ≤ v.level)) = true)
    (hmx : (mxClass r.code).isSome = true)
    (hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨ api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (hres : ResOk r.code r.contract r.stack ks cs) (hne : v ≠ .evex) :
    NoResidue (scrubW v w (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
      (xsOf r.code ks) (psOf ks) (gsOf Taint.clobbers r.code) ks cs r.code) r.contract
      (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits) := by
  obtain ⟨pre, post, leak, e⟩ := r.ofSig
  have hv := r.verified
  have hp := hpost
  have hr := hres
  rw [e] at hv hp hr ⊢
  have hrb' := hrb
  rw [← withMode_ptrBits ((abi.withConsts r.consts).withTables api.sig r.tables) api.pubMode] at hrb' hp ⊢
  exact (Verified.scrubMW hwd (ScrubAbi.of r.consts api.sig r.tables api.pubMode) hv (SpSafe.of_all r.spSafe) hd
    hcs hst hcv
    (fun i hi => by simpa using Code.all_instrs hlv i hi) (fun _ => MxSame.of_fun (mxFun_of hmx)) hrb' hp hr
    (tailOk_of _ _ _) (xs_of _ _) (fun e => absurd e hne) (fun _ _ e => absurd e hne) (gs_of _ _)).2

/-- `scrubRegMC`, with the wipe's stores chosen by `w` (`scrubW`). -/
def scrubRegMCW {api : Api} (r : Registration api target) (v : VecLevel) (w : Bool)
    (hwd : w = true → v ≠ .sse) (ks cs : List Nat)
    (hcs : cs.sum = r.stack) (hcv : ∀ b ∈ cs, 0 < b ∧ b < 4096 ∧ b % 8 = 0)
    (hd : r.code.x86_64Depth ≤ r.stack) (hst : r.stack + 8 < 2 ^ 64)
    (hlv : r.code.all (fun i => decide (i.vecLevelR ≤ v.level)) = true)
    (hmx : (mxClass r.code).isSome = true)
    (hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨ api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (hres : ResOk r.code r.contract r.stack ks cs)
    (hw : r.written = []) (hne : v ≠ .evex) : Registration api target where
  suffix := r.suffix
  consts := r.consts
  tables := r.tables
  stack := r.stack
  code := scrubW v w (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
    (xsOf r.code ks) (psOf ks) (gsOf Taint.clobbers r.code) ks cs r.code
  contract := r.contract
  verified := by
    obtain ⟨pre, post, leak, e⟩ := r.ofSig
    have hv := r.verified
    have hp := hpost
    have hr := hres
    rw [e] at hv hp hr ⊢
    have hrb' := hrb
    rw [← withMode_ptrBits ((abi.withConsts r.consts).withTables api.sig r.tables) api.pubMode] at hrb' hp ⊢
    exact (Verified.scrubMW hwd (ScrubAbi.of r.consts api.sig r.tables api.pubMode) hv (SpSafe.of_all r.spSafe) hd
      hcs hst hcv
      (fun i hi => by simpa using Code.all_instrs hlv i hi) (fun _ => MxSame.of_fun (mxFun_of hmx)) hrb' hp hr
      (tailOk_of _ _ _) (xs_of _ _) (fun e => absurd e hne) (fun _ _ e => absurd e hne) (gs_of _ _)).1
  ofApi := r.ofApi
  ofSig := r.ofSig
  spSafe := scrubW_spSafe v w _ _ _ _ _ _ (tailOk_of 0 r.code ks).psOk (tailOk_of 0 r.code ks).gsOk r.spSafe
  written := r.written
  writtenOk := by
    rw [hw]; exact fun _ _ _ _ _ => True.intro
  extra := r.extra
  vendor := r.vendor
  notWith := r.notWith
  residue := some ⟨scrubCodeMCW_noResidue r v w hwd ks cs hcs hcv hd hst hlv hmx hrb hpost hres hne⟩

end VG.X86_64.Scrub

namespace VG.X86_64.RScrub

open VG.X86_64 VG.X86_64.Taint VG.X86_64.RTaint VG.X86_64.Scrub VG.Impl.Scrub.X86_64

/-- `withScrubRes`, with the stack wiped in the chunks `cs` (from the top;
`Scrub.scrubRegMC`), which `hcs` and `hcv` check; with `wide` false, 16
bytes at a time at every level (`Scrub.scrubRegMCW`), so that the stores
of granules 16 bytes aligned never split a cache line. -/
def withScrubResC {api : Api} (r : Registration api target)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (ks cs : List Nat) (hres : ResOk r.code r.contract r.stack ks cs) (wide : Bool := true) :
    Registration api target :=
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
    if wide then
      scrubRegMC r v ks cs hcs (fun b hb => of_decide_eq_true (List.all_eq_true.mp hcv b hb)) hd hst
        ((Code.allOnce_eq _ r.code).symm.trans hlv) (mxClassOnce_eq r.code ▸ hmx) hrb hpost hres hw (levelFor_ne _)
    else
      scrubRegMCW r v false (fun h => Bool.noConfusion h) ks cs hcs
        (fun b hb => of_decide_eq_true (List.all_eq_true.mp hcv b hb)) hd hst
        ((Code.allOnce_eq _ r.code).symm.trans hlv) (mxClassOnce_eq r.code ▸ hmx) hrb hpost hres hw (levelFor_ne _)
  else r else r else r else r else r else r else r else r

end VG.X86_64.RScrub
