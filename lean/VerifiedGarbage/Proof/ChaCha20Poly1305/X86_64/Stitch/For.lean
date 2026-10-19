module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Short.Correct
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Verified
public import VerifiedGarbage.Proof.Framework.Cold
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Short.Correct
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Verified
meta import VerifiedGarbage.Proof.Framework.Cold

@[expose] public section

/-!
# ChaCha20-Poly1305 for short records (x86-64): the entry test

`Stitch.sealStitchedS` and `openStitchedS` test the lengths (`shortTest`):
1 to 448 bytes of data and fewer than 16 of additional data run `sealShort`
(`openShort`), the rest `sealStitched` (`openStitched`). The test changes
only `rax`, `r10` and the flags, which the contracts do not read
(`FlagsOnly`), and both runs of the constant-time proof take the same
branch, the lengths being public.
-/


namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.ChaCha20Poly1305.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch

/-- The lengths `sealShort` and `openShort` take. -/
abbrev ShortLen (s : State) : Prop := 1 ≤ (s.gpr .r9).toNat ∧ (s.gpr .r9).toNat ≤ 448 ∧ (s.gpr .rcx).toNat < 16

theorem short_iff (x : BitVec 64) : (x - 1#64).toNat < 448 ↔ 1 ≤ x.toNat ∧ x.toNat ≤ 448 := by
  bv_omega

theorem sbb_and (a b : BitVec 64) (c d : Bool) :
    ((a - a - BitVec.setWidth 64 (BitVec.ofBool c)) &&& (b - b - BitVec.setWidth 64 (BitVec.ofBool d)) == 0) =
      !(c && d) := by
  cases c <;> cases d <;> simp

theorem shortTest_ok (s : State) :
    WP isa (.block shortTest) s fun t => isa.eval .ne t = some (decide (ShortLen s)) ∧ FlagsOnly s t := by
  apply WP.of_runBlock
  have x1 : BitVec.signExtend 64 (1 : BitVec 32) = 1#64 := by decide
  have x448 : BitVec.signExtend 64 (448 : BitVec 32) = 448#64 := by decide
  have x16 : BitVec.signExtend 64 (16 : BitVec 32) = 16#64 := by decide
  have hw := short_iff (s.gpr .r9)
  simp only [shortTest, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, x1, x448, x16,
    Option.bind_some, Option.map_some, gpr_arithFlags, cf_arithFlags, gpr_setReg, eval, zf_arithFlags,
    zf_setReg, Option.some.injEq, exists_eq_left', ↓reduceIte, reduceCtorEq]
  refine ⟨?_, fun r h₁ h₂ => ?_, rfl, rfl, rfl, rfl⟩
  · rw [sbb_and, Bool.not_not, show (448#64).toNat = 448 from rfl, show (16#64).toNat = 16 from rfl,
      ← Bool.decide_and, decide_eq_decide, hw, and_assoc]
  · simp only [gpr_arithFlags, gpr_setReg, h₁, h₂, ite_false]

/-! ## The short records' code, from the entry -/

/-- The short branch of `seal`. -/
def sealShortE (x : Impl.ChaCha20.X86_64.Callee) : Prog isa := .seq (.block entry) (sealShort x)

/-- The short branch of `open`. -/
def openShortE (x : Impl.ChaCha20.X86_64.Callee) : Prog isa := .seq (.block entry) (openShort x)

theorem sealShortE_mx (x : Impl.ChaCha20.X86_64.Callee) (hw : x.wide = 5) :
    (sealShortE x).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [sealShortE, sealShort, hw]
  generalize x.vl = vl
  cases vl <;> decide +kernel

theorem openShortE_mx (x : Impl.ChaCha20.X86_64.Callee) (hw : x.wide = 5) :
    (openShortE x).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [openShortE, openShort, hw]
  generalize x.vl = vl
  cases vl <;> decide +kernel

theorem sealShortE_ok (x : Impl.ChaCha20.X86_64.Callee) (hw : x.wide = 5) {s₀ : State} (hp : APre true s₀)
    (hs : ShortLen s₀) : WP isa (sealShortE x) s₀ fun s' => abiPreserved s₀ s' ∧ sealX86_64.post s₀ s' := by
  unfold sealShortE
  refine WP.mono_mx (Q := fun s' => (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) ∧ Frame (Short.allR s₀) s₀.mem s'.mem ∧
      sealX86_64.post s₀ s') (sealShortE_mx x hw) (WP.seq (WP.mono (entry_ok hp) fun s e => ?_)) fun s' h mx => ?_
  · subst e
    exact Short.sealShort_ok x (.inr (.inl hw)) hp hs.2.1 hs.2.2
  · obtain ⟨cs, fr, post⟩ := h
    refine ⟨⟨cs, fr.readW (Region.contains_self _ _) (by unfold Short.allR; rdisj_all) (by decide), ?_⟩, post⟩
    rw [mx]

theorem openShortE_ok (x : Impl.ChaCha20.X86_64.Callee) (hw : x.wide = 5) {s₀ : State} (hp : APre false s₀)
    (hs : ShortLen s₀) : WP isa (openShortE x) s₀ fun s' => abiPreserved s₀ s' ∧ openX86_64.post s₀ s' := by
  unfold openShortE
  refine WP.mono_mx (Q := fun s' => (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) ∧ Frame (Short.allR s₀) s₀.mem s'.mem ∧
      openX86_64.post s₀ s') (openShortE_mx x hw) (WP.seq (WP.mono (entry_ok hp) fun s e => ?_)) fun s' h mx => ?_
  · subst e
    exact Short.openShort_ok x (.inr (.inl hw)) hp hs.2.1 hs.2.2
  · obtain ⟨cs, fr, post⟩ := h
    refine ⟨⟨cs, fr.readW (Region.contains_self _ _) (by unfold Short.allR; rdisj_all) (by decide), ?_⟩, post⟩
    rw [mx]

theorem sealShort_taint (x : Impl.ChaCha20.X86_64.Callee) (hw : x.wide = 5) :
    ∃ h, (taintS.check (τ₀ true) (sealShort x) h).isSome = true := by
  simp only [sealShort, hw]
  generalize x.vl = vl
  cases vl <;> exact ⟨_, by taint_decide⟩

theorem openShort_taint (x : Impl.ChaCha20.X86_64.Callee) (hw : x.wide = 5) :
    ∃ h, (taintS.check (τ₀ false) (openShort x) h).isSome = true := by
  simp only [openShort, hw]
  generalize x.vl = vl
  cases vl <;> exact ⟨_, by taint_decide⟩

theorem sealShortE_ct (x : Impl.ChaCha20.X86_64.Callee) (hw : x.wide = 5) :
    ConstantTime isa sealX86_64.pre sealX86_64.pub (sealShortE x) := by
  obtain ⟨_, hS⟩ := sealShort_taint x hw
  intro s₀ s₀' _ _ _ _ h₁ h₂ hq e₁ e₂
  have hp := APre.of _ h₁
  have hp' := APre.of _ h₂
  exact ((entry_rel hp hp' hq).seq (RelCT.taint (A := taintS)
    (P := fun s₁ s₂ => s₁ = entryS s₀ ∧ s₂ = entryS s₀') (τ₀ true)
    (fun _ _ h => by rw [h.1, h.2]; exact agree₀ hp hp' hq) hS) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem openShortE_ct (x : Impl.ChaCha20.X86_64.Callee) (hw : x.wide = 5) :
    ConstantTime isa openX86_64.pre openX86_64.pub (openShortE x) := by
  obtain ⟨_, hS⟩ := openShort_taint x hw
  intro s₀ s₀' _ _ _ _ h₁ h₂ hq e₁ e₂
  have hp := APre.of _ h₁
  have hp' := APre.of _ h₂
  exact ((entry_rel hp hp' hq).seq (RelCT.taint (A := taintS)
    (P := fun s₁ s₂ => s₁ = entryS s₀ ∧ s₂ = entryS s₀') (τ₀ false)
    (fun _ _ h => by rw [h.1, h.2]; exact agree₀ hp hp' hq) hS) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem sealShortE_spSafe (x : Impl.ChaCha20.X86_64.Callee) (hw : x.wide = 5) :
    (sealShortE x).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [sealShortE, sealShort, hw]
  generalize x.vl = vl
  cases vl <;> exact Code.all_of_allInstrs (by decide +kernel)

theorem openShortE_spSafe (x : Impl.ChaCha20.X86_64.Callee) (hw : x.wide = 5) :
    (openShortE x).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [openShortE, openShort, hw]
  generalize x.vl = vl
  cases vl <;> exact Code.all_of_allInstrs (by decide +kernel)

theorem sealShortE_xdepth (x : Impl.ChaCha20.X86_64.Callee) (hw : x.wide = 5) :
    (sealShortE x).x86_64Depth = 0 := by
  simp only [sealShortE, sealShort, hw]
  generalize x.vl = vl
  cases vl <;> decide +kernel

theorem openShortE_xdepth (x : Impl.ChaCha20.X86_64.Callee) (hw : x.wide = 5) :
    (openShortE x).x86_64Depth = 0 := by
  simp only [openShortE, openShort, hw]
  generalize x.vl = vl
  cases vl <;> decide +kernel

/-! ## The test and the branch -/

/-- `seal` with the short records' test in front of `big`. -/
abbrev sealWith (x : Impl.ChaCha20.X86_64.Callee) (big : Prog isa) : Prog isa :=
  .seq (.block shortTest) (Code.iteCold .ne (sealShortE x) big)

/-- `open` with the short records' test in front of `big`. -/
abbrev openWith (x : Impl.ChaCha20.X86_64.Callee) (big : Prog isa) : Prog isa :=
  .seq (.block shortTest) (Code.iteCold .ne (openShortE x) big)

theorem sealWith_ok (x : Impl.ChaCha20.X86_64.Callee) (hw : x.wide = 5) {big : Prog isa}
    (hb : ∀ s, sealX86_64.pre s → ∃ t s', Exec isa big s t s' ∧ abiPreserved s s' ∧ sealX86_64.post s s')
    (s : State) (hs : sealX86_64.pre s) :
    ∃ t s', Exec isa (sealWith x big) s t s' ∧ abiPreserved s s' ∧ sealX86_64.post s s' := by
  have hw' : WP isa (sealWith x big) s fun z => abiPreserved s z ∧ sealX86_64.post s z := by
    refine WP.seq (WP.mono (shortTest_ok s) fun e ⟨he, hf⟩ => ?_)
    refine WP.iteCold_iff.mpr (WP.ite _ he (fun h => ?_) (fun _ => ?_))
    · have hl : ShortLen e := by
        simp only [decide_eq_true_eq] at h
        simp only [ShortLen, hf.r9, hf.rcx]; exact h
      exact WP.mono (sealShortE_ok x hw (APre.of e (hf.pre hs)) hl) fun z ⟨ha, hp⟩ => ⟨hf.abi ha, hf.post hp⟩
    · obtain ⟨t, s', ex, ha, hp⟩ := hb e (hf.pre hs)
      exact ⟨t, s', ex, hf.abi ha, hf.post hp⟩
  obtain ⟨t, s', he, hq⟩ := hw'
  exact ⟨t, s', he, hq⟩

theorem openWith_ok (x : Impl.ChaCha20.X86_64.Callee) (hw : x.wide = 5) {big : Prog isa}
    (hb : ∀ s, openX86_64.pre s → ∃ t s', Exec isa big s t s' ∧ abiPreserved s s' ∧ openX86_64.post s s')
    (s : State) (hs : openX86_64.pre s) :
    ∃ t s', Exec isa (openWith x big) s t s' ∧ abiPreserved s s' ∧ openX86_64.post s s' := by
  have hw' : WP isa (openWith x big) s fun z => abiPreserved s z ∧ openX86_64.post s z := by
    refine WP.seq (WP.mono (shortTest_ok s) fun e ⟨he, hf⟩ => ?_)
    refine WP.iteCold_iff.mpr (WP.ite _ he (fun h => ?_) (fun _ => ?_))
    · have hl : ShortLen e := by
        simp only [decide_eq_true_eq] at h
        simp only [ShortLen, hf.r9, hf.rcx]; exact h
      exact WP.mono (openShortE_ok x hw (APre.of e (hf.preO hs)) hl) fun z ⟨ha, hp⟩ => ⟨hf.abi ha, hf.postO hp⟩
    · obtain ⟨t, s', ex, ha, hp⟩ := hb e (hf.preO hs)
      exact ⟨t, s', ex, hf.abi ha, hf.postO hp⟩
  obtain ⟨t, s', he, hq⟩ := hw'
  exact ⟨t, s', he, hq⟩

/-- What the test leaves, from `s`. -/
def Tested (s t : State) : Prop := isa.eval .ne t = some (decide (ShortLen s)) ∧ FlagsOnly s t

theorem shortTest_taint : ∃ hc, (taint.check (Taint.ofRegs [.r9, .rcx]) (.block shortTest) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem sealWith_ct (x : Impl.ChaCha20.X86_64.Callee) (hw : x.wide = 5) {big : Prog isa}
    (hb : ConstantTime isa sealX86_64.pre sealX86_64.pub big) :
    ConstantTime isa sealX86_64.pre sealX86_64.pub (sealWith x big) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  have hblk : RelCT isa PP (.block shortTest) fun _ _ => True := by
    obtain ⟨_, hc⟩ := shortTest_taint
    exact RelCT.taint (A := taint) (Taint.ofRegs [.r9, .rcx]) (fun s₁ s₂ h => Taint.agree_ofRegs (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.2.2.2.2.2.2.2.1
      · exact h.2.2.2.2.2.1)) hc
  refine RelCT.seq (RelCT.wpDep (F := Tested) hblk fun s₁ s₂ _ => ⟨shortTest_ok s₁, shortTest_ok s₂⟩) ?_
  have cmp : ∀ {c : Prog isa}, ConstantTime isa sealX86_64.pre sealX86_64.pub c → ∀ {R : State → State → Prop},
      (∀ a b, R a b → ∃ σ₁ σ₂, PP σ₁ σ₂ ∧ Tested σ₁ a ∧ Tested σ₂ b) → RelCT isa R c fun _ _ => True := by
    intro c hc R hR a b t₁ t₂ a' b' hr e₁ e₂
    obtain ⟨σ₁, σ₂, ⟨p₁, p₂, hp⟩, ⟨_, f₁⟩, ⟨_, f₂⟩⟩ := hR a b hr
    exact ⟨hc _ _ _ _ _ _ (f₁.pre p₁) (f₂.pre p₂) (FlagsOnly.pub f₁ f₂ hp) e₁ e₂, trivial⟩
  refine RelCT.iteCold (RelCT.ite (fun a b ⟨_, σ₁, σ₂, ⟨_, _, hp⟩, ⟨e₁, _⟩, ⟨e₂, _⟩⟩ => ?_)
    (cmp (sealShortE_ct x hw) fun a b ⟨⟨_, σ₁, σ₂, hp, h₁, h₂⟩, _⟩ => ⟨σ₁, σ₂, hp, h₁, h₂⟩)
    (cmp hb fun a b ⟨⟨_, σ₁, σ₂, hp, h₁, h₂⟩, _⟩ => ⟨σ₁, σ₂, hp, h₁, h₂⟩))
  have h9 : σ₁.gpr .r9 = σ₂.gpr .r9 := hp.2.2.2.2.2.1
  have hc : σ₁.gpr .rcx = σ₂.gpr .rcx := hp.2.2.2.1
  exact e₁.trans ((congrArg some (by simp only [ShortLen, h9, hc])).trans e₂.symm)

theorem openWith_ct (x : Impl.ChaCha20.X86_64.Callee) (hw : x.wide = 5) {big : Prog isa}
    (hb : ConstantTime isa openX86_64.pre openX86_64.pub big) :
    ConstantTime isa openX86_64.pre openX86_64.pub (openWith x big) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  have hblk : RelCT isa PPO (.block shortTest) fun _ _ => True := by
    obtain ⟨_, hc⟩ := shortTest_taint
    exact RelCT.taint (A := taint) (Taint.ofRegs [.r9, .rcx]) (fun s₁ s₂ h => Taint.agree_ofRegs (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.2.2.2.2.2.2.2.1
      · exact h.2.2.2.2.2.1)) hc
  refine RelCT.seq (RelCT.wpDep (F := Tested) hblk fun s₁ s₂ _ => ⟨shortTest_ok s₁, shortTest_ok s₂⟩) ?_
  have cmp : ∀ {c : Prog isa}, ConstantTime isa openX86_64.pre openX86_64.pub c → ∀ {R : State → State → Prop},
      (∀ a b, R a b → ∃ σ₁ σ₂, PPO σ₁ σ₂ ∧ Tested σ₁ a ∧ Tested σ₂ b) → RelCT isa R c fun _ _ => True := by
    intro c hc R hR a b t₁ t₂ a' b' hr e₁ e₂
    obtain ⟨σ₁, σ₂, ⟨p₁, p₂, hp⟩, ⟨_, f₁⟩, ⟨_, f₂⟩⟩ := hR a b hr
    exact ⟨hc _ _ _ _ _ _ (f₁.preO p₁) (f₂.preO p₂) (FlagsOnly.pubO f₁ f₂ hp) e₁ e₂, trivial⟩
  refine RelCT.iteCold (RelCT.ite (fun a b ⟨_, σ₁, σ₂, ⟨_, _, hp⟩, ⟨e₁, _⟩, ⟨e₂, _⟩⟩ => ?_)
    (cmp (openShortE_ct x hw) fun a b ⟨⟨_, σ₁, σ₂, hp, h₁, h₂⟩, _⟩ => ⟨σ₁, σ₂, hp, h₁, h₂⟩)
    (cmp hb fun a b ⟨⟨_, σ₁, σ₂, hp, h₁, h₂⟩, _⟩ => ⟨σ₁, σ₂, hp, h₁, h₂⟩))
  have h9 : σ₁.gpr .r9 = σ₂.gpr .r9 := hp.2.2.2.2.2.1
  have hc : σ₁.gpr .rcx = σ₂.gpr .rcx := hp.2.2.2.1
  exact e₁.trans ((congrArg some (by simp only [ShortLen, h9, hc])).trans e₂.symm)

theorem sealWith_spSafe (x : Impl.ChaCha20.X86_64.Callee) (hw : x.wide = 5) {big : Prog isa}
    (hb : big.all (fun i => !X86_64.isa.writesSp i) = true) :
    (sealWith x big).all (fun i => !X86_64.isa.writesSp i) = true := by
  have h := sealShortE_spSafe x hw
  simp only [Code.iteCold, Code.all, hb, h, Bool.and_true]
  decide

theorem openWith_spSafe (x : Impl.ChaCha20.X86_64.Callee) (hw : x.wide = 5) {big : Prog isa}
    (hb : big.all (fun i => !X86_64.isa.writesSp i) = true) :
    (openWith x big).all (fun i => !X86_64.isa.writesSp i) = true := by
  have h := openShortE_spSafe x hw
  simp only [Code.iteCold, Code.all, hb, h, Bool.and_true]
  decide

theorem sealWith_xdepth (x : Impl.ChaCha20.X86_64.Callee) (hw : x.wide = 5) {big : Prog isa}
    (hb : big.x86_64Depth ≤ 24) : (sealWith x big).x86_64Depth ≤ 24 := by
  have h := sealShortE_xdepth x hw
  simp only [Code.iteCold, Code.x86_64Depth, h, Nat.max_le] at hb ⊢
  omega

theorem openWith_xdepth (x : Impl.ChaCha20.X86_64.Callee) (hw : x.wide = 5) {big : Prog isa}
    (hb : big.x86_64Depth ≤ 24) : (openWith x big).x86_64Depth ≤ 24 := by
  have h := openShortE_xdepth x hw
  simp only [Code.iteCold, Code.x86_64Depth, h, Nat.max_le] at hb ⊢
  omega

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch

/-!
# ChaCha20 and Poly1305 together (x86-64): `sealFor` and `openFor`

The `seal` and `open` instances use: with the AVX2 implementation of
`vg_poly1305_blocks`, the stitched code behind the short records' test
(`sealStitchedS`, `openStitchedS`); with the AVX-512 one, `sealSmall` and
`openSmall`; otherwise `seal` and `open`.
-/


namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch

/-! ## The AVX2 code with the short records' path -/

theorem sealW_verified (v : Proof.ChaCha20.X86_64.XorImpl) (hv : v.poly = .avx2) :
    Verified X86_64.target (sealWith { v.callee with pass := 512 } (sealStitched { v.callee with pass := 512 } v.poly))
      (sealScratchContract X86_64.abi 212 24) :=
  Verified.of_correct (sealWith_ok _ (avx2_of v hv).2.2 (sealS_ok v hv))
    (sealWith_ct _ (avx2_of v hv).2.2 (sealS_ct v hv)) (by
    sig_implies [Proof.ChaCha20Poly1305.sealScratchContract, Proof.ChaCha20Poly1305.sealScratchSig,
      Spec.ChaCha20Poly1305.sealPost, Proof.ChaCha20Poly1305.sealX86_64,
      Proof.ChaCha20Poly1305.preX86_64, Proof.ChaCha20Poly1305.pubX86_64, X86_64.abi, X86_64.stackArg,
      X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]
      [sealSat] using sealSat)

theorem sealW_framed (v : Proof.ChaCha20.X86_64.XorImpl) (hv : v.poly = .avx2) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratchWipedX 1720 1 42
        (sealWith { v.callee with pass := 512 } (sealStitched { v.callee with pass := 512 } v.poly)))
      (Spec.ChaCha20Poly1305.sealContract X86_64.abi 1744) :=
  X86_64.Verified.stackArgScratchWipedX (sig := Spec.ChaCha20Poly1305.sealSig) (nm := "work") (e := .u64)
    (n := 212) (post := Spec.ChaCha20Poly1305.sealPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 1720) (k := 42) (sealW_verified v hv) (by decide) (by decide) (by decide)
    (sealWith_spSafe _ (avx2_of v hv).2.2 (sealS_spSafe v hv)) (sealWith_xdepth _ (avx2_of v hv).2.2 (sealS_xdepth v))
    (by decide) (pre_local _ _) (sealPost_local _) (sealPost_out _) sealFrameSat_pre

theorem openW_verified (v : Proof.ChaCha20.X86_64.XorImpl) (hv : v.poly = .avx2) :
    Verified X86_64.target (openWith v.callee (openStitched v.callee v.poly)) (openScratchContract X86_64.abi 212 24) :=
  Verified.of_correct (openWith_ok _ (avx2_of v hv).2.2 (openS_ok v hv))
    (openWith_ct _ (avx2_of v hv).2.2 (openS_ct v hv)) openS_implies

theorem openW_framed (v : Proof.ChaCha20.X86_64.XorImpl) (hv : v.poly = .avx2) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratchWipedX 1720 1 42 (openWith v.callee (openStitched v.callee v.poly)))
      (Spec.ChaCha20Poly1305.openContract X86_64.abi 1744) :=
  X86_64.Verified.stackArgScratchWipedX (sig := Spec.ChaCha20Poly1305.openSig) (nm := "work") (e := .u64)
    (n := 212) (post := Spec.ChaCha20Poly1305.openPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 1720) (k := 42) (openW_verified v hv) (by decide) (by decide) (by decide)
    (openWith_spSafe _ (avx2_of v hv).2.2 (openS_spSafe v hv)) (openWith_xdepth _ (avx2_of v hv).2.2 (openS_xdepth v))
    (by decide) (pre_local _ _) (openPost_local _) (openPost_out _) openFrameSat_pre

/-! ## The `seal` of an instance -/

theorem sealFor_spSafe (v : Proof.ChaCha20.X86_64.XorImpl) :
    (sealFor v.callee v.poly).all (fun i => !X86_64.isa.writesSp i) = true := by
  have h₁ := seal_spSafe v
  cases hb : v.poly with
  | avx2 =>
    have h₂ := sealWith_spSafe { v.callee with pass := 512 } (avx2_of v hb).2.2 (sealS_spSafe v hb)
    rw [hb] at h₂; exact h₂
  | avx512 =>
    rw [hb] at h₁
    have := sealSmall_spSafe v.small v.small_poly h₁
    rwa [Proof.ChaCha20.X86_64.XorImpl.small_callee] at this
  | _ => rw [hb] at h₁; exact h₁

theorem sealFor_xdepth (v : Proof.ChaCha20.X86_64.XorImpl) : (sealFor v.callee v.poly).x86_64Depth ≤ 24 := by
  have h₁ := seal_xdepth v
  cases hb : v.poly with
  | avx2 =>
    have h₂ := sealWith_xdepth { v.callee with pass := 512 } (avx2_of v hb).2.2 (sealS_xdepth v)
    rw [hb] at h₂; exact h₂
  | avx512 =>
    rw [hb] at h₁
    have := sealSmall_xdepth v.small v.small_poly h₁
    rwa [Proof.ChaCha20.X86_64.XorImpl.small_callee] at this
  | _ => rw [hb] at h₁; exact h₁

theorem sealFor_framed (v : Proof.ChaCha20.X86_64.XorImpl) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratchWipedX 1720 1 42 (sealFor v.callee v.poly))
      (Spec.ChaCha20Poly1305.sealContract X86_64.abi 1744) := by
  have h₁ := seal_framed v
  cases hb : v.poly with
  | avx2 => have h₂ := sealW_framed v hb; rw [hb] at h₂; exact h₂
  | avx512 =>
    have ho := seal_ok v
    have hc := seal_ct v
    have hs := seal_spSafe v
    have hd := seal_xdepth v
    rw [hb] at ho hc hs hd
    have hv := sealSmall_verified v.small v.small_poly ho hc
    have hs' := sealSmall_spSafe v.small v.small_poly hs
    have hd' := sealSmall_xdepth v.small v.small_poly hd
    rw [Proof.ChaCha20.X86_64.XorImpl.small_callee] at hv hs' hd'
    exact X86_64.Verified.stackArgScratchWipedX (sig := Spec.ChaCha20Poly1305.sealSig) (nm := "work") (e := .u64)
      (n := 212) (post := Spec.ChaCha20Poly1305.sealPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
      (bytes := 1720) (k := 42) hv (by decide) (by decide) (by decide) hs' hd' (by decide) (pre_local _ _) (sealPost_local _) (sealPost_out _)
      sealFrameSat_pre
  | _ => rw [hb] at h₁; exact h₁


/-! ## The `open` of an instance -/

theorem openFor_spSafe (v : Proof.ChaCha20.X86_64.XorImpl) :
    (openFor v.callee v.poly).all (fun i => !X86_64.isa.writesSp i) = true := by
  have h₁ := open_spSafe v
  cases hb : v.poly with
  | avx2 =>
    have h₂ := openWith_spSafe v.callee (avx2_of v hb).2.2 (openS_spSafe v hb)
    rw [hb] at h₂; exact h₂
  | avx512 =>
    rw [hb] at h₁
    have := openSmall_spSafe v.small v.small_poly h₁
    rwa [Proof.ChaCha20.X86_64.XorImpl.small_callee] at this
  | ifma =>
    rw [hb] at h₁
    have := openWin_spSafe Proof.ChaCha20.X86_64.XorImpl.avx512vl.small
      Proof.ChaCha20.X86_64.XorImpl.avx512vl.small_poly h₁
    rwa [Proof.ChaCha20.X86_64.XorImpl.small_callee] at this
  | _ => rw [hb] at h₁; exact h₁

theorem openFor_framed (v : Proof.ChaCha20.X86_64.XorImpl) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratchWipedX 1720 1 42 (openFor v.callee v.poly))
      (Spec.ChaCha20Poly1305.openContract X86_64.abi 1744) := by
  have h₁ := open_framed v
  cases hb : v.poly with
  | avx2 => have h₂ := openW_framed v hb; rw [hb] at h₂; exact h₂
  | avx512 =>
    have ho := open_ok v
    have hc := open_ct v
    have hs := open_spSafe v
    have hd := open_xdepth v
    rw [hb] at ho hc hs hd
    have hv := openSmall_verified v.small v.small_poly ho hc
    have hs' := openSmall_spSafe v.small v.small_poly hs
    have hd' := openSmall_xdepth v.small v.small_poly hd
    rw [Proof.ChaCha20.X86_64.XorImpl.small_callee] at hv hs' hd'
    exact X86_64.Verified.stackArgScratchWipedX (sig := Spec.ChaCha20Poly1305.openSig) (nm := "work") (e := .u64)
      (n := 212) (post := Spec.ChaCha20Poly1305.openPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
      (bytes := 1720) (k := 42) hv (by decide) (by decide) (by decide) hs' hd' (by decide) (pre_local _ _) (openPost_local _) (openPost_out _)
      openFrameSat_pre
  | ifma =>
    have ho := open_ok v
    have hc := open_ct v
    have hs := open_spSafe v
    have hd := open_xdepth v
    rw [hb] at ho hc hs hd
    have hp := Proof.ChaCha20.X86_64.XorImpl.avx512vl.small_poly
    have hv := openWin_verified _ hp ho hc
    have hs' := openWin_spSafe _ hp hs
    have hd' := openWin_xdepth _ hp hd
    rw [Proof.ChaCha20.X86_64.XorImpl.small_callee] at hv hs' hd'
    exact X86_64.Verified.stackArgScratchWipedX (sig := Spec.ChaCha20Poly1305.openSig) (nm := "work") (e := .u64)
      (n := 212) (post := Spec.ChaCha20Poly1305.openPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
      (bytes := 1720) (k := 42) hv (by decide) (by decide) (by decide) hs' hd' (by decide) (pre_local _ _) (openPost_local _) (openPost_out _)
      openFrameSat_pre
  | _ => rw [hb] at h₁; exact h₁


end VG.Proof.ChaCha20Poly1305.X86_64.Stitch
