import VerifiedGarbage.Proof.X448.X86.Main
import VerifiedGarbage.Proof.X448.X86.Runs
import VerifiedGarbage.Proof.X448.X86.Lit

/-!
# X448 on x86 (32-bit): constant time

The field functions' calls are related run by run (`CallCT.lean`), so the
whole function is too: the pieces of inline code by the taint analysis, from
what each run's correctness proof (`Main.lean`'s stages) says of its own state,
and the calls, the inversion's squarings and the ladder's iterations by
`RelCT`. `W F` relates two runs from entry states the contract relates, each
in a state `F` says of its own run.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

/-- Two entry states the constant-time statement relates. -/
def P₀ (σ₁ σ₂ : State) : Prop :=
  Proof.X448.x448X86.pre σ₁ ∧ Proof.X448.x448X86.pre σ₂ ∧ Proof.X448.x448X86.pub σ₁ σ₂

theorem P₀.base {σ₁ σ₂ : State} (h : P₀ σ₁ σ₂) : bs σ₁ = bs σ₂ := by
  simp only [bs, h.2.2.2.2.2.2]

theorem P₀.sp {σ₁ σ₂ : State} (h : P₀ σ₁ σ₂) : σ₁.gpr .esp = σ₂.gpr .esp := h.2.2.1

/-- Two runs, each in a state `F` says of its own run. -/
def W (F : State → State → Prop) (s₁ s₂ : State) : Prop :=
  ∃ σ₁ σ₂, P₀ σ₁ σ₂ ∧ F σ₁ s₁ ∧ F σ₂ s₂

/-- Code whose traces agree, with what each run's correctness says of it. -/
theorem W.then {F G : State → State → Prop} {R Q : State → State → Prop} {c : Prog isa}
    (htr : RelCT isa (W F) c R) (hw : ∀ σ s, Pre σ → F σ s → WP isa c s (G σ))
    (hq : ∀ σ₁ σ₂ t₁ t₂, P₀ σ₁ σ₂ → R t₁ t₂ → G σ₁ t₁ → G σ₂ t₂ → Q t₁ t₂) :
    RelCT isa (W F) c Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, hr⟩ := htr _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨σ₁, σ₂, hP, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, g₁⟩ := hw _ _ (Pre.of _ hP.1) f₁
  obtain ⟨_, u₂, x₂, g₂⟩ := hw _ _ (Pre.of _ hP.2.1) f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, hq _ _ _ _ hP hr g₁ g₂⟩

/-- As `then`, from runs that `P` relates, which `W F` relates too. -/
theorem W.then' {F G : State → State → Prop} {P R Q : State → State → Prop} {c : Prog isa}
    (hP : ∀ s₁ s₂, P s₁ s₂ → W F s₁ s₂)
    (htr : RelCT isa P c R) (hw : ∀ σ s, Pre σ → F σ s → WP isa c s (G σ))
    (hq : ∀ σ₁ σ₂ t₁ t₂, P₀ σ₁ σ₂ → R t₁ t₂ → G σ₁ t₁ → G σ₂ t₂ → Q t₁ t₂) :
    RelCT isa P c Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, hr⟩ := htr _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨σ₁, σ₂, hP', f₁, f₂⟩ := hP _ _ hp
  obtain ⟨_, u₁, x₁, g₁⟩ := hw _ _ (Pre.of _ hP'.1) f₁
  obtain ⟨_, u₂, x₂, g₂⟩ := hw _ _ (Pre.of _ hP'.2.1) f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, hq _ _ _ _ hP' hr g₁ g₂⟩

theorem W.step {F G : State → State → Prop} {R : State → State → Prop} {c : Prog isa}
    (htr : RelCT isa (W F) c R) (hw : ∀ σ s, Pre σ → F σ s → WP isa c s (G σ)) :
    RelCT isa (W F) c (W G) :=
  W.then htr hw fun _ _ _ _ hP _ g₁ g₂ => ⟨_, _, hP, g₁, g₂⟩

/-! ## Code reading the arguments -/

/-- The taint analysis starts with the stack arguments public, and the words
holding `out` and `scratch` known to be the base addresses of the writable
regions. -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [56, 8192], argLen := 20, argBases := [(4, 0), (16, 1)] }

theorem wf₀ {s : State} (hp : Pre s) : VG.X86.Taint.Wf τ₀ s := by
  have hsc := hp.sc_fit; have ho := hp.out_fit; have hs := hp.sp_fit
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hp.wr, τ₀], by simpa [hp.wr] using hp.out_sc, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega_using [hsc, ho]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega_using [hs]) hp.ret_out hp.args_out
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega_using [hs]) hp.ret_sc hp.args_sc
  · intro p hp'
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.X448.x448X86.pre s₁) (h₂ : Proof.X448.x448X86.pre s₂)
    (hpub : Proof.X448.x448X86.pub s₁ s₂) : VG.X86.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨hesp, a0, a1, a2, a3⟩ := hpub
  have hp₁ := Pre.of _ h₁; have hp₂ := Pre.of _ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ hp₁, wf₀ hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]; simp only [outR, a0, a3]
  · simp only [τ₀] at hk
    rw [show VG.X86.Taint.depth τ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq hp₁.sp_fit h4 hk, VG.X86.Taint.argByte_eq hp₂.sp_fit h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    have : (k - 4) / 4 = 0 ∨ (k - 4) / 4 = 1 ∨ (k - 4) / 4 = 2 ∨ (k - 4) / 4 = 3 := by omega_using [hk]
    rcases this with h | h | h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1
    · exact congrArg _ a2
    · exact congrArg _ a3


/-- What code reading the arguments needs of its run. -/
def AF (σ s : State) : Prop :=
  Scr s (bs σ) ∧ s.gpr .esp = σ.gpr .esp ∧ s.wr = σ.wr ∧ XFrame σ s.mem

/-- The taint analysis of code reading the arguments: `esp`, `edi` and the
arguments public. -/
def τf : VG.X86.Taint.T := { regs := .ofList [.esp, .edi], flags := false, argLen := 20 }

theorem byte_same {σ s : State} (hp : Pre σ) (h : AF σ s) {k : Nat} (h4 : 4 ≤ k) (hk : k < 20) :
    s.mem (VG.X86.Taint.argByte s k) = σ.mem (VG.X86.Taint.argByte σ k) := by
  have hs := hp.sp_fit
  have e : VG.X86.Taint.argByte s k = argAddr σ 0 + BitVec.ofNat 64 (k - 4) := by
    rw [argAddr_eq, addr_eq (by omega)]
    simp only [VG.X86.Taint.argByte, h.2.1]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega
  have hc : (argsR σ).Contains (VG.X86.Taint.argByte s k) 1 := by
    rw [e]; exact Offset.contains_base _ (by omega) (by omega)
  rw [h.2.2.2 _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) hr
    · exact hp.args_sc _ hc hr
    · exact hp.args_out _ hc hr
    · exact hp.stk_args _ hr hc)]
  simp only [VG.X86.Taint.argByte, h.2.1]

theorem wfF {σ s : State} (hp : Pre σ) (h : AF σ s) : VG.X86.Taint.Wf τf s := by
  have hs := hp.sp_fit
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨by rw [h.2.1]; exact hs, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim⟩
  rw [h.2.2.1, hp.wr, h.2.1]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) hp.ret_out hp.args_out
  · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) hp.ret_sc hp.args_sc

theorem agreeF {σ₁ σ₂ s₁ s₂ : State} (hP : P₀ σ₁ σ₂) (h₁ : AF σ₁ s₁) (h₂ : AF σ₂ s₂) :
    VG.X86.Taint.Agree τf s₁ s₂ := by
  have hp₁ := Pre.of _ hP.1
  have hp₂ := Pre.of _ hP.2.1
  have a := agree₀ hP.1 hP.2.1 hP.2.2
  have esp : s₁.gpr .esp = s₂.gpr .esp := h₁.2.1.trans (hP.sp.trans h₂.2.1.symm)
  have edi : s₁.gpr .edi = s₂.gpr .edi :=
    BitVec.setWidth_32_64_inj.mp (h₁.1.edi.trans (hP.base.trans h₂.1.edi.symm))
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, wfF hp₁ h₁, wfF hp₂ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => esp,
    fun k h4 hk => ?_⟩
  · simp only [τf, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact esp
    · exact edi
  · have := a.argMem k h4 hk
    simp only [τf, τ₀, VG.X86.Taint.depth, Nat.zero_add] at this hk ⊢
    rw [byte_same hp₁ h₁ h4 hk, byte_same hp₂ h₂ h4 hk]
    exact this

/-! ## The ladder -/

theorem stepHead_fin {s₀ s : State} {base : Addr} {k : Nat} {u : Spec.X448.Fe} {n : Nat} (hn : n < 448)
    (hbits : ∀ t < 448, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 (bit k t))
    (hi : LInv base k u s₀ s (n + 1)) :
    WP isa (.block stepHead) s fun t =>
      FInv base t ∧ t.gpr .esp = s.gpr .esp ∧ t.gpr .esi = BitVec.ofNat 32 n := by
  have hs := hi.scr
  have bitval : s.mem (off base (BITS + n)) = BitVec.ofNat 8 (bit k n) := by
    rw [hi.mem _ (by rw [ofs_off' base (by simp only [BITS]; omega)]; simp only [BITS]; omega)
      (by rw [ofs_off' base (by simp only [BITS]; omega)]; simp only [BITS]; omega)
      (by rw [ofs_off' base (by simp only [BITS]; omega)]; simp only [BITS, ACC]; omega)]
    exact hbits n hn
  rw [show stepHead = stepPre ++ (cswap X2 X3 ++ cswap Z2 Z3) by
      simp only [stepHead, stepPre, List.append_assoc], WP.block_append_iff]
  refine WP.mono (stepPre_ok hs hn hi.esi (by have := bit_le k n; omega)
    (by have := ladderAfter_swap_le k u (n := n + 1) (by omega); omega) bitval hi.swap)
    fun s₁ ⟨b₁, c₁, g₁, rd₁, wr₁, m₁⟩ => ?_
  have hs₁ : Scr s₁ base := ⟨by rw [g₁ _ (by decide)]; exact hs.edi,
    wr₁ ▸ hs.wr, by rw [g₁ _ (by decide)]; exact hs.nowrap⟩
  have out₁ : Outside base SWAP 4 s.mem s₁.mem := by
    rw [m₁]; exact writeW_outside _ _ _ (by decide)
  have bb₁ : BoundedEnv s₁.mem base := by
    intro i j hj
    rw [out₁.limbs (Or.inr (by simp only [slot, SWAP]; omega))
      (Nat.le_trans (slot_bound i) (by decide)) hj]
    exact hi.bounded i j hj
  refine WP.mono (swaps_ok hs₁ bb₁ c₁) fun s₂ ⟨k₂, bb₂, _⟩ => ?_
  have hc₁ : CallCtx s₁ base := hi.ctx.keep (g₁ _ (by decide))
  exact ⟨⟨k₂.scr hs₁, k₂.ctx hc₁, bb₂⟩, (k₂.regs.1 _ (by decide)).trans (g₁ _ (by decide)),
    (k₂.regs.1 _ (by decide)).trans b₁⟩

/-- `n + 1` iterations left. -/
def LadI (n : Nat) (σ s : State) : Prop := n < 448 ∧ ∃ s₂, Lad σ s₂ s (n + 1)

theorem Lad.agree {σ₁ σ₂ s₁ s₂ t₁ t₂ : State} {n : Nat} (hP : P₀ σ₁ σ₂) (h₁ : Lad σ₁ s₁ t₁ n)
    (h₂ : Lad σ₂ s₂ t₂ n) : VG.X86.Taint.Agree (τr [.esp, .esi, .edi]) t₁ t₂ := by
  refine agree_regs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h₁.sp.trans (hP.sp.trans h₂.sp.symm)
  · exact h₁.2.1.esi.trans h₂.2.1.esi.symm
  · exact BitVec.setWidth_32_64_inj.mp (h₁.2.1.scr.edi.trans (hP.base.trans h₂.2.1.scr.edi.symm))

theorem step_tr (n : Nat) : RelCT isa (W (LadI n)) step fun _ _ => True := by
  have head : RelCT isa (W (LadI n)) (.block stepHead) fun t₁ t₂ => ∃ base, RF base t₁ t₂ := by
    refine W.then (G := fun σ t => FInv (bs σ) t ∧ t.gpr .esp = σ.gpr .esp ∧ t.gpr .esi = BitVec.ofNat 32 n)
      (RelCT.taint (A := taint) (τr [.esp, .esi, .edi]) ?_ (by taint_decide)) ?_ ?_
    · rintro s₁ s₂ ⟨σ₁, σ₂, hP, ⟨-, _, l₁⟩, ⟨-, _, l₂⟩⟩
      exact Lad.agree hP l₁ l₂
    · rintro σ s - ⟨hn, s₂, m, L, f⟩
      exact WP.mono (stepHead_fin hn m.bits L) fun t ⟨fi, sp, si⟩ =>
        ⟨fi, sp.trans (Lad.sp ⟨m, L, f⟩), si⟩
    · rintro σ₁ σ₂ t₁ t₂ hP - ⟨f₁, p₁, i₁⟩ ⟨f₂, p₂, i₂⟩
      rw [hP.base] at f₁
      exact ⟨_, f₁, f₂, p₁.trans (hP.sp.trans p₂.symm)⟩
  rw [step, stepBody, ← stepFields_impl]
  refine RelCT.seq (RelCT.seq head ((RelCT.exists_ fun base => (ops_rel (base := base) stepFields).mono
    (fun _ _ h => h) fun t₁ t₂ (h : RF base t₁ t₂) => (⟨base, h⟩ : ∃ b, RF b t₁ t₂)))) ?_
  exact RelCT.taint (A := taint) (τr [.esp, .edi]) (fun _ _ ⟨_, h⟩ => h.agree) (by taint_decide)

theorem loop_rel : ∀ n, RelCT isa (W (LadI n)) (.loop step .ne) (W fun σ s => ∃ s₂, Lad σ s₂ s 0) := by
  refine RelCT.loop (M := isa) (fun n => W (LadI n)) fun n => ?_
  refine W.then (G := fun σ t => (n < 448 ∧ ∃ s₂, Lad σ s₂ t n) ∧ t.zf = some (decide (n = 0))) (step_tr n) ?_ ?_
  · rintro σ s - ⟨hn, s₂, m, L, f⟩
    refine WP.mono (xframe m.pre (NoSp.of_all (by lit_decide)) (by lit_decide)
      (Lad.sp ⟨m, L, f⟩) (Lad.wr ⟨m, L, f⟩) f (step_ok hn m.bits L)) fun t ⟨⟨l, z⟩, f'⟩ =>
      ⟨⟨hn, s₂, m, l, f'⟩, z⟩
  · rintro σ₁ σ₂ t₁ t₂ hP - ⟨l₁, z₁⟩ ⟨l₂, z₂⟩
    rw [eval_ne z₁, eval_ne z₂]
    refine ⟨rfl, fun hz => ⟨σ₁, σ₂, hP, ?_, ?_⟩, fun hz => ?_⟩
    · have : n = 0 := by simpa using hz
      subst this; exact l₁.2
    · have : n = 0 := by simpa using hz
      subst this; exact l₂.2
    · have hn0 : n ≠ 0 := fun h0 => by simp [h0] at hz
      obtain ⟨hn, a₁, m₁, L₁, f₁⟩ := l₁
      obtain ⟨-, a₂, m₂, L₂, f₂⟩ := l₂
      have e : n - 1 + 1 = n := by omega
      exact ⟨n - 1, by omega, σ₁, σ₂, hP, ⟨by omega, a₁, m₁, e ▸ L₁, f₁⟩, ⟨by omega, a₂, m₂, e ▸ L₂, f₂⟩⟩

theorem ladder_rel : RelCT isa (W Mid) ladder (W fun σ s => ∃ s₂, Lad σ s₂ s 0) := by
  refine RelCT.seq (W.step (G := LadI 447) (RelCT.taint (A := taint) (τr [])
    (fun _ _ _ => agree_regs fun _ h => (List.not_mem_nil h).elim) (by taint_decide)) ?_) (loop_rel 447)
  rintro σ s - m
  refine WP.mono (setCounter_ok s 448 (by decide)) fun t ⟨h1, h2, h3, h4, h5⟩ =>
    ⟨by decide, s, m, m.start t h1 h2 h3 h4 h5, by rw [h3]; exact XFrame.of_outside m.out⟩

/-! ## The whole function -/

theorem setup_rel : RelCT isa (W fun σ s => s = σ) (.block setup) (W S1) := by
  refine W.step (RelCT.taint (A := taint) τ₀ ?_ (by taint_decide)) fun σ s hp e => by subst e; exact setup_stage hp
  rintro s₁ s₂ ⟨σ₁, σ₂, hP, rfl, rfl⟩
  exact agree₀ hP.1 hP.2.1 hP.2.2

theorem S1.af {σ s : State} (h : S1 σ s) : AF σ s :=
  ⟨h.1, h.2.2.1.1 _ (by decide), h.2.2.1.2.2, XFrame.of_outside h.2.2.2.1⟩

theorem bits_rel : RelCT isa (W S1) bits (W Mid) := by
  refine W.step (RelCT.taint (A := taint) τf ?_ (by taint_decide)) fun σ s hp h => bits_stage hp h
  rintro s₁ s₂ ⟨σ₁, σ₂, hP, h₁, h₂⟩
  exact agreeF hP h₁.af h₂.af

theorem lastSwap_rel : RelCT isa (W fun σ s => ∃ s₂, Lad σ s₂ s 0) (.block lastSwap)
    (W fun σ s => ∃ s₂ s₄, Sw σ s₂ s₄ s) := by
  refine W.step (RelCT.taint (A := taint) (τr [.esp, .esi, .edi]) ?_ (by taint_decide))
    fun σ s _ ⟨s₂, l⟩ => WP.mono (lastSwap_stage l) fun t h => ⟨s₂, s, h⟩
  rintro s₁ s₂ ⟨σ₁, σ₂, hP, ⟨_, l₁⟩, ⟨_, l₂⟩⟩
  exact Lad.agree hP l₁ l₂

/-- After the inversion. -/
def IvE (σ s : State) : Prop := ∃ s₂ s₄ s₅, Iv σ s₂ s₄ s₅ s

theorem Sw.rf {σ₁ σ₂ s₂ s₄ s₂' s₄' t₁ t₂ : State} (hP : P₀ σ₁ σ₂) (h₁ : Sw σ₁ s₂ s₄ t₁)
    (h₂ : Sw σ₂ s₂' s₄' t₂) : RF (bs σ₁) t₁ t₂ := by
  obtain ⟨s₁', c₁, p₁, -⟩ := h₁.fin
  obtain ⟨s₂'', c₂, p₂, -⟩ := h₂.fin
  rw [← hP.base] at s₂'' c₂
  exact ⟨⟨s₁', c₁, h₁.2.2.1⟩, ⟨s₂'', c₂, by rw [hP.base]; exact h₂.2.2.1⟩,
    p₁.trans (hP.sp.trans p₂.symm)⟩

theorem invert_piece : RelCT isa (W fun σ s => ∃ s₂ s₄, Sw σ s₂ s₄ s) Impl.X448.X86.invert
    fun t₁ t₂ => (∃ b, RF b t₁ t₂) ∧ W IvE t₁ t₂ := by
  refine W.then (G := IvE) (R := fun t₁ t₂ => ∃ b, RF b t₁ t₂)
    ((RelCT.exists_ fun b => (invert_rel b).mono (fun _ _ h => h)
      fun t₁ t₂ (h : RF b t₁ t₂) => (⟨b, h⟩ : ∃ b, RF b t₁ t₂)).mono ?_ fun _ _ h => h)
    (fun σ s _ ⟨s₂, s₄, h⟩ => WP.mono (invert_stage h) fun t h => ⟨s₂, s₄, s, h⟩)
    fun _ _ _ _ hP hr g₁ g₂ => ⟨hr, _, _, hP, g₁, g₂⟩
  rintro s₁ s₂ ⟨σ₁, σ₂, hP, ⟨_, _, h₁⟩, ⟨_, _, h₂⟩⟩
  exact ⟨_, Sw.rf hP h₁ h₂⟩

theorem IvE.af {σ s : State} (h : IvE σ s) :
    Scr s (bs σ) ∧ CallCtx s (bs σ) ∧ BoundedEnv s.mem (bs σ) ∧ AF σ s := by
  obtain ⟨_, _, _, w, k, b, -, f⟩ := h
  obtain ⟨hs, hc, sp, wr⟩ := w.fin
  exact ⟨k.scr hs, k.ctx hc, b, k.scr hs, (k.regs.1 _ (by decide)).trans sp, k.regs.2.2.trans wr, f⟩

theorem finishMul_rel (b : Addr) : RelCT isa (RF b) (mulCall X2 X2 T7) (RF b) :=
  fieldOp_rel (.mul 1 1 21)

theorem finish_rel : RelCT isa (fun t₁ t₂ => (∃ b, RF b t₁ t₂) ∧ W IvE t₁ t₂) finish
    fun _ _ => True := by
  have hm : RelCT isa (fun t₁ t₂ => (∃ b, RF b t₁ t₂) ∧ W IvE t₁ t₂) (mulCall X2 X2 T7) (W AF) := by
    refine W.then' (G := AF) (fun _ _ h => h.2)
      ((RelCT.exists_ fun b => (finishMul_rel b).mono (fun _ _ h => h) fun _ _ _ => trivial).mono (fun _ _ h => h.1)
        fun _ _ h => h) ?_ fun _ _ _ _ hP _ g₁ g₂ => ⟨_, _, hP, g₁, g₂⟩
    intro σ s hp h
    obtain ⟨hs, hc, hb, -, sp, wr, f⟩ := h.af
    refine WP.mono (xframe hp (NoSp.of_all (by lit_decide)) (by lit_decide) sp wr f
      (mulCall_ok hs hc (o := X2) (a := X2) (b := T7) (by decide) (by decide) (by decide) (hb 1) (hb 21)))
      fun t ⟨⟨c, _, _⟩, f'⟩ => ⟨hs.of_keeps c.keeps (by decide), (c.keeps.1 _ (by decide)).trans sp,
        c.keeps.2.2.trans wr, f'⟩
  unfold finish
  exact RelCT.seq hm (RelCT.taint (A := taint) τf (fun _ _ ⟨_, _, hP, a₁, a₂⟩ => agreeF hP a₁ a₂)
    (by taint_decide))

theorem x448_ct : ConstantTime isa Proof.X448.x448X86.pre Proof.X448.x448X86.pub
    Impl.X448.X86.x448 := by
  refine RelCT.constantTime (Q := fun _ _ => True)
    ((?_ : RelCT isa (W fun σ s => s = σ) x448 fun _ _ => True).mono
      (fun s₁ s₂ h => ⟨s₁, s₂, h, rfl, rfl⟩) fun _ _ h => h)
  unfold x448
  exact setup_rel.seq (bits_rel.seq (ladder_rel.seq (lastSwap_rel.seq (invert_piece.seq finish_rel))))

end VG.Proof.X448.X86
