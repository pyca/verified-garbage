module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.Base
public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.Framework.X86.CallWith

/-! # Two runs of parameter generation at the same point

Both runs satisfy the same predicate with the same parameters (`Both`): the
same environment, the same values of the state words that steer branches and
hold pointers, the same loop indices. Code whose trace depends only on
registers both runs agree on is checked by the taint analysis; a branch's
condition is fixed by the parameters; what each run reaches is what its
correctness proof says. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86

/-- Both runs satisfy `Φ a`, for the same `a`. -/
def Both {α : Type} (Φ : α → State → Prop) (s t : State) : Prop := ∃ a, Φ a s ∧ Φ a t

theorem both_post {α : Type} {Φ Ψ : α → State → Prop} {c : Prog isa}
    (hct : RelCT isa (Both Φ) c fun _ _ => True) (hw : ∀ a s, Φ a s → WP isa c s (Ψ a)) :
    RelCT isa (Both Φ) c (Both Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨a, h₁, h₂⟩ := hp
  exact ⟨ht, a, wp_result (hw a _ h₁) e₁, wp_result (hw a _ h₂) e₂⟩

theorem both_map {α β : Type} {Φ : α → State → Prop} {Φ' : β → State → Prop} {c : Prog isa}
    {Q : State → State → Prop} (f : α → β) (h : ∀ a s, Φ a s → Φ' (f a) s) (hct : RelCT isa (Both Φ') c Q) :
    RelCT isa (Both Φ) c Q :=
  hct.mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨f a, h _ _ h₁, h _ _ h₂⟩) fun _ _ h => h

theorem both_mono {α : Type} {Φ Φ' : α → State → Prop} (h : ∀ a s, Φ a s → Φ' a s) {s t : State}
    (hp : Both Φ s t) : Both Φ' s t :=
  let ⟨a, h₁, h₂⟩ := hp; ⟨a, h a _ h₁, h a _ h₂⟩

/-- For each value of the parameters. -/
theorem both_exists {α : Type} {Φ : α → State → Prop} {c : Prog isa} {Q : State → State → Prop}
    (h : ∀ a, RelCT isa (fun s t => Φ a s ∧ Φ a t) c Q) : RelCT isa (Both Φ) c Q :=
  RelCT.exists_ h

/-- A branch whose condition the parameters fix. -/
theorem both_ite {α : Type} {Φ : α → State → Prop} {cond : isa.Cond} {th el : Prog isa}
    {Q : State → State → Prop} (b : α → Bool) (hc : ∀ a s, Φ a s → isa.eval cond s = some (b a))
    (ht : RelCT isa (Both fun a s => Φ a s ∧ b a = true) th Q)
    (he : RelCT isa (Both fun a s => Φ a s ∧ b a = false) el Q) :
    RelCT isa (Both Φ) (.ite cond th el) Q := by
  refine RelCT.ite (fun s t ⟨a, h₁, h₂⟩ => by rw [hc a s h₁, hc a t h₂]) ?_ ?_
  · refine ht.mono (fun s t ⟨⟨a, h₁, h₂⟩, e⟩ => ⟨a, ⟨h₁, ?_⟩, h₂, ?_⟩) fun _ _ h => h <;>
    · rw [hc a s h₁] at e; exact Option.some.inj e
  · refine he.mono (fun s t ⟨⟨a, h₁, h₂⟩, e⟩ => ⟨a, ⟨h₁, ?_⟩, h₂, ?_⟩) fun _ _ h => h <;>
    · rw [hc a s h₁] at e; exact Option.some.inj e

/-- Code whose trace the taint analysis checks from registers the
parameters fix. -/
theorem both_agree {α : Type} {Φ : α → State → Prop} {c : Prog isa} {Q : State → State → Prop} (rs : List Reg)
    (val : α → Reg → BitVec 32) (hpin : ∀ a s, Φ a s → ∀ r ∈ rs, s.gpr r = val a r)
    (h : RelCT isa (VG.X86.Taint.Agree (τr rs)) c Q) : RelCT isa (Both Φ) c Q :=
  h.mono (fun s t ⟨a, h₁, h₂⟩ => agree_regs fun r hr => (hpin a s h₁ r hr).trans (hpin a t h₂ r hr).symm)
    fun _ _ h => h

/-- Code the taint analysis checks from the registers `rs`. -/
theorem tcheck (rs : List Reg) (c : Prog isa)
    (h : (VG.Taint.check taint (τr rs) c (VG.Taint.hintOf taint (τr rs) c)).isSome = true) :
    RelCT isa (VG.X86.Taint.Agree (τr rs)) c fun _ _ => True :=
  RelCT.taint (A := taint) (τr rs) (fun _ _ h => h) h

/-- Code the taint analysis checks from the registers `rs`, which it keeps
public. -/
theorem tkeep (rs : List Reg) (c : Prog isa)
    (h : (VG.Taint.check taint (τr rs) c (VG.Taint.hintOf taint (τr rs) c)).map (taint.le (τr rs)) = some true) :
    RelCT isa (VG.X86.Taint.Agree (τr rs)) c (VG.X86.Taint.Agree (τr rs)) := by
  obtain ⟨τ', H, L⟩ := Option.map_eq_some_iff.mp h
  exact checkedProgramChange H L

/-- `RelCT.callWith`, popping into any register. -/
theorem callWithPop {rs : List Reg} {n : String} {c : Prog isa} {k : Contract isa} {r : Reg}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {P : State → State → Prop} (rd wr : List Region)
    (hP : ∀ s₁ s₂, P s₁ s₂ → CallPre k rs rd wr s₁ ∧ CallPre k rs rd wr s₂ ∧
      s₁.gpr .esp = s₂.gpr .esp ∧
      k.pub ((pushed rs s₁).callEntry.withRegions rd wr) ((pushed rs s₂).callEntry.withRegions rd wr)) :
    RelCT isa P (.frame (.push rs) (.call n c) (.pop r rs.length)) fun _ _ => True := by
  refine RelCT.frame (fun s₁ s₂ h => (hP _ _ h).2.2.1) (RelCT.call hv hct rd wr ?_)
  rintro _ _ ⟨s₁, s₂, h, rfl, rfl⟩
  obtain ⟨k₁, k₂, hsp, hpub⟩ := hP _ _ h
  refine ⟨k₁.pre, k₂.pre, hpub, by rw [pushed_rd, pushed_wr]; exact k₁.cov, by rw [pushed_wr]; exact k₁.covw,
    by rw [pushed_rd, pushed_wr]; exact k₂.cov, by rw [pushed_wr]; exact k₂.covw, ?_⟩
  rw [pushed_esp, pushed_esp, hsp]

/-- `tcheck` for code checked as `c₀`, which differs only in immediates and
offsets. -/
theorem tcheckE (rs : List Reg) (c c₀ : Prog isa) (e : Code.erase c = Code.erase c₀)
    (hh : VG.X86.Taint.hintNoBases (VG.Taint.hintOf taint (τr rs) c₀) = true)
    (h : (VG.Taint.check taint (τr rs) c₀ (VG.Taint.hintOf taint (τr rs) c₀)).map (taint.le (τr [])) = some true) :
    RelCT isa (VG.X86.Taint.Agree (τr rs)) c fun _ _ => True :=
  (erased_relCT c c₀ _ e rfl hh h).mono (fun _ _ h => h) fun _ _ _ => trivial

theorem Base.edi {E : Env} {s : State} (B : Base E s) : s.gpr .edi = E.base.setWidth 32 := by
  rw [← B.scr.edi, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

end VG.Proof.Dsa.X86.Generation
