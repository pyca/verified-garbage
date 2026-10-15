import VerifiedGarbage.Proof.Spectre.X86_64.Gadget

/-!
# The gadget with a speculation barrier

`fenced` is `gadget` with `lfence` at the top of the bounds-checked branch
(Intel's recommended mitigation): it is speculatively constant time
(`fenced_sct`), proved from the semantics, since a misprediction into the
branch stops at the barrier. (The taint analysis cannot prove it: it treats
every loaded byte as secret, so it rejects `gadget` already sequentially.)
-/

namespace VG.Proof.SpectreDemo

open VG.X86_64 VG.X86_64.Spectre

def fencedThen : List isa.Instr :=
  [.lfence, .movzx8 .rax ⟨.rdi, some .rsi, 1, 0⟩, .movzx8 .r8 ⟨.rcx, some .rax, 1, 0⟩]

def fenced : Prog isa :=
  .seq (.block [.alu .cmp .rsi (.reg .rdx)]) (.ite .b (.block fencedThen) (.block []))

theorem run_movzx8 {ms : Bool} {d : Reg} {m : MemOp} {s s' : State}
    (h : spectre.run ms (.movzx8 d m) s = some s') :
    s'.gpr d = (s.mem (s.ea m)).setWidth 64 ∧ ∀ r, r ≠ d → s'.gpr r = s.gpr r := by
  cases ms
  · exact ⟨movzx8_gpr h, fun _ hr => movzx8_other h hr⟩
  · have h' : exec (.movzx8 d m) (widen s) = some s' := h
    have g := movzx8_gpr h'
    have o := fun r (hr : r ≠ d) => movzx8_other h' hr
    exact ⟨g, o⟩

theorem leaks_movzx8 (ms : Bool) (d : Reg) (m : MemOp) (s : State) :
    spectre.leaks ms (.movzx8 d m) s = [s.ea m] := by
  cases ms <;> rfl

/-- The bounds-checked branch leaks the same in two runs that agree on the
pointers and the index, and, unless misspeculating, on `a[i]`. -/
theorem fencedThen_eq {u₁ u₂ : isa.State} {ms : Bool} {n : Nat} {t₁ t₂ : List SLeak}
    {r₁ r₂ : Option (isa.State × Nat)} (hdi : u₁.gpr .rdi = u₂.gpr .rdi)
    (hsi : u₁.gpr .rsi = u₂.gpr .rsi) (hcx : u₁.gpr .rcx = u₂.gpr .rcx)
    (hm : ms = false →
      u₁.mem (u₁.gpr .rdi + u₁.gpr .rsi) = u₂.mem (u₂.gpr .rdi + u₂.gpr .rsi))
    (e₁ : SBlock spectre fencedThen u₁ ms n t₁ r₁) (e₂ : SBlock spectre fencedThen u₂ ms n t₂ r₂) :
    t₁ = t₂ := by
  unfold fencedThen at e₁ e₂
  cases ms
  · -- In bounds: `lfence` does nothing, and both loads are at the same addresses.
    have hm := hm rfl
    have hz : BitVec.ofInt 64 (0 : Int) = 0 := rfl
    have hl : ∀ u, spectre.leaks false .lfence u = [] := fun _ => rfl
    cases e₁ with
    | stop => cases e₂; rfl
    | cons _ x₁ b₁ =>
      cases e₂ with
      | cons _ x₂ b₂ =>
        cases x₁; cases x₂
        cases b₁ with
        | stop => cases b₂; rfl
        | cons _ y₁ c₁ =>
          cases b₂ with
          | cons _ y₂ c₂ =>
            obtain ⟨g₁, o₁⟩ := run_movzx8 y₁
            obtain ⟨g₂, o₂⟩ := run_movzx8 y₂
            simp only [leaks_movzx8, State.ea] at g₁ g₂ ⊢
            simp only [BitVec.mul_one, hz] at g₁ g₂ hm ⊢
            have ea : u₁.gpr .rdi + u₁.gpr .rsi = u₂.gpr .rdi + u₂.gpr .rsi := by rw [hdi, hsi]
            cases c₁ with
            | stop => cases c₂; simp only [hl, List.map_cons, List.map_nil, ea]
            | cons _ z₁ d₁ =>
              cases c₂ with
              | cons _ z₂ d₂ =>
                cases d₁; cases d₂
                simp only [leaks_movzx8, hl, State.ea, BitVec.mul_one,
                  List.map_cons, List.map_nil, List.cons_append, List.nil_append, ea,
                  o₁ .rcx (by decide), o₂ .rcx (by decide), g₁, g₂, hcx]
                rw [hdi, hsi] at hm
                simp only [show ∀ x : BitVec 64, x + 0 = x from BitVec.add_zero, hm]
  · -- Misspeculating: the run stops at `lfence`.
    cases e₁ with
    | stop => cases e₂; rfl
    | fence => cases e₂ with
      | fence => rfl
      | cons hf => cases hf
    | cons hf => cases hf

theorem fenced_sct : SpecConstantTime spectre Pre Pub fenced := by
  intro s₁ s₂ D n t₁ t₂ o₁ o₂ _ _ hp e₁ e₂
  obtain ⟨hdi, hsi, hdx, hcx, hm⟩ := hp
  have cmp : ∀ {s v : State} {n t r}, SBlock spectre [.alu .cmp .rsi (.reg .rdx)] s false n t r →
      r = some (v, n - 1) → v = arithFlags s (s.gpr .rsi - s.gpr .rdx)
        (decide ((s.gpr .rsi).toNat < (s.gpr .rdx).toNat))
        (subOverflow (s.gpr .rsi) (s.gpr .rdx) (s.gpr .rsi - s.gpr .rdx)) ∧ t = [] := by
    intro s v n t r b hr
    cases b with
    | stop => cases hr
    | cons _ x b =>
      cases b
      simp only [Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, -⟩ := hr
      simp only [Spectre.run, Bool.false_eq_true, ite_false, isa, exec, execAlu, readSrc,
        Option.bind_some, Option.some.injEq] at x
      exact ⟨x.symm, rfl⟩
  cases e₁ with
  | seqHalt a₁ =>
    cases e₂ with
    | seqHalt a₂ =>
      cases a₁ with | blockHalt b₁ => cases a₂ with | blockHalt b₂ =>
      cases b₁ with
      | stop => cases b₂; rfl
      | cons _ _ b => cases b
    | seq a₂ _ =>
      cases a₁ with | blockHalt b₁ => cases a₂ with | blockDone b₂ =>
      cases b₁ with
      | stop => cases b₂
      | cons _ _ b => cases b
  | seq a₁ i₁ =>
    cases e₂ with
    | seqHalt a₂ =>
      cases a₁ with | blockDone b₁ => cases a₂ with | blockHalt b₂ =>
      cases b₂ with
      | stop => cases b₁
      | cons _ _ b => cases b
    | seq a₂ i₂ =>
      cases a₁ with | blockDone b₁ => cases a₂ with | blockDone b₂ =>
      have nb₁ : ∀ {s n t s' n'}, SBlock spectre [.alu .cmp .rsi (.reg .rdx)] s false n t (some (s', n')) →
          n' = n - 1 := by
        intro s n t s' n' b
        cases b with
        | cons _ _ b => cases b; rfl
      obtain rfl := nb₁ b₁
      obtain rfl := nb₁ b₂
      obtain ⟨rfl, rfl⟩ := cmp b₁ rfl
      obtain ⟨rfl, rfl⟩ := cmp b₂ rfl
      simp only [List.nil_append]
      have hcf : isa.eval .b (arithFlags s₁ (s₁.gpr .rsi - s₁.gpr .rdx)
            (decide ((s₁.gpr .rsi).toNat < (s₁.gpr .rdx).toNat))
            (subOverflow (s₁.gpr .rsi) (s₁.gpr .rdx) (s₁.gpr .rsi - s₁.gpr .rdx))) =
          some (decide ((s₁.gpr .rsi).toNat < (s₁.gpr .rdx).toNat)) := rfl
      have hcf₂ : isa.eval .b (arithFlags s₂ (s₂.gpr .rsi - s₂.gpr .rdx)
            (decide ((s₂.gpr .rsi).toNat < (s₂.gpr .rdx).toNat))
            (subOverflow (s₂.gpr .rsi) (s₂.gpr .rdx) (s₂.gpr .rsi - s₂.gpr .rdx))) =
          some (decide ((s₁.gpr .rsi).toNat < (s₁.gpr .rdx).toNat)) := by rw [hsi, hdx]; rfl
      cases i₁ with
      | iteEnd => cases i₂; rw [hcf, hcf₂]
      | iteF x₁ =>
        cases i₂ with
        | iteF x₂ =>
          rw [hcf, hcf₂]
          cases x₁ with
          | blockDone b => cases b; cases x₂ with
            | blockDone b => cases b; rfl
            | blockHalt b => cases b
          | blockHalt b => cases b
      | iteT x₁ =>
        cases i₂ with
        | iteT x₂ =>
          rw [hcf, hcf₂]
          rw [hcf] at x₁; rw [hcf₂] at x₂
          congr 1
          have body : ∀ {u ms D n t o}, SExec spectre (.block fencedThen) u ms D n t o →
              ∃ r, SBlock spectre fencedThen u ms n t r := by
            intro u ms D n t o x
            cases x with
            | blockDone b => exact ⟨_, b⟩
            | blockHalt b => exact ⟨_, b⟩
          obtain ⟨_, y₁⟩ := body x₁
          obtain ⟨_, y₂⟩ := body x₂
          refine fencedThen_eq (by simp [arithFlags, State.setFlags, hdi])
            (by simp [arithFlags, State.setFlags, hsi]) (by simp [arithFlags, State.setFlags, hcx])
            (fun hms => ?_) y₁ y₂
          have hlt : (s₁.gpr .rsi).toNat < (s₁.gpr .rdx).toNat := by
            simpa [Spectre.mis] using hms
          have hk := hm _ hlt
          simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, hdi, hsi] at hk
          simp only [arithFlags, State.setFlags, hk, hdi, hsi]

end VG.Proof.SpectreDemo
