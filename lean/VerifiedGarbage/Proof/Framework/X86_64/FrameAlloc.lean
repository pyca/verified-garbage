module

public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
public import VerifiedGarbage.Proof.Framework.RelCT

/-! # Running code inside a stack frame (x86-64)

`.frame (.alloc n) body (.free n)` pushes a frame of `n` bytes (`allocState`)
and pops it (`freeState`): `alloc_frame_ok` runs it from a proof about
`body` that ends with the frame's `rsp` and permissions, and `RelCT.alloc`
its timing from its body's. -/

@[expose] public section
namespace VG.X86_64

def freeState (bytes : Nat) (s : State) : State :=
  { s.setReg .rsp (s.gpr .rsp + BitVec.ofNat 64 bytes) with wr := s.wr.tail }

theorem alloc_frame_ok {bytes : Nat} (hb : 0 < bytes ∧ bytes < 4096 ∧ bytes % 8 = 0)
    {s : State} (hl : bytes ≤ (s.gpr .rsp).toNat) {body : Prog isa} {Q : State → Prop}
    (run : WP isa body (allocState bytes s) fun t =>
      t.gpr .rsp = (allocState bytes s).gpr .rsp ∧ t.wr = (allocState bytes s).wr ∧ Q (freeState bytes t)) :
    WP isa (.frame (.alloc bytes) body (.free bytes)) s Q := by
  obtain ⟨trace, t, he, hsp, hwr, hq⟩ := run
  have ha : isa.push (.alloc bytes) s = some (allocState bytes s) := by
    simp only [isa, push, allocState]
    exact ite_eq_left ⟨hb.1, hb.2.1, hb.2.2, hl⟩
  have hf : isa.pop (.free bytes) (allocState bytes s) t = some (freeState bytes t) := by
    simp only [isa, pop]
    exact ite_eq_left ⟨hb.1, hb.2.1, hb.2.2, hsp, hwr, rfl⟩
  exact ⟨_, _, Exec.frame ha he hf, hq⟩

theorem freeState_rsp {bytes : Nat} {s t : State}
    (hsp : t.gpr .rsp = (allocState bytes s).gpr .rsp) :
    (freeState bytes t).gpr .rsp = s.gpr .rsp := by
  change t.gpr .rsp + BitVec.ofNat 64 bytes = _
  rw [hsp]
  change s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 bytes = _
  exact BitVec.sub_add_cancel ..

theorem freeState_wr {bytes : Nat} {s t : State}
    (hw : t.wr = (allocState bytes s).wr) : (freeState bytes t).wr = s.wr := by
  change t.wr.tail = _
  rw [hw]
  rfl

theorem alloc_some {bytes : Nat} {s a : State} (h : isa.push (.alloc bytes) s = some a) :
    a = allocState bytes s := by
  simp only [isa, push] at h
  split at h
  · cases h; rfl
  · cases h

/-- Two runs of a frame of `bytes` bytes leak the same trace when the runs of
its body, from the states after the allocation, do. -/
theorem RelCT.alloc {bytes : Nat} {body : Prog isa} {P R : State → State → Prop}
    (hb : RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ a = allocState bytes s₁ ∧ b = allocState bytes s₂)
      body R) :
    RelCT isa P (.frame (.alloc bytes) body (.free bytes)) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | frame p₁ b₁ q₁ =>
    cases e₂ with
    | frame p₂ b₂ q₂ =>
      obtain rfl := alloc_some p₁
      obtain rfl := alloc_some p₂
      obtain ⟨rfl, -⟩ := hb _ _ _ _ _ _ ⟨s₁, s₂, hp, rfl, rfl⟩ b₁ b₂
      exact ⟨rfl, trivial⟩

end VG.X86_64
