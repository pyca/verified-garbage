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

/-- The state a `free` leaves: `freeState`, with the released frame's bytes
`lose`'s and the unknowns it used gone. -/
def freeLost (bytes : Nat) (s : State) : State :=
  { freeState bytes s with
    mem := lose s.mem (s.gpr .rsp) bytes s.unknowns
    unknowns := fun n => s.unknowns (n + bytes / 4) }

theorem free_lost {bytes : Nat} (hb : 0 < bytes ∧ bytes < 4096 ∧ bytes % 8 = 0) {s t : State}
    (hsp : t.gpr .rsp = (allocState bytes s).gpr .rsp) (hwr : t.wr = (allocState bytes s).wr) :
    isa.pop (.free bytes) (allocState bytes s) t = some (freeLost bytes t) := by
  simp only [isa, pop]
  exact ite_eq_left ⟨hb.1, hb.2.1, hb.2.2, hsp, hwr, rfl⟩

/-- A frame of `bytes` bytes: its body runs from `allocState bytes s`, ends
with the frame's `rsp` and permissions, and the `free` leads to
`freeState bytes t`, of which the postcondition may rely on nothing the
frame's bytes hold, nor on the unknowns (as `WP.frame`'s, `Frame.lean`): it
holds whatever memory `m` that differs from the body's only in the frame,
and whatever unknowns `u`, the state then has. -/
theorem alloc_frame_ok {bytes : Nat} (hb : 0 < bytes ∧ bytes < 4096 ∧ bytes % 8 = 0)
    {s : State} (hl : bytes ≤ (s.gpr .rsp).toNat) {body : Prog isa} {Q : State → Prop}
    (run : WP isa body (allocState bytes s) fun t =>
      t.gpr .rsp = (allocState bytes s).gpr .rsp ∧ t.wr = (allocState bytes s).wr ∧ ∀ m u,
        Frame [⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩] t.mem m →
        Q { freeState bytes t with mem := m, unknowns := u }) :
    WP isa (.frame (.alloc bytes) body (.free bytes)) s Q := by
  obtain ⟨trace, t, he, hsp, hwr, hq⟩ := run
  have ha : isa.push (.alloc bytes) s = some (allocState bytes s) := by
    simp only [isa, push, allocState]
    exact ite_eq_left ⟨hb.1, hb.2.1, hb.2.2, hl⟩
  refine ⟨_, _, Exec.frame ha he (free_lost hb hsp hwr), hq _ _ ?_⟩
  rw [hsp]
  exact lose_frame _ _ _ _

/-- `alloc_frame_ok` with the state the `free` leaves, `freeLost bytes t`. Only the residue lemmas use it, which state per
run what a released frame holds (MCDT's exit); every other proof uses
`alloc_frame_ok`. -/
theorem alloc_frame_okMem {bytes : Nat} (hb : 0 < bytes ∧ bytes < 4096 ∧ bytes % 8 = 0)
    {s : State} (hl : bytes ≤ (s.gpr .rsp).toNat) {body : Prog isa} {Q : State → Prop}
    (run : WP isa body (allocState bytes s) fun t =>
      t.gpr .rsp = (allocState bytes s).gpr .rsp ∧ t.wr = (allocState bytes s).wr ∧ Q (freeLost bytes t)) :
    WP isa (.frame (.alloc bytes) body (.free bytes)) s Q := by
  obtain ⟨trace, t, he, hsp, hwr, hq⟩ := run
  have ha : isa.push (.alloc bytes) s = some (allocState bytes s) := by
    simp only [isa, push, allocState]
    exact ite_eq_left ⟨hb.1, hb.2.1, hb.2.2, hl⟩
  exact ⟨_, _, Exec.frame ha he (free_lost hb hsp hwr), hq⟩

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
