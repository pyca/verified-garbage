module

public import VerifiedGarbage.Impl.Argon2.AArch64.Derive
public import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Compose the saved-register frames and the 272-byte local allocation. -/

@[expose] public section

namespace VG.Proof.Argon2.AArch64.Derive
open VG VG.AArch64

def frameStart (s : State) : List Reg → State
  | [] => allocated 272 s
  | r :: rs => frameStart (pushed r s) rs

def frameEnd (s : State) : List Reg → State
  | [] => freed 272 s
  | r :: rs => popped r (frameEnd s rs)

theorem frameEnd_metadata (s t : State) (rs : List Reg)
    (sp : t.sp = (frameStart s rs).sp)
    (wr : t.wr = (frameStart s rs).wr) :
    (frameEnd t rs).sp = s.sp ∧ (frameEnd t rs).wr = s.wr := by
  induction rs generalizing s with
  | nil =>
    constructor
    · change t.sp + BitVec.ofNat 64 272 = s.sp
      rw [sp]; exact BitVec.sub_add_cancel _ _
    · change t.wr.tail = s.wr
      rw [wr]; rfl
  | cons r rs ih =>
    obtain ⟨innerSp, innerWr⟩ := ih (pushed r s) sp wr
    constructor
    · change (frameEnd t rs).sp + 16 = s.sp
      rw [innerSp]; exact BitVec.sub_add_cancel _ _
    · change (frameEnd t rs).wr.tail = s.wr
      rw [innerWr]; rfl

theorem frameEnd_mem (s : State) (rs : List Reg) : (frameEnd s rs).mem = s.mem := by
  induction rs with
  | nil => rfl
  | cons r rs ih => exact ih

/-- The frames saving `rs` around the allocation of 272 bytes: each pop reads
its register from the body's memory, which the frames inside it, released
before it, do not reach, and the postcondition holds whatever memory `m`
that differs from the body's only in the frames, the `272 + 16 * rs.length`
bytes below the stack pointer, and whatever unknowns `u`. -/
theorem frame_ok (s : State) (rs : List Reg) (body : Prog isa) (Q : State → Prop)
    (space : 272 + 16 * rs.length ≤ s.sp.toNat)
    (run : WP isa body (frameStart s rs) fun t =>
      t.sp = (frameStart s rs).sp ∧ t.wr = (frameStart s rs).wr ∧
        ∀ m u, Frame [below s.sp (272 + 16 * rs.length)] t.mem m →
          Q { frameEnd t rs with mem := m, unknowns := u }) :
    WP isa (Impl.Argon2.AArch64.Derive.frame body rs) s Q := by
  induction rs generalizing s Q with
  | nil =>
    exact WP.alloc (by decide) (by simpa using space) (run.mono fun _ h => h.2.2)
  | cons r rs ih =>
    have pushedBound : (pushed r s).sp.toNat = s.sp.toNat - 16 := by
      change (s.sp - 16).toNat = s.sp.toNat - 16
      rw [BitVec.toNat_sub_of_le (by
        rw [BitVec.le_def]
        change 16 ≤ s.sp.toNat
        simp only [List.length_cons] at space; omega_using [space])]
      rfl
    have innerSpace : 272 + 16 * rs.length ≤ (pushed r s).sp.toNat := by
      rw [pushedBound]; simp only [List.length_cons] at space; omega_using [space]
    have hk : 272 + 16 * (r :: rs).length = (272 + 16 * rs.length) + 16 := by
      simp only [List.length_cons]; omega_using []
    have hn : 272 + 16 * rs.length + 16 < 2 ^ 64 := by
      have := s.sp.isLt; simp only [List.length_cons] at space; omega_using [space, this]
    apply WP.frame (by simp only [List.length_cons] at space; omega_using [space])
    apply ih (pushed r s) (fun t => ∀ m u, Frame [⟨s.sp - 16, 16⟩] t.mem m →
      Q { popped r t with mem := m, unknowns := u }) innerSpace
    apply run.mono
    rintro t ⟨sp, wr, result⟩
    refine ⟨sp, wr, fun m₁ u₁ f₁ m₂ u₂ f₂ => ?_⟩
    rw [hk] at result
    -- The saved register is in this frame, which the inner frames' release
    -- does not reach.
    obtain ⟨esp, -⟩ := frameEnd_metadata (pushed r s) t rs sp wr
    have f₁' : Frame [below (s.sp - 16) (272 + 16 * rs.length)] t.mem m₁ := f₁
    have hslot : m₁.read (frameEnd t rs).sp 8 = (frameEnd t rs).mem.read (frameEnd t rs).sp 8 := by
      rw [esp, frameEnd_mem]
      show m₁.read (s.sp - 16) 8 = t.mem.read (s.sp - 16) 8
      refine f₁'.read (r := ⟨s.sp - 16, 16⟩) (by simp [Region.Contains]) (fun R hR => ?_) (by decide)
      simp only [List.mem_singleton] at hR; subst hR
      exact frame_not_below s.sp hn
    have e : popped r { frameEnd t rs with mem := m₁, unknowns := u₁ } =
        { popped r (frameEnd t rs) with mem := m₁, unknowns := u₁ } := by
      simp only [popped]
      rw [show ({ frameEnd t rs with mem := m₁, unknowns := u₁ } : State).mem.read
          ({ frameEnd t rs with mem := m₁, unknowns := u₁ } : State).sp 8 =
            (frameEnd t rs).mem.read (frameEnd t rs).sp 8 from hslot]
      rfl
    rw [e]
    refine result m₂ u₂ ((Frame.sub f₁' fun R hR => ?_).trans (Frame.sub f₂ fun R hR => ?_))
    · simp only [List.mem_singleton] at hR; subst hR
      exact ⟨_, List.mem_singleton_self _, below_body s.sp _⟩
    · simp only [List.mem_singleton] at hR; subst hR
      exact ⟨_, List.mem_singleton_self _, below_frame s.sp _ hn⟩

end VG.Proof.Argon2.AArch64.Derive
