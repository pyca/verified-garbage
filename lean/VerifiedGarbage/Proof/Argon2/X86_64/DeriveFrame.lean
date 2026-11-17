module

public import VerifiedGarbage.Impl.Argon2.X86_64.Derive
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.Offset

/-! Compose the nested saved-register frames and the 272-byte local allocation. -/

@[expose] public section

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

def frameStart (s : State) : List Reg → State
  | [] => pushed (List.replicate 34 .rax) s
  | r :: rs => frameStart (pushed [r] s) rs

def frameEnd (s : State) : List Reg → State
  | [] => popped .rax 34 s
  | r :: rs => popped r 1 (frameEnd s rs)

theorem frameEnd_metadata (s t : State) (rs : List Reg)
    (sp : t.gpr .rsp = (frameStart s rs).gpr .rsp)
    (wr : t.wr = (frameStart s rs).wr) :
    (frameEnd t rs).gpr .rsp = s.gpr .rsp ∧ (frameEnd t rs).wr = s.wr := by
  induction rs generalizing s with
  | nil =>
    constructor
    · rw [frameEnd, popped_rsp, sp, frameStart, pushed_rsp]
      simp only [List.length_replicate, Nat.reduceMul, BitVec.sub_add_cancel]
    · rw [frameEnd, popped_wr, wr, frameStart, pushed_wr]; rfl
  | cons r rs ih =>
    obtain ⟨innerSp, innerWr⟩ := ih (pushed [r] s) sp wr
    constructor
    · rw [frameEnd, popped_rsp, innerSp, pushed_rsp]
      simp only [List.length_singleton, Nat.mul_one, BitVec.sub_add_cancel]
    · rw [frameEnd, popped_wr, innerWr, pushed_wr]; rfl

theorem frameEnd_mem (s : State) (rs : List Reg) : (frameEnd s rs).mem = s.mem := by
  induction rs with
  | nil => exact popped_mem ..
  | cons r rs ih => exact (popped_mem ..).trans ih

/-- The nested frames, whose bytes, `272 + 8 * rs.length` below `rsp`, each hold
whatever they hold once released. -/
theorem frame_ok (s : State) (rs : List Reg) (body : Prog isa) (Q : State → Prop)
    (notSp : .rsp ∉ rs) (space : 272 + 8 * rs.length ≤ (s.gpr .rsp).toNat)
    (run : WP isa body (frameStart s rs) fun t =>
      t.gpr .rsp = (frameStart s rs).gpr .rsp ∧ t.wr = (frameStart s rs).wr ∧ ∀ m u,
        Frame [⟨s.gpr .rsp - BitVec.ofNat 64 (272 + 8 * rs.length), 272 + 8 * rs.length⟩] t.mem m →
        Q { frameEnd t rs with mem := m, unknowns := u }) :
    WP isa (Impl.Argon2.X86_64.Derive.frame body rs) s Q := by
  induction rs generalizing s Q with
  | nil =>
    exact WP.frame (by decide) (by decide) (by decide) (by simpa using space) run
  | cons r rs ih =>
    simp only [List.mem_cons, not_or] at notSp
    have pushedBound : ((pushed [r] s).gpr .rsp).toNat = (s.gpr .rsp).toNat - 8 := by
      rw [pushed_rsp]
      simp only [List.length_singleton, Nat.mul_one]
      exact toNat_sub_ofNat (by simp only [List.length_cons] at space; omega_using [space])
    have innerSpace : 272 + 8 * rs.length ≤ ((pushed [r] s).gpr .rsp).toNat := by
      rw [pushedBound]; simp only [List.length_cons] at space; omega_using [space]
    have hp : (pushed [r] s).gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 8 := by
      rw [pushed_rsp]; rfl
    have hlt := (s.gpr .rsp).isLt
    simp only [List.length_cons] at space
    apply WP.frame (by simp) (by simpa using notSp.1) (Ne.symm notSp.1)
      (by simp only [List.length_singleton, Nat.mul_one]; omega_using [space])
    apply ih (pushed [r] s) (fun t => t.gpr .rsp = (pushed [r] s).gpr .rsp ∧
      t.wr = (pushed [r] s).wr ∧ ∀ m u,
        Frame [⟨s.gpr .rsp - BitVec.ofNat 64 (8 * [r].length), 8 * [r].length⟩] t.mem m →
        Q { popped r [r].length t with mem := m, unknowns := u }) notSp.2 innerSpace
    apply run.mono
    rintro t ⟨sp, wr, result⟩
    obtain ⟨endSp, endWr⟩ := frameEnd_metadata (pushed [r] s) t rs sp wr
    refine ⟨sp, wr, fun m₁ u₁ fm₁ => ⟨endSp, endWr, fun m₂ u₂ fm₂ => ?_⟩⟩
    replace fm₂ : Frame [⟨s.gpr .rsp - BitVec.ofNat 64 8, 8⟩] m₁ m₂ := fm₂
    have slot : ∀ i < 1, m₁.readW ((frameEnd t rs).gpr .rsp + BitVec.ofNat 64 (8 * i)) 64 =
        (frameEnd t rs).mem.readW ((frameEnd t rs).gpr .rsp + BitVec.ofNat 64 (8 * i)) 64 := by
      intro i hi
      simp only [Nat.lt_one_iff] at hi; subst hi
      rw [frameEnd_mem, endSp, Nat.mul_zero, BitVec.add_zero]
      refine fm₁.readW (r := ⟨(pushed [r] s).gpr .rsp, 8⟩) (Region.contains_self _ _) ?_ (by decide)
      intro r' hr'
      simp only [List.mem_singleton] at hr'; subst hr'
      exact Offset.base_disjoint_below _ (by omega_using [space, hlt])
    show Q { popped r 1 { frameEnd t rs with mem := m₁, unknowns := u₁ } with mem := m₂, unknowns := u₂ }
    rw [popped_withMem slot]
    refine result m₂ u₂ ((fm₁.sub ?_).trans (fm₂.sub ?_))
    · intro r' hr'
      simp only [List.mem_singleton] at hr'; subst hr'
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      rw [hp, BitVec.sub_sub, ← BitVec.ofNat_add]
      exact Offset.sub_below _ (by simp only [List.length_cons]; omega_using [])
        (by simp only [List.length_cons]; omega_using [])
    · intro r' hr'
      simp only [List.mem_singleton] at hr'; subst hr'
      exact ⟨_, List.mem_singleton_self _, Offset.sub_below _ (by simp only [List.length_cons]; omega_using [])
        (by simp only [List.length_cons]; omega_using [])⟩

end VG.Proof.Argon2.X86_64.Derive
