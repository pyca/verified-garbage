import VerifiedGarbage.Impl.P521Field.X86_64
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.Offset

/-!
# P-521's field functions on x86-64: the frames that save registers

`frames body rs` (`Impl/P521Field/X86_64.lean`) pushes each register of
`rs` in a frame of its own, runs `body`, and pops them back. From `s`, the
body starts in `framesStart s rs`: `rsp` is `8 |rs|` lower, the other
registers are unchanged, `rs[j]` is at `rsp - 8 (j + 1)` (`framesStart_word`)
and nothing else in memory changed (`framesStart_frame`). If the body
leaves `rsp`, the writable regions and those words as they were, the pops
(`framesEnd`) restore every register of `rs` (`framesEnd_gpr`).
-/

namespace VG.Proof.P521Field.X86_64

open VG VG.X86_64 VG.Impl.P521Field.X86_64

/-- The state the body of `frames body rs` starts in, from `s`. -/
def framesStart (s : State) : List Reg → State
  | [] => s
  | r :: rs => framesStart (pushed [r] s) rs

/-- The state after the pops of `frames body rs`, from the body's last `t`. -/
def framesEnd (t : State) : List Reg → State
  | [] => t
  | r :: rs => popped r 1 (framesEnd t rs)

theorem framesStart_rsp (s : State) (rs : List Reg) :
    (framesStart s rs).gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 (8 * rs.length) := by
  induction rs generalizing s with
  | nil => simp [framesStart]
  | cons r rs ih =>
    rw [framesStart, ih, pushed_rsp]
    simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.mul_one]
    rw [BitVec.sub_sub, ← BitVec.ofNat_add]
    exact congrArg (fun n => s.gpr .rsp - BitVec.ofNat 64 n) (by omega)

theorem framesStart_gpr (s : State) (rs : List Reg) {r : Reg} (h : r ≠ .rsp) :
    (framesStart s rs).gpr r = s.gpr r := by
  induction rs generalizing s with
  | nil => rfl
  | cons x xs ih => exact (ih (pushed [x] s)).trans (pushed_gpr _ _ h)

theorem framesStart_rd (s : State) (rs : List Reg) : (framesStart s rs).rd = s.rd := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih => exact (ih (pushed [r] s)).trans (pushed_rd ..)

theorem framesStart_mxcsr (s : State) (rs : List Reg) : (framesStart s rs).mxcsr = s.mxcsr := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih => exact (ih (pushed [r] s)).trans (pushed_mxcsr ..)

/-- The writable regions only grow. -/
theorem framesStart_wr (s : State) (rs : List Reg) {R : Region} (h : R ∈ s.wr) :
    R ∈ (framesStart s rs).wr := by
  induction rs generalizing s with
  | nil => exact h
  | cons r rs ih => exact ih (pushed [r] s) (by rw [pushed_wr]; exact List.mem_cons_of_mem _ h)

/-- The pushes change only the `8 |rs|` bytes below `rsp`. -/
theorem framesStart_frame (s : State) (rs : List Reg) (notSp : .rsp ∉ rs)
    (space : 8 * rs.length ≤ (s.gpr .rsp).toNat) :
    Frame [below (s.gpr .rsp) (8 * rs.length)] s.mem (framesStart s rs).mem := by
  induction rs generalizing s with
  | nil => exact Frame.refl _ _
  | cons r rs ih =>
    simp only [List.mem_cons, not_or] at notSp
    have enough : 8 ≤ (s.gpr .rsp).toNat := by simp only [List.length_cons] at space; omega
    have innerSpace : 8 * rs.length ≤ ((pushed [r] s).gpr .rsp).toNat := by
      rw [pushed_rsp]
      simp only [List.length_singleton, Nat.mul_one]
      rw [toNat_sub_ofNat enough]
      simp only [List.length_cons] at space; omega
    have outer := (pushRegs_mem s [r] (by simpa using notSp.1) (by simpa using enough)).1
    have inner := ih (pushed [r] s) notSp.2 innerSpace
    apply (outer.sub ?_).trans (inner.sub ?_)
    · intro region hr
      simp only [List.mem_singleton] at hr; subst region
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      exact Offset.sub_below (s.gpr .rsp) (by simp only [List.length_cons, List.length_nil]; omega)
        (by simp only [List.length_cons, List.length_nil]; omega)
    · intro region hr
      simp only [List.mem_singleton] at hr; subst region
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      rw [pushed_rsp]
      simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.mul_one, below]
      rw [BitVec.sub_sub, ← BitVec.ofNat_add, show 8 + 8 * rs.length = 8 * (rs.length + 1) by omega]
      exact Region.sub_prefix (by omega)

/-- `rs[j]` is at `rsp - 8 (j + 1)` when the body starts. -/
theorem framesStart_word (s : State) (rs : List Reg) (notSp : .rsp ∉ rs)
    (space : 8 * rs.length ≤ (s.gpr .rsp).toNat) (j : Nat) (bound : j < rs.length) :
    (framesStart s rs).mem.readW (s.gpr .rsp - BitVec.ofNat 64 (8 * (j + 1))) 64 = s.gpr rs[j] := by
  induction rs generalizing s j with
  | nil => exact absurd bound (Nat.not_lt_zero _)
  | cons r rs ih =>
    simp only [List.mem_cons, not_or] at notSp
    have enough : 8 ≤ (s.gpr .rsp).toNat := by simp only [List.length_cons] at space; omega
    have innerSpace : 8 * rs.length ≤ ((pushed [r] s).gpr .rsp).toNat := by
      rw [pushed_rsp]
      simp only [List.length_singleton, Nat.mul_one]
      rw [toNat_sub_ofNat enough]
      simp only [List.length_cons] at space; omega
    cases j with
    | zero =>
      have stored := (pushRegs_mem s [r] (by simpa using notSp.1) (by simpa using enough)).2 0 (by simp)
      have inner := framesStart_frame (pushed [r] s) rs notSp.2 innerSpace
      have unchanged : (framesStart (pushed [r] s) rs).mem.readW ((pushed [r] s).gpr .rsp) 64 =
          (pushed [r] s).mem.readW ((pushed [r] s).gpr .rsp) 64 := inner.readW
        (r := ⟨(pushed [r] s).gpr .rsp, 8⟩) (Region.contains_self _ _) (by
          intro region hr
          simp only [List.mem_singleton] at hr; subst region
          apply Offset.base_disjoint_below
          have limit := (s.gpr .rsp).isLt
          simp only [List.length_cons] at space; omega) (by decide)
      rw [pushed_rsp] at unchanged
      simp only [List.length_singleton, Nat.mul_one] at unchanged
      exact unchanged.trans stored
    | succ j =>
      have word := ih (pushed [r] s) notSp.2 innerSpace j (by simpa using bound)
      rw [pushed_rsp, pushed_gpr _ _ (fun h => notSp.2 (h ▸ List.getElem_mem _))] at word
      simp only [List.length_singleton, Nat.mul_one] at word
      rw [BitVec.sub_sub, ← BitVec.ofNat_add, show 8 + 8 * (j + 1) = 8 * (j + 1 + 1) by omega] at word
      exact word

theorem framesEnd_mem (t : State) (rs : List Reg) : (framesEnd t rs).mem = t.mem := by
  induction rs with
  | nil => rfl
  | cons r rs ih => exact (popped_mem ..).trans ih

theorem framesEnd_rd (t : State) (rs : List Reg) : (framesEnd t rs).rd = t.rd := by
  induction rs with
  | nil => rfl
  | cons r rs ih => exact (popped_rd ..).trans ih

theorem framesEnd_mxcsr (t : State) (rs : List Reg) : (framesEnd t rs).mxcsr = t.mxcsr := by
  induction rs with
  | nil => rfl
  | cons r rs ih => exact (popped_mxcsr ..).trans ih

/-- The pops: `rsp` back up by `8 |rs|`. -/
theorem framesEnd_rsp (t : State) (rs : List Reg) :
    (framesEnd t rs).gpr .rsp = t.gpr .rsp + BitVec.ofNat 64 (8 * rs.length) := by
  induction rs with
  | nil => simp [framesEnd]
  | cons r rs ih =>
    rw [framesEnd, popped_rsp, ih, BitVec.add_assoc, ← BitVec.ofNat_add]
    simp only [List.length_cons]
    exact congrArg (fun n => t.gpr .rsp + BitVec.ofNat 64 n) (by omega)

/-- The pop of `r` loads it from the stack. -/
theorem popped_self (t : State) {r : Reg} (h : r ≠ .rsp) :
    (popped r 1 t).gpr r = t.mem.readW (t.gpr .rsp) 64 := by
  simp only [popped, popReg, State.setReg]
  simp [h]

/-- The pops leave the registers not in `rs` but `rsp`. -/
theorem framesEnd_other (t : State) (rs : List Reg) {r : Reg} (hr : r ≠ .rsp) (hn : r ∉ rs) :
    (framesEnd t rs).gpr r = t.gpr r := by
  induction rs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mem_cons, not_or] at hn
    exact (popped_gpr _ _ _ hr hn.1).trans (ih hn.2)

/-- The pops restore each register of `rs` from its word, as the pushes
from `s` stored it. -/
theorem framesEnd_restore (s t : State) (rs : List Reg) (notSp : .rsp ∉ rs) (hnd : rs.Nodup)
    (sp : t.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 (8 * rs.length))
    (words : ∀ j (hj : j < rs.length),
      t.mem.readW (s.gpr .rsp - BitVec.ofNat 64 (8 * (j + 1))) 64 = s.gpr rs[j]) :
    ∀ r ∈ rs, (framesEnd t rs).gpr r = s.gpr r := by
  induction rs generalizing s with
  | nil => intro r h; exact absurd h (List.not_mem_nil)
  | cons x xs ih =>
    simp only [List.mem_cons, not_or] at notSp
    have hnd' := List.nodup_cons.mp hnd
    have inner := ih (pushed [x] s) notSp.2 hnd'.2 (by
        rw [sp, pushed_rsp]
        simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.mul_one]
        rw [BitVec.sub_sub, ← BitVec.ofNat_add]
        exact congrArg (fun n => s.gpr .rsp - BitVec.ofNat 64 n) (by omega))
      (fun j hj => by
        rw [pushed_rsp, pushed_gpr _ _ (fun h => notSp.2 (h ▸ List.getElem_mem _))]
        simp only [List.length_singleton, Nat.mul_one]
        rw [BitVec.sub_sub, ← BitVec.ofNat_add, show 8 + 8 * (j + 1) = 8 * (j + 1 + 1) by omega]
        exact words (j + 1) (by simp only [List.length_cons]; omega))
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · rw [framesEnd, popped_self _ (Ne.symm notSp.1), framesEnd_mem, framesEnd_rsp, sp]
      have := words 0 (by simp)
      simp only [List.getElem_cons_zero, Nat.zero_add, Nat.mul_one] at this
      rw [← this]
      congr 1
      simp only [List.length_cons]
      rw [show 8 * (xs.length + 1) = 8 + 8 * xs.length by omega, BitVec.ofNat_add, ← BitVec.sub_sub,
        BitVec.sub_add_cancel]
    · have hrx : r ≠ x := fun h => hnd'.1 (h ▸ hr)
      have hrsp : r ≠ .rsp := fun h => notSp.2 (h ▸ hr)
      rw [framesEnd, popped_gpr _ _ _ hrsp hrx, inner r hr, pushed_gpr _ _ hrsp]

theorem framesEnd_metadata (s t : State) (rs : List Reg)
    (sp : t.gpr .rsp = (framesStart s rs).gpr .rsp) (wr : t.wr = (framesStart s rs).wr) :
    (framesEnd t rs).gpr .rsp = s.gpr .rsp ∧ (framesEnd t rs).wr = s.wr := by
  induction rs generalizing s with
  | nil => exact ⟨sp, wr⟩
  | cons r rs ih =>
    obtain ⟨innerSp, innerWr⟩ := ih (pushed [r] s) sp wr
    constructor
    · rw [framesEnd, popped_rsp, innerSp, pushed_rsp]
      simp only [List.length_singleton, Nat.mul_one, BitVec.sub_add_cancel]
    · rw [framesEnd, popped_wr, innerWr, pushed_wr]; rfl

/-- `frames body rs` from `s`: the body from `framesStart s rs`, leaving `rsp`
and the writable regions as they were, then the pops. -/
theorem frames_ok (s : State) (rs : List Reg) (body : Prog isa) (Q : State → Prop)
    (notSp : .rsp ∉ rs) (space : 8 * rs.length ≤ (s.gpr .rsp).toNat)
    (run : WP isa body (framesStart s rs) fun t =>
      t.gpr .rsp = (framesStart s rs).gpr .rsp ∧ t.wr = (framesStart s rs).wr ∧ Q (framesEnd t rs)) :
    WP isa (frames body rs) s Q := by
  induction rs generalizing s Q with
  | nil => exact WP.mono run fun t h => h.2.2
  | cons r rs ih =>
    simp only [List.mem_cons, not_or] at notSp
    have pushedBound : ((pushed [r] s).gpr .rsp).toNat = (s.gpr .rsp).toNat - 8 := by
      rw [pushed_rsp]
      simp only [List.length_singleton, Nat.mul_one]
      exact toNat_sub_ofNat (by simp only [List.length_cons] at space; omega)
    have innerSpace : 8 * rs.length ≤ ((pushed [r] s).gpr .rsp).toNat := by
      rw [pushedBound]; simp only [List.length_cons] at space; omega
    apply WP.frame (by simp) (by simpa using notSp.1) (Ne.symm notSp.1)
      (by simp only [List.length_cons] at space; simp only [List.length_singleton, Nat.mul_one]; omega)
    apply ih (pushed [r] s) (fun t => t.gpr .rsp = (pushed [r] s).gpr .rsp ∧
      t.wr = (pushed [r] s).wr ∧ Q (popped r 1 t)) notSp.2 innerSpace
    apply run.mono
    rintro t ⟨sp, wr, result⟩
    obtain ⟨endSp, endWr⟩ := framesEnd_metadata (pushed [r] s) t rs sp wr
    exact ⟨sp, wr, endSp, endWr, result⟩

/-- Two runs that agree on the registers `qs`. -/
def AgreeOn (qs : List Reg) (s₁ s₂ : State) : Prop := ∀ q ∈ qs, s₁.gpr q = s₂.gpr q

/-- The frames leak the same if their body does, from runs agreeing on
registers that include `rsp`. -/
theorem frames_ct {qs : List Reg} (hsp : .rsp ∈ qs) {body : Prog isa}
    (hb : RelCT isa (AgreeOn qs) body fun _ _ => True) :
    ∀ rs : List Reg, RelCT isa (AgreeOn qs) (frames body rs) fun _ _ => True
  | [] => hb
  | r :: rs => RelCT.frame (fun _ _ h => h _ hsp) ((frames_ct hsp hb rs).mono
      (fun a b ⟨s₁, s₂, hp, ha, hb'⟩ q hq => by
        subst ha hb'
        by_cases h : q = .rsp
        · subst h; rw [pushed_rsp, pushed_rsp, hp _ hsp]
        · rw [pushed_gpr _ _ h, pushed_gpr _ _ h, hp _ hq])
      (fun _ _ _ => trivial))

end VG.Proof.P521Field.X86_64
