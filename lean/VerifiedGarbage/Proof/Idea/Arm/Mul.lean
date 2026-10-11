import VerifiedGarbage.Proof.Idea.Arith32
import VerifiedGarbage.Impl.Idea.Arm
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd

/-!
# IDEA on ARMv7: ⊙ without branches

`mul_run`: `mulCode d a b` leaves `a ⊙ b` (of their low 16 bits) in `d`, and
changes nothing but `r8`, `r9` and `d`, given the mask `0xffff` in `r12`.
The arithmetic is `Proof.Idea.prep32_toNat` and `Proof.Idea.reduce32`.
-/

namespace VG.Proof.Idea.Arm

open VG VG.Arm VG.Impl.Idea.Arm

/-- What a block keeps: every register but `written`, memory, regions and `sp`. -/
structure Keep (written : List Reg) (s s' : State) : Prop where
  reg : ∀ r, r ∉ written → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Keep.refl (rs : List Reg) (s : State) : Keep rs s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem Keep.trans {rs : List Reg} {s s' s'' : State}
    (h : Keep rs s s') (h' : Keep rs s' s'') : Keep rs s s'' :=
  ⟨fun r hr => (h'.reg r hr).trans (h.reg r hr), h'.mem.trans h.mem,
    h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp⟩

theorem Keep.mono {rs rs' : List Reg} {s s' : State} (h : Keep rs s s')
    (hs : ∀ r ∈ rs, r ∈ rs') : Keep rs' s s' :=
  ⟨fun r hr => h.reg r fun hm => hr (hs r hm), h.mem, h.rd, h.wr, h.sp⟩

/-- `Keep.mono` for literal lists, by evaluation. -/
theorem Keep.weaken {rs rs' : List Reg} {s s' : State} (h : Keep rs s s')
    (hs : (rs.all fun r => rs'.contains r) = true) : Keep rs' s s' :=
  h.mono fun r hr => by
    have := List.all_eq_true.mp hs r hr
    simpa using this

theorem runBlock_append (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rw [List.nil_append, runBlock_nil, Option.bind_some]
  | cons i is ih =>
    show (isa.exec i s).bind _ = ((isa.exec i s).bind _).bind _
    cases isa.exec i s with
    | none => rfl
    | some s' => exact ih s'

theorem run_append {a b : List Instr} {s s₁ s₂ : State}
    (h₁ : runBlock isa a s = some s₁) (h₂ : runBlock isa b s₁ = some s₂) :
    runBlock isa (a ++ b) s = some s₂ := by
  rw [runBlock_append, h₁, Option.bind_some, h₂]

theorem enc_one : encodable 1 = true := by decide

theorem mul_ofNat32 (x y : BitVec 32) : x * y = BitVec.ofNat 32 (x.toNat * y.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat]

/-- The mask `0xffff` is in `r12`. -/
abbrev MaskOk (s : State) : Prop := s.gpr .r12 = 65535

macro "keep_tac" : tactic => `(tactic| (
  refine ⟨fun q hq => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
  simp only [RegUpd.gpr_setReg, hq, ite_false]))

theorem mul_run (d a b : Reg) (hb : b ≠ .r8) (s : State) (hm : MaskOk s) :
    ∃ s', runBlock isa (mulCode d a b) s = some s' ∧
      s'.gpr d = (Spec.Idea.mul ((s.gpr a).setWidth 16) ((s.gpr b).setWidth 16)).setWidth 32 ∧
      Keep [.r8, .r9, d] s s' := by
  have hm' : (65535 : BitVec 32).toNat = 65535 := rfl
  simp only [mulCode, runBlock_cons, runStep_some, runBlock_nil, isa, exec, Op2.eval, enc_one,
    ↓reduceIte, Option.map_some, RegUpd.gpr_setReg, reduceCtorEq, hm, hb,
    Nat.reduceLeDiff, and_self, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_⟩
  · have hA := prep32_toNat (s.gpr a) 65535 hm'
    have hB := prep32_toNat (s.gpr b) 65535 hm'
    have hp₀ := Nat.mul_le_mul (residue_pos (s.gpr a |>.setWidth 16)) (residue_pos (s.gpr b |>.setWidth 16))
    have hp := Nat.mul_le_mul (residue_le (s.gpr a |>.setWidth 16)) (residue_le (s.gpr b |>.setWidth 16))
    rw [mul32_toNat]
    refine reduce32 _ hp₀ (Nat.le_trans hp (by decide)) _ 65535 1 ?_ hm' rfl
    rw [BitVec.toNat_sub, mul_ofNat32, hA, hB, BitVec.toNat_ofNat]
    show (2 ^ 32 - 1 + _ % 2 ^ 32) % 2 ^ 32 = _
    have := Nat.le_trans hp (show 2 ^ 16 * 2 ^ 16 ≤ 2 ^ 32 by decide)
    have := Nat.le_trans (show 1 ≤ 1 * 1 by decide) hp₀
    omega
  · keep_tac

end VG.Proof.Idea.Arm
