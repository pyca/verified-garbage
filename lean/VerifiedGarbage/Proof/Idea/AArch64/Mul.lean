import VerifiedGarbage.Proof.Idea.Arith
import VerifiedGarbage.Impl.Idea.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-!
# IDEA on AArch64: ⊙ without branches

`mul_run`: `mulCode d a b` leaves `a ⊙ b` (of their low 16 bits) in `d`, and
changes nothing but `x11`, `x12` and `d`, given the mask `0xffff` in `x15`.
The arithmetic is `Proof.Idea.prep_toNat` and `Proof.Idea.reduce`.
-/

namespace VG.Proof.Idea.AArch64

open VG VG.AArch64 VG.Impl.Idea.AArch64

/-- What a block keeps: every register but `written`, memory, regions and `sp`. -/
structure Keep (written : List Reg) (s s' : State) : Prop where
  reg : ∀ r, r ∉ written → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Keep.trans {rs : List Reg} {s s' s'' : State}
    (h : Keep rs s s') (h' : Keep rs s' s'') : Keep rs s s'' :=
  ⟨fun r hr => (h'.reg r hr).trans (h.reg r hr), h'.mem.trans h.mem,
    h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp⟩

theorem Keep.mono {rs rs' : List Reg} {s s' : State} (h : Keep rs s s')
    (hs : ∀ r ∈ rs, r ∈ rs') : Keep rs' s s' :=
  ⟨fun r hr => h.reg r fun hm => hr (hs r hm), h.mem, h.rd, h.wr, h.sp⟩

theorem keep_reg_of {written : List Reg} {s s' : State}
    (h : ∀ r, r ∉ written → s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) : Keep written s s' := ⟨h, hm, hrd, hwr, hsp⟩

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

theorem ofNat_one : BitVec.ofNat 64 1 = 1 := rfl

theorem mul_ofNat (x y : BitVec 64) :
    x * y = BitVec.ofNat 64 (x.toNat * y.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat]

/-- The mask `0xffff` is in `x15`. -/
abbrev MaskOk (s : State) : Prop := s.gpr .x15 = 65535

theorem mul_run {d b : Reg} (a : Reg) (hb₁ : b ≠ .x11) (s : State)
    (hm : MaskOk s) :
    ∃ s', runBlock isa (mulCode d a b) s = some s' ∧
      s'.gpr d = (Spec.Idea.mul ((s.gpr a).setWidth 16) ((s.gpr b).setWidth 16)).setWidth 64 ∧
      Keep [.x11, .x12, d] s s' := by
  have hm' : (65535 : BitVec 64).toNat = 65535 := rfl
  simp only [mulCode, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, isa, Size.bits,
    BitVec.setWidth_eq, RegUpd.gpr_write, reduceCtorEq, ↓reduceIte, hm, hb₁,
    Nat.reduceLT, ofNat_one, Option.some.injEq, exists_eq_left']
  refine ⟨?_, keep_reg_of (fun q hq => ?_) rfl rfl rfl rfl⟩
  · have hA := prep_toNat (s.gpr a) 65535 hm'
    have hB := prep_toNat (s.gpr b) 65535 hm'
    have hp : (((s.gpr a - 1 &&& 65535) + 1 : BitVec 64)).toNat *
        (((s.gpr b - 1 &&& 65535) + 1 : BitVec 64)).toNat ≤ 2 ^ 32 := by
      rw [hA, hB]; exact Nat.le_trans (Nat.mul_le_mul (residue_le _) (residue_le _)) (by decide)
    rw [mul_ofNat, reduce _ hp 65535 hm', hA, hB, mul_toNat]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [RegUpd.gpr_write, hq.1, hq.2.1, hq.2.2, ite_false]

end VG.Proof.Idea.AArch64
