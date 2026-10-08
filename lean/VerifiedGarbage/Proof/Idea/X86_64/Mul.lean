import VerifiedGarbage.Spec.Idea
import VerifiedGarbage.Impl.Idea.X86_64
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-!
# IDEA on x86-64: ⊙ without branches

`mul_run`: `mulCode` leaves `rax ⊙ rdx` (of their low 16 bits) in `rdx`,
and changes nothing but `rax`, `rdx` and the flags. The arithmetic is
`prep_toNat` (the operands' residues) and `reduce` (the product modulo
2¹⁶ + 1 from its halves, corrected by the sign of their difference).
-/

namespace VG.Proof.Idea.X86_64

open VG VG.X86_64 VG.Impl.Idea.X86_64

/-- What a block keeps: every register but `written`, memory and regions. -/
structure Keep (written : List Reg) (s s' : State) : Prop where
  reg : ∀ r, r ∉ written → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Keep.trans {rs : List Reg} {s s' s'' : State}
    (h : Keep rs s s') (h' : Keep rs s' s'') : Keep rs s s'' :=
  ⟨fun r hr => (h'.reg r hr).trans (h.reg r hr), h'.mem.trans h.mem,
    h'.rd.trans h.rd, h'.wr.trans h.wr⟩

theorem Keep.mono {rs rs' : List Reg} {s s' : State} (h : Keep rs s s')
    (hs : ∀ r ∈ rs, r ∈ rs') : Keep rs' s s' :=
  ⟨fun r hr => h.reg r fun hm => hr (hs r hm), h.mem, h.rd, h.wr⟩

theorem runBlock_append (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rw [List.nil_append, runBlock_nil, Option.bind_some]
  | cons i is ih =>
    show (isa.exec i s).bind _ = ((isa.exec i s).bind _).bind _
    cases isa.exec i s with
    | none => rfl
    | some s' => exact ih s'

/-- Composing two runs. -/
theorem run_append {a b : List Instr} {s s₁ s₂ : State}
    (h₁ : runBlock isa a s = some s₁) (h₂ : runBlock isa b s₁ = some s₂) :
    runBlock isa (a ++ b) s = some s₂ := by
  rw [runBlock_append, h₁, Option.bind_some, h₂]

theorem signExtend_one : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
theorem signExtend_mask : BitVec.signExtend 64 (65535 : BitVec 32) = 65535 := by decide

theorem mask_toNat (x m : BitVec 64) (hm : m.toNat = 65535) :
    (x &&& m).toNat = x.toNat % 65536 := by
  rw [BitVec.toNat_and, hm, show 65535 = 2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem setWidth16_toNat (x : BitVec 64) : (x.setWidth 16).toNat = x.toNat % 65536 := by
  simp [BitVec.toNat_setWidth]

/-- `((x - 1) & 0xffff) + 1` is the residue of `x`'s low word. -/
theorem prep_toNat (a m : BitVec 64) (hm : m.toNat = 65535) :
    (((a - 1) &&& m) + 1 : BitVec 64).toNat = Spec.Idea.residue (a.setWidth 16) := by
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  rw [BitVec.toNat_add, mask_toNat _ _ hm, BitVec.toNat_sub, h1]
  unfold Spec.Idea.residue
  have hs := setWidth16_toNat a
  split
  · rename_i h
    have h' : a.toNat % 65536 = 0 := by rw [← hs, h]; rfl
    omega
  · rename_i h
    have h' : a.toNat % 65536 ≠ 0 := by
      intro h''; apply h; apply BitVec.eq_of_toNat_eq; rw [hs, h'']; rfl
    rw [hs]; omega

theorem residue_le (a : Spec.Idea.Word) : Spec.Idea.residue a ≤ 2 ^ 16 := by
  unfold Spec.Idea.residue
  split
  · exact Nat.le_refl _
  · exact Nat.le_of_lt a.isLt

theorem residue_pos (a : Spec.Idea.Word) : 0 < Spec.Idea.residue a := by
  unfold Spec.Idea.residue
  split
  · decide
  · rename_i h
    exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq h')

/-- The product modulo 2¹⁶ + 1 from its halves, as `mulCode` computes it. -/
theorem reduce (p : Nat) (hp : p ≤ 2 ^ 32) (m : BitVec 64) (hm : m.toNat = 65535) :
    (((BitVec.ofNat 64 p &&& m) - BitVec.ofNat 64 p >>> 16) +
      ((BitVec.ofNat 64 p &&& m) - BitVec.ofNat 64 p >>> 16) >>> 63 +
      (((BitVec.ofNat 64 p &&& m) - BitVec.ofNat 64 p >>> 16) >>> 63) <<< 16) &&& m =
      BitVec.ofNat 64 (p % 65537 % 65536) := by
  have hlo : (BitVec.ofNat 64 p &&& m).toNat = p % 65536 := by
    rw [mask_toNat _ _ hm, BitVec.toNat_ofNat]; omega
  have hhi : (BitVec.ofNat 64 p >>> 16).toNat = p / 65536 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; omega
  generalize hr : (BitVec.ofNat 64 p &&& m) - BitVec.ofNat 64 p >>> 16 = r
  have hrn : r.toNat = (2 ^ 64 - p / 65536 + p % 65536) % 2 ^ 64 := by
    rw [← hr, BitVec.toNat_sub, hlo, hhi]
  apply BitVec.eq_of_toNat_eq
  rw [mask_toNat _ _ hm, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hrn, BitVec.toNat_ofNat]
  generalize hH : p / 65536 = H
  generalize hL : p % 65536 = L
  have hdec : p = 65536 * H + L := by omega
  have hL' : L < 65536 := by omega
  have hH' : H ≤ 65536 := by omega
  subst hdec
  clear hrn hr hlo hhi hH hL hp
  have e1 : (65536 * H + L) % 65537 = (L + 65537 - H) % 65537 := by omega
  rw [e1]
  by_cases hc : L < H
  · have hR : (2 ^ 64 - H + L) % 2 ^ 64 = 2 ^ 64 - (H - L) := by
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    have ht : (2 ^ 64 - (H - L)) / 2 ^ 63 = 1 := by omega
    rw [hR, ht]
    omega
  · have hR : (2 ^ 64 - H + L) % 2 ^ 64 = L - H := by omega
    have ht : (L - H) / 2 ^ 63 = 0 := by omega
    rw [hR, ht]
    omega

theorem mul_toNat (a b : Spec.Idea.Word) :
    (Spec.Idea.mul a b).setWidth 64 =
      BitVec.ofNat 64 (Spec.Idea.residue a * Spec.Idea.residue b % 65537 % 65536) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Spec.Idea.mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-- `mulCode` on the machine. -/
theorem mul_run (s : State) : ∃ s', runBlock isa mulCode s = some s' ∧
    s'.gpr .rdx = (Spec.Idea.mul ((s.gpr .rax).setWidth 16) ((s.gpr .rdx).setWidth 16)).setWidth 64 ∧
    Keep [.rax, .rdx] s s' := by
  simp only [mulCode, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execShift, execMul,
    readSrc, isa, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags,
    ↓reduceIte, reduceCtorEq, Nat.reduceLeDiff, and_self, Option.map_some, signExtend_one,
    signExtend_mask, Option.bind_some, Option.some.injEq, exists_eq_left']
  have hm : (65535 : BitVec 64).toNat = 65535 := rfl
  have hA := prep_toNat (s.gpr .rax) 65535 hm
  have hB := prep_toNat (s.gpr .rdx) 65535 hm
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl⟩⟩
  · rw [hA, hB, mul_toNat]
    exact reduce _ (Nat.le_trans (Nat.mul_le_mul (residue_le _) (residue_le _)) (by decide)) 65535 hm
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.1, hr.2, ite_false]

end VG.Proof.Idea.X86_64
