import VerifiedGarbage.Proof.X25519.X86_64.Step
import VerifiedGarbage.Proof.Divstep.WordDef

/-!
# X25519 on x86-64, inversion by divsteps: the word divstep

One divstep on words (`dstep`) leaves in `rbx`, `rcx`, `rbp` and `r9`–`r12`
the words of `Proof/Divstep/WordDef.lean`'s `wstep` (`dstep_ok`), given
`r13 = (d >>> 63) ^ 1` (whether `d ≥ 0`), which it keeps. The proof splits
on the three kinds of step (`g` odd and `d ≥ 0`, `g` odd and `d < 0`, `g`
even) before running the block, so that every `cmov` is decided.
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64
open VG.Proof.Divstep (WSt wstep)

/-- Whether `d ≥ 0`, as `0` or `1`. -/
def dmOf (D : BitVec 64) : BitVec 64 := (D >>> 63) ^^^ 1

/-- The words of a divstep: `d`, `f`, `g`, `u`, `v`, `q`, `r`. -/
def regsD (s : State) : WSt :=
  ⟨s.gpr .rbx, s.gpr .rcx, s.gpr .rbp, s.gpr .r9, s.gpr .r10, s.gpr .r11, s.gpr .r12⟩

/-- The registers a divstep writes. -/
abbrev dRegs : List Reg := [.rax, .rbx, .rcx, .rdx, .rbp, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

theorem neg_sel (X : BitVec 64) : (X ^^^ BitVec.allOnes 64) - BitVec.allOnes 64 = -X := by
  have h := BitVec.neg_eq_not_add X
  have h1 : BitVec.allOnes 64 = -1 := by decide
  rw [BitVec.xor_allOnes, h1, h]; grind

theorem shl1 (x : BitVec 64) : x <<< 1 = x + x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_add, Nat.shiftLeft_eq, Nat.pow_one]
  omega

theorem c_allOnes : (0 : BitVec 64) - 1 = BitVec.allOnes 64 := by decide
theorem ones_lit : (18446744073709551615#64) = BitVec.allOnes 64 := by decide
theorem and_ones (x : BitVec 64) : x &&& 18446744073709551615#64 = x := by
  rw [ones_lit, BitVec.and_allOnes]
theorem c_one : (1 : BitVec 64) - 1 = 0 := by decide

/-- `g` odd and `d ≥ 0`: the swap. -/
theorem wstep_swap (w : WSt) (hB : w.G &&& 1 = 1) (hS : w.D >>> 63 = 0) :
    wstep w = ⟨2 - w.D, w.G, (w.G - w.F) >>> 1, w.Q + w.Q, w.R + w.R, w.Q - w.U, w.R - w.V⟩ := by
  simp only [wstep, hB, hS, c_allOnes, BitVec.and_allOnes, neg_sel, shl1, ← BitVec.sub_eq_add_neg,
    WSt.mk.injEq]
  refine ⟨by grind, by grind, trivial, by grind, by grind, trivial, trivial⟩

/-- `g` odd and `d < 0`: `g + f`. -/
theorem wstep_odd (w : WSt) (hB : w.G &&& 1 = 1) (hS : w.D >>> 63 = 1) :
    wstep w = ⟨w.D + 2, w.F, (w.G + w.F) >>> 1, w.U + w.U, w.V + w.V, w.Q + w.U, w.R + w.V⟩ := by
  simp only [wstep, hB, hS, c_allOnes, c_one]
  simp [shl1]
  simp only [and_ones, and_self]

/-- `g` even. -/
theorem wstep_even (w : WSt) (hB : w.G &&& 1 = 0) :
    wstep w = ⟨w.D + 2, w.F, w.G >>> 1, w.U + w.U, w.V + w.V, w.Q, w.R⟩ := by
  simp only [wstep, hB]
  simp [shl1]

theorem dz2 : (2 : BitVec 32).setWidth 64 = 2 := by decide
theorem ds2 : (2 : BitVec 32).signExtend 64 = 2 := by decide
theorem ds1 : (1 : BitVec 32).signExtend 64 = 1 := by decide
theorem b10 : ((1 : BitVec 64) == 0) = false := by decide
theorem b00 : ((0 : BitVec 64) == 0) = true := by decide
theorem and0 (x : BitVec 64) : x &&& 0 = 0 := by simp
theorem x01 : (0 : BitVec 64) ^^^ 1 = 1 := by decide
theorem x11 : (1 : BitVec 64) ^^^ 1 = 0 := by decide

/-- Runs a block by symbolic execution, reading registers through the
writes and deciding the `cmov`s from the given facts. -/
syntax "drun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| drun) => `(tactic| drun [])
  | `(tactic| drun [$ls,*]) => `(tactic| (
      apply WP.of_runBlock
      set_option linter.unusedSimpArgs false in
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
        execShift, execMul, execCmov, eval, State.setReg32, Option.bind_some,
        Option.map_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags,
        RegUpd.zf_setReg, RegUpd.zf_arithFlags, RegUpd.cf_setReg, RegUpd.cf_arithFlags,
        RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
        RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setFlags,
        RegUpd.rd_setFlags, RegUpd.wr_setFlags, ite_true, ite_false, reduceCtorEq, Nat.le_refl,
        true_and, and_true, and_self, Nat.reduceLeDiff, Nat.reduceSub, Nat.reduceEqDiff, ↓reduceIte,
        Option.some.injEq, exists_eq_left', Bool.not_false, Bool.not_true, dz2, ds2, ds1, b10, b00,
        $ls,*]))

/-- Closes `Keeps dRegs s t` after a run. -/
macro "dkeep" : tactic => `(tactic| (
  refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, h1, h2, h3, h4, h5, h6, h7,
    h8, h9, h10, h11, h12, ↓reduceIte]))

theorem dKeep {s t : State} (h : ∀ r, r ∉ dRegs → t.gpr r = s.gpr r) (hm : t.mem = s.mem)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) : Keeps dRegs s t := ⟨h, hm, hr, hw⟩

/-- A divstep on words: even, `d ≥ 0`. -/
theorem dstep_even0 (s : State) (hB : s.gpr .rbp &&& 1 = 0) (h13 : s.gpr .r13 = 0 ^^^ 1) :
    WP isa (.block dstep) s fun t =>
      regsD t = wstep (regsD s) ∧ t.gpr .r13 = dmOf (t.gpr .rbx) ∧ Keeps dRegs s t := by
  rw [wstep_even (regsD s) hB]
  drun [dstep, h13, hB, x01, x11, and0, regsD, dmOf, WSt.mk.injEq]
  dkeep

/-- A divstep on words: even, `d < 0`. -/
theorem dstep_even1 (s : State) (hB : s.gpr .rbp &&& 1 = 0) (h13 : s.gpr .r13 = 1 ^^^ 1) :
    WP isa (.block dstep) s fun t =>
      regsD t = wstep (regsD s) ∧ t.gpr .r13 = dmOf (t.gpr .rbx) ∧ Keeps dRegs s t := by
  rw [wstep_even (regsD s) hB]
  drun [dstep, h13, hB, x01, x11, and0, regsD, dmOf, WSt.mk.injEq]
  dkeep

/-- A divstep on words: the swap. -/
theorem dstep_swap (s : State) (hB : s.gpr .rbp &&& 1 = 1) (hS : s.gpr .rbx >>> 63 = 0) (h13 : s.gpr .r13 = 0 ^^^ 1) :
    WP isa (.block dstep) s fun t =>
      regsD t = wstep (regsD s) ∧ t.gpr .r13 = dmOf (t.gpr .rbx) ∧ Keeps dRegs s t := by
  rw [wstep_swap (regsD s) hB hS]
  drun [dstep, h13, hB, hS, x01, x11, and0, regsD, dmOf, WSt.mk.injEq]
  dkeep

/-- A divstep on words: odd, `d < 0`. -/
theorem dstep_odd (s : State) (hB : s.gpr .rbp &&& 1 = 1) (hS : s.gpr .rbx >>> 63 = 1) (h13 : s.gpr .r13 = 1 ^^^ 1) :
    WP isa (.block dstep) s fun t =>
      regsD t = wstep (regsD s) ∧ t.gpr .r13 = dmOf (t.gpr .rbx) ∧ Keeps dRegs s t := by
  rw [wstep_odd (regsD s) hB hS]
  drun [dstep, h13, hB, hS, x01, x11, and0, regsD, dmOf, WSt.mk.injEq]
  dkeep

/-- One divstep on words. -/
theorem dstep_ok (s : State) (h13 : s.gpr .r13 = dmOf (s.gpr .rbx)) :
    WP isa (.block dstep) s fun t =>
      regsD t = wstep (regsD s) ∧ t.gpr .r13 = dmOf (t.gpr .rbx) ∧ Keeps dRegs s t := by
  have hB : s.gpr .rbp &&& 1 = 0 ∨ s.gpr .rbp &&& 1 = 1 := by
    have e : (s.gpr .rbp &&& 1).toNat = (s.gpr .rbp).toNat % 2 := by
      rw [BitVec.toNat_and, show (1 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod]
    rcases Nat.mod_two_eq_zero_or_one (s.gpr .rbp).toNat with h | h
    · exact Or.inl (BitVec.eq_of_toNat_eq (by rw [e, h]; rfl))
    · exact Or.inr (BitVec.eq_of_toNat_eq (by rw [e, h]; rfl))
  have hS : s.gpr .rbx >>> 63 = 0 ∨ s.gpr .rbx >>> 63 = 1 := by
    have h := (s.gpr .rbx).isLt
    rcases Nat.lt_or_ge (s.gpr .rbx).toNat (2 ^ 63) with h' | h'
    · exact Or.inl (BitVec.eq_of_toNat_eq (by
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; simp; omega))
    · exact Or.inr (BitVec.eq_of_toNat_eq (by
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; simp; omega))
  rw [dmOf] at h13
  rcases hB with hB | hB <;> rcases hS with hS | hS <;> rw [hS] at h13
  · exact dstep_even0 s hB h13
  · exact dstep_even1 s hB h13
  · exact dstep_swap s hB hS h13
  · exact dstep_odd s hB hS h13

end VG.Proof.X25519.X86_64
