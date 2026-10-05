import VerifiedGarbage.Impl.Weierstrass.X86_64.Inv
import VerifiedGarbage.Proof.Divstep.Word
import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop

/-!
# Inversion by divsteps on x86-64: the word divstep

One divstep on words (`wstepCode`) leaves in `rbx`, `rcx`, `rbp` and
`r9`–`r12` the words of `Proof/Divstep/Word.lean`'s `wstep` (`wstepCode_ok`);
`N` of them, counted down in `rdx` (`wstepsLoop_ok`), leave its `N` steps.
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open VG.Proof.Divstep (WSt wstep)

/-- The words of a divstep: `d`, `f`, `g`, `u`, `v`, `q`, `r` in `rbx`,
`rcx`, `rbp`, `r9`–`r12`. -/
def regsW (s : State) : WSt :=
  ⟨s.gpr .rbx, s.gpr .rcx, s.gpr .rbp, s.gpr .r9, s.gpr .r10, s.gpr .r11, s.gpr .r12⟩

/-- The registers a divstep writes. -/
abbrev stepRegs : List Reg := [.rax, .rbx, .rcx, .rbp, .r8, .r9, .r10, .r11, .r12, .r13]

theorem sext1 : (1 : BitVec 32).signExtend 64 = 1 := by decide
theorem sext2 : (2 : BitVec 32).signExtend 64 = 2 := by decide
theorem zext0 : (0 : BitVec 32).setWidth 64 = 0 := by decide

/-- Runs a block of register and memory instructions by symbolic execution,
reading registers through the writes. -/
syntax "irun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| irun) => `(tactic| irun [])
  | `(tactic| irun [$ls,*]) => `(tactic| (
      apply WP.of_runBlock
      set_option linter.unusedSimpArgs false in
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
        execShift, execMul, State.setReg32, Option.bind_some,
        Option.map_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags,
        RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.cf_arithFlags,
        RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setFlags,
        RegUpd.rd_setFlags, RegUpd.wr_setFlags, ite_true, ite_false, reduceCtorEq, Nat.le_refl,
        true_and, and_true, and_self, Nat.reduceLeDiff, Nat.reduceSub, Nat.reduceEqDiff, ↓reduceIte,
        Option.some.injEq, exists_eq_left', sext1, sext2, zext0, $ls,*]))

/-- One divstep on words. -/
theorem wstepCode_ok (s : State) :
    WP isa (.block wstepCode) s fun t => regsW t = wstep (regsW s) ∧ Keeps stepRegs s t := by
  irun [wstepCode, condAdd, swapAdd, List.cons_append, List.nil_append]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [regsW, wstep, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, reduceCtorEq,
      ↓reduceIte, Divstep.shl1]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, h1, h2, h3, h4, h5, h6, h7, h8, h9,
      h10, ↓reduceIte]

/-- `rdx -= 1`, its zero flag whether it is now zero. -/
theorem decRdx_ok (s : State) {j : Nat} (hj : 1 ≤ j) (hj' : j < 2 ^ 64) (hb : s.gpr .rdx = BitVec.ofNat 64 j) :
    WP isa (.block [.alu .sub .rdx (.imm 1)]) s fun s' =>
      s'.gpr .rdx = BitVec.ofNat 64 (j - 1) ∧ s'.zf = some (decide (j - 1 = 0)) ∧ Keeps [.rdx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    RegUpd.gpr_setReg, RegUpd.zf_setReg, RegUpd.zf_arithFlags, ite_true, Option.some.injEq, exists_eq_left', hb,
    sext1]
  have e : BitVec.ofNat 64 j - 1 = BitVec.ofNat 64 (j - 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
    rw [Nat.mod_eq_of_lt hj', Nat.mod_eq_of_lt (by omega : j - 1 < 2 ^ 64)]
    omega
  refine ⟨e, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [e]
    congr 1
    by_cases h : j - 1 = 0
    · rw [h]; simp
    · rw [decide_eq_false h]
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro he
      have := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      exact h this
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- `N ≥ 1` word divsteps, counted down in `rdx`. -/
theorem wstepsLoop_ok {N : Nat} (hN : 1 ≤ N) (hN' : N < 2 ^ 31) (s : State) :
    WP isa (wsteps N) s fun t =>
      regsW t = Divstep.wsteps N (regsW s) ∧ Keeps (.rdx :: stepRegs) s t := by
  rw [wsteps]
  refine WP.seq ?_
  have h0 : WP isa (.block [.mov32 .rdx (.imm (BitVec.ofNat 32 N))]) s fun t =>
      t.gpr .rdx = BitVec.ofNat 64 N ∧ Keeps [.rdx] s t := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32, Option.map_some,
      RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    · simp only [List.mem_singleton] at hr; simp only [RegUpd.gpr_setReg, hr, ite_false]
  refine WP.mono h0 fun s₁ ⟨c₁, k₁⟩ => ?_
  have e₁ : regsW s₁ = regsW s := by
    simp only [regsW, k₁.1 .rbx (by decide), k₁.1 .rcx (by decide), k₁.1 .rbp (by decide),
      k₁.1 .r9 (by decide), k₁.1 .r10 (by decide), k₁.1 .r11 (by decide), k₁.1 .r12 (by decide)]
  refine countLoop_ok (n := N)
    (Inv := fun j t => regsW t = Divstep.wsteps (N - j) (regsW s) ∧ t.gpr .rdx = BitVec.ofNat 64 j ∧
      Keeps (.rdx :: stepRegs) s t)
    (fun j t hj1 hjN ⟨rt, t13, kt⟩ => ?_) (fun t ⟨rt, _, kt⟩ => ⟨by simpa using rt, kt⟩) hN
    ⟨by rw [Nat.sub_self, e₁]; rfl, c₁, k₁.mono (by decide)⟩
  rw [WP.block_append_iff]
  refine WP.mono (wstepCode_ok t) fun u ⟨ru, ku⟩ => ?_
  refine WP.mono (decRdx_ok u hj1 (by omega) (by rw [ku.1 .rdx (by decide), t13])) fun w ⟨xw, zw, kw⟩ =>
    ⟨⟨?_, xw, (kt.trans (ku.mono (by decide))).trans (kw.mono (by decide))⟩, zw⟩
  have ew : regsW w = regsW u := by
    simp only [regsW, kw.1 .rbx (by decide), kw.1 .rcx (by decide), kw.1 .rbp (by decide),
      kw.1 .r9 (by decide), kw.1 .r10 (by decide), kw.1 .r11 (by decide), kw.1 .r12 (by decide)]
  rw [ew, ru, rt, show N - (j - 1) = (N - j) + 1 by omega, Divstep.wsteps_succ]

end VG.Proof.Weierstrass.X86_64
