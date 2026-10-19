module

public import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx512.Step
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# An AVX-512 round on the machine

`round_ok`: the code of a round reads the round key at the key pointer
`r8` into `rax`, advances the pointer by the step `r9`, and does to the 64
state words what `roundW` does, with the key's low 48 bits.
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86_64.BitslicedAvx512

open VG VG.X86_64 VG.X86_64.StraightZ VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64.BitsliceAvx512
open VG.Impl.TripleDes.Bitslice
open VG.Proof.TripleDes.Bitslice (step steps roundW steps_succ steps_congr rdOff wrOff flipRole rdOff_flip
  wrOff_flip)

/-! ## The round key -/

theorem keyLoad_ok {s : State} (hkey : InRegions (s.rd ++ s.wr) (s.gpr .r8) 8) :
    ∃ s', runBlock isa keyLoad s = some s' ∧
      s'.gpr .rax = (s.mem.readW (s.gpr .r8) 64).rotateRight 48 ∧
      s'.gpr .r8 = s.gpr .r8 + s.gpr .r9 ∧ (∀ r, r ≠ .rax → r ≠ .r8 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let kp := s.gpr .r8
  let K := s.mem.readW kp 64
  let δ := s.gpr .r9
  let s₁ := s.setReg .rax K
  have e₁ : exec (.mov .rax (.mem { base := .r8, disp := 0 })) s = some s₁ := by
    have hea : s.ea { base := .r8, disp := 0 } = kp := by simp [State.ea, kp]
    have hl : s.load64 kp = some K := by simp only [State.load64, hkey, ite_true, kp, K]
    simp only [exec, readSrc, hea, hl, Option.map_some]
    rfl
  let v := kp + δ
  let s₂ := (arithFlags s₁ v (decide (2 ^ 64 ≤ kp.toNat + δ.toNat)) (addOverflow kp δ v)).setReg .r8 v
  have e₂ : exec (.alu .add .r8 (.reg .r9)) s₁ = some s₂ := by
    simp only [exec, execAlu, readSrc, Option.bind_some]
    have ha : s₁.gpr .r8 = kp := by simp [s₁, gpr_setReg, kp]
    have hd : s₁.gpr .r9 = δ := by simp [s₁, gpr_setReg, δ]
    rw [ha, hd]
  let s₃ := (s₂.setFlags (some ((s₂.gpr .rax).rotateRight 48).msb) none s₂.zf s₂.sf).setReg .rax
    ((s₂.gpr .rax).rotateRight 48)
  have e₃ : exec (.shift .ror .rax 48) s₂ = some s₃ := by
    simp only [exec, execShift]; rfl
  refine ⟨s₃, ?_, ?_, ?_, fun r h1 h2 => ?_, ?_, ?_, ?_⟩
  · rw [keyLoad, runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃,
      runStep_some, runBlock_nil]
  · simp [s₃, s₂, s₁, gpr_setReg, K, kp]
  · simp [s₃, s₂, gpr_setReg, gpr_setFlags, v, kp, δ]
  · simp [s₃, s₂, s₁, gpr_setReg, gpr_setFlags, h1, h2]
  · simp [s₃, s₂, s₁, mem_setReg, mem_setFlags, mem_arithFlags]
  · simp [s₃, s₂, s₁, rd_setReg, rd_setFlags, rd_arithFlags]
  · simp [s₃, s₂, s₁, wr_setReg, wr_setFlags, wr_arithFlags]

/-! ## The S-boxes -/

def stepsCode (n : Nat) : List Instr := (List.range n).flatMap sboxStep

theorem stepsCode_succ (n : Nat) :
    stepsCode (n + 1) = stepsCode n ++ sboxStep n := by
  simp only [stepsCode, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

/-- S-box `j`'s key bits are at the top of the rotated key, shifted by the
bits of the S-boxes before it. -/
theorem keyBits (K : BitVec 64) {j i : Nat} (hj : j < 8) (hi : i < 6) :
    (K.rotateRight 48 <<< (6 * j)).getLsbD (58 + i) = (K.setWidth 48).getLsbD (inBit j i) := by
  rw [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_rotateRight, BitVec.getLsbD_setWidth]
  have h1 : ¬ 58 + i < 6 * j := by omega
  have h2 : ¬ 58 + i - 6 * j < 64 - 48 % 64 := by omega
  have h3 : 58 + i - 6 * j - (64 - 48 % 64) = inBit j i := by unfold inBit; omega
  have h4 : inBit j i < 48 := by unfold inBit; omega
  simp only [h1, decide_false, Bool.not_false, Bool.true_and, h2, ite_false, h3, h4, decide_true,
    Bool.true_and, show 58 + i < 64 by omega, show 58 + i - 6 * j < 64 by omega]

theorem stepsCode_ok (ρ : Role) (K : BitVec 64) {n : Nat} (hn : n ≤ 8) {s : State} (h : Room s)
    (hp : Ptrs ρ s) (hr : s.gpr .rax = K.rotateRight 48) :
    ∃ s', runBlock isa (stepsCode n) s = some s' ∧
      (∀ x < 64, words s' x = steps ρ (K.setWidth 48) n (words s) x) ∧
      s'.gpr .rax = K.rotateRight 48 <<< (6 * n) ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [spillR s, stateR s] s.mem s'.mem := by
  induction n with
  | zero => exact ⟨s, runBlock_nil, fun _ _ => rfl, by simp [hr], fun _ _ _ => rfl, rfl, rfl,
      Frame.refl _ _⟩
  | succ n ih =>
    obtain ⟨s₁, run₁, w₁, r₁, g₁, rd₁, wr₁, f₁⟩ := ih (by omega)
    have c₁ := g₁ .rcx (by decide) (by decide)
    have si₁ := g₁ .rsi (by decide) (by decide)
    have h₁ := h.congr c₁ si₁ wr₁
    have hp₁ : Ptrs ρ s₁ := hp.congr (g₁ _ (by decide) (by decide)) (g₁ _ (by decide) (by decide)) si₁
    obtain ⟨s₂, run₂, w₂, r₂, g₂, rd₂, wr₂, f₂⟩ :=
      sboxStep_ok ρ (by omega : n < 8) h₁ hp₁ (K.setWidth 48)
        (fun i hi => by rw [r₁]; exact keyBits K (by omega) hi)
    refine ⟨s₂, ?_, fun x hx => ?_, ?_, fun r h1 h2 => (g₂ r h1 h2).trans (g₁ r h1 h2),
      rd₂.trans rd₁, wr₂.trans wr₁, ?_⟩
    · rw [stepsCode_succ]; exact runBlock_cat_some run₁ run₂
    · rw [w₂ x hx, steps_succ]
      exact VG.Proof.TripleDes.Bitslice.step_congr ρ _ (by omega) w₁ (w₁ x hx)
    · rw [r₂, r₁, ← BitVec.shiftLeft_add, show 6 * n + 6 = 6 * (n + 1) by omega]
    · rw [show spillR s₁ = spillR s by simp only [spillR, c₁],
        show stateR s₁ = stateR s by simp only [stateR, si₁]] at f₂
      exact f₁.trans f₂

/-! ## Counting down a register -/

theorem sub1_run (s : State) (r : Reg) :
    ∃ s', runBlock isa [.alu .sub r (.imm 1)] s = some s' ∧ s'.gpr r = s.gpr r - 1 ∧
      s'.zf = some (s.gpr r - 1 == 0) ∧ (∀ r', r' ≠ r → s'.gpr r' = s.gpr r') ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let v := s.gpr r
  let t := v - (1 : BitVec 32).signExtend 64
  refine ⟨(arithFlags s t (decide (v.toNat < ((1 : BitVec 32).signExtend 64).toNat))
    (subOverflow v ((1 : BitVec 32).signExtend 64) t)).setReg r t, ?_, ?_, ?_, fun r' h => ?_,
    ?_, ?_, ?_⟩
  · rw [runBlock_cons]; rfl
  · simp only [gpr_setReg_self]; rfl
  · simp only [zf_setReg, zf_arithFlags]; rfl
  · simp [gpr_setReg, h]
  · simp [mem_setReg, mem_arithFlags]
  · simp [rd_setReg, rd_arithFlags]
  · simp [wr_setReg, wr_arithFlags]

/-! ## The halves' pointers -/

theorem swapPtrs_run (s : State) :
    ∃ s', runBlock isa swapPtrs s = some s' ∧ s'.gpr .r12 = s.gpr .r13 ∧ s'.gpr .r13 = s.gpr .r12 ∧
      (∀ r, r ≠ .rbx → r ≠ .r12 → r ≠ .r13 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let s₁ := s.setReg .rbx (s.gpr .r12)
  let s₂ := s₁.setReg .r12 (s₁.gpr .r13)
  let s₃ := s₂.setReg .r13 (s₂.gpr .rbx)
  refine ⟨s₃, ?_, ?_, ?_, fun r a b c => ?_, ?_, ?_, ?_⟩
  · rw [swapPtrs, runBlock_cons, show exec (.mov .rbx (.reg .r12)) s = some s₁ from rfl, runStep_some,
      runBlock_cons, show exec (.mov .r12 (.reg .r13)) s₁ = some s₂ from rfl, runStep_some,
      runBlock_cons, show exec (.mov .r13 (.reg .rbx)) s₂ = some s₃ from rfl, runStep_some, runBlock_nil]
  · simp [s₃, s₂, s₁, gpr_setReg]
  · simp [s₃, s₂, s₁, gpr_setReg]
  · simp [s₃, s₂, s₁, gpr_setReg, a, b, c]
  · simp [s₃, s₂, s₁, mem_setReg]
  · simp [s₃, s₂, s₁, rd_setReg]
  · simp [s₃, s₂, s₁, wr_setReg]

/-! ## A round -/

theorem round_eq : round = keyLoad ++ stepsCode 8 ++ swapPtrs ++ ([.alu .sub .r10 (.imm 1)] : List Instr) :=
  rfl

theorem round_ok (ρ : Role) {s : State} (h : Room s) (hp : Ptrs ρ s)
    (hkey : InRegions (s.rd ++ s.wr) (s.gpr .r8) 8) :
    ∃ s', runBlock isa round s = some s' ∧
      (∀ x < 64, words s' x = roundW ρ ((s.mem.readW (s.gpr .r8) 64).setWidth 48) (words s) x) ∧
      s'.gpr .r8 = s.gpr .r8 + s.gpr .r9 ∧
      s'.gpr .r10 = s.gpr .r10 - 1 ∧ s'.zf = some (s.gpr .r10 - 1 == 0) ∧ Ptrs (flipRole ρ) s' ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .r8 → r ≠ .r10 → r ≠ .r12 → r ≠ .r13 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [spillR s, stateR s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, r₁, k₁, g₁, m₁, rd₁, wr₁⟩ := keyLoad_ok hkey
  have c₁ := g₁ .rcx (by decide) (by decide)
  have si₁ := g₁ .rsi (by decide) (by decide)
  have h₁ := h.congr c₁ si₁ wr₁
  have hp₁ : Ptrs ρ s₁ := hp.congr (g₁ _ (by decide) (by decide)) (g₁ _ (by decide) (by decide)) si₁
  obtain ⟨s₂, run₂, w₂, -, g₂, rd₂, wr₂, f₂⟩ :=
    stepsCode_ok ρ _ (Nat.le_refl 8) h₁ hp₁ r₁
  obtain ⟨s₃, run₃, p12₃, p13₃, g₃, m₃, rd₃, wr₃⟩ := swapPtrs_run s₂
  obtain ⟨s₄, run₄, cnt₄, zf₄, g₄, m₄, rd₄, wr₄⟩ := sub1_run s₃ .r10
  have g₂₁ : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .r8 → s₂.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [g₂ r h1 h2, g₁ r h1 h3]
  have g₄₃ : ∀ r, r ≠ .rbx → r ≠ .r10 → r ≠ .r12 → r ≠ .r13 → s₄.gpr r = s₂.gpr r := fun r a b c d => by
    rw [g₄ r b, g₃ r a c d]
  have r10₃ : s₃.gpr .r10 = s.gpr .r10 := by
    rw [g₃ _ (by decide) (by decide) (by decide), g₂₁ _ (by decide) (by decide) (by decide)]
  have si₄ : s₄.gpr .rsi = s.gpr .rsi := by
    rw [g₄₃ _ (by decide) (by decide) (by decide) (by decide), g₂₁ _ (by decide) (by decide) (by decide)]
  have e₄ : ∀ y, words s₄ y = words s₂ y := fun y => by
    simp only [words, m₄, m₃, si₄, g₂₁ .rsi (by decide) (by decide) (by decide)]
  refine ⟨s₄, ?_, fun x hx => ?_, ?_, by rw [cnt₄, r10₃], by rw [zf₄, r10₃], ⟨?_, ?_⟩,
    fun r h1 h2 h3 h4 h5 h6 => ?_, rd₄.trans (rd₃.trans (rd₂.trans rd₁)),
    wr₄.trans (wr₃.trans (wr₂.trans wr₁)), ?_⟩
  · rw [round_eq]
    exact runBlock_cat_some (runBlock_cat_some (runBlock_cat_some run₁ run₂) run₃) run₄
  · rw [e₄ x, w₂ x hx]
    have e : ∀ y, words s₁ y = words s y := fun y => by simp only [words, m₁, si₁]
    exact steps_congr ρ _ (Nat.le_refl 8) (fun y _ => e y) x hx
  · rw [g₄₃ _ (by decide) (by decide) (by decide) (by decide), g₂ _ (by decide) (by decide), k₁]
  · rw [g₄ _ (by decide), p12₃, si₄, g₂₁ _ (by decide) (by decide) (by decide), hp.wr, rdOff_flip]
  · rw [g₄ _ (by decide), p13₃, si₄, g₂₁ _ (by decide) (by decide) (by decide), hp.rd, wrOff_flip]
  · rw [g₄₃ r h2 h4 h5 h6, g₂₁ r h1 h2 h3]
  · rw [show spillR s₁ = spillR s by simp only [spillR, c₁],
      show stateR s₁ = stateR s by simp only [stateR, si₁]] at f₂
    rw [m₁] at f₂
    rw [m₄, m₃]
    exact f₂

end VG.Proof.TripleDes.X86_64.BitslicedAvx512
