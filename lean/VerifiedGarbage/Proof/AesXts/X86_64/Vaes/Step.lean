module
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.AesXts.X86_64Vaes
public import VerifiedGarbage.Proof.Aes.X86_64.Lit
public import VerifiedGarbage.Proof.AesXts.Alpha16
public import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Semantics

import VerifiedGarbage.Proof.AesXts.X86_64.Clmul87
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.Block

/-!
# One-pass XTS-AES on x86-64: the tweaks times `α⁸`

`stepT_ok`: `stepT t` replaces both lanes of the tweak register `t`, words
`v`, with `stepW v`, `v` shifted left by eight bits XORed with
`P (v >>> 120)` (`vpsrldq`, `vpclmulqdq` with `0x87`, `vpslldq`, `vpxor`),
whose bytes are those of the tweak eight blocks on (`next_b8`).
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.Vaes

open VG VG.X86_64
open VG.Impl.AesXts.X86_64Vaes (stepT)
open VG.Proof.AesXts (P)

/-- A tweak eight blocks on, as a word. -/
def stepW (v : BitVec 128) : BitVec 128 := (v <<< 8) ^^^ P (v >>> 120)

theorem setWidth_qword_shr120 (v : BitVec 128) : (qword (v >>> 120) 0).setWidth 128 = v >>> 120 := by
  ext i hi
  simp only [qword, BitVec.getElem_setWidth, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight,
    BitVec.getElem_ushiftRight]
  by_cases h : i < 64
  · simp [h]
  · simp only [h, decide_false, Bool.false_and]
    rw [BitVec.getLsbD_of_ge _ _ (by omega)]

theorem pclmul_step (v k : BitVec 128) (hk : qword k 0 = 0x87) :
    pclmul (v >>> 120) k 0 = P (v >>> 120) := by
  simp only [pclmul, show (0 : BitVec 8).getLsbD 0 = false from rfl, show (0 : BitVec 8).getLsbD 4 = false from rfl,
    Bool.false_eq_true, ↓reduceIte, hk, clmul_87, setWidth_qword_shr120]

@[simp] theorem lane_vpclmul256 (d a b : XReg) (n : BitVec 8) (s : State) (r : XReg) (l : Nat) :
    ((VOp.vpclmulqdq .l256 d a b n).exec s).lane r l =
      if r = d then pclmul (s.lane a l) (s.lane b l) n else s.lane r l := by
  simp only [VOp.exec, State.lane, State.setV]
  by_cases h : r = d <;> by_cases hl : l = 0 <;> simp [h, hl]

theorem psrldq_15 (v : BitVec 128) : XShiftOp.eval .psrldq v 15 = v >>> 120 := rfl

theorem pslldq_1 (v : BitVec 128) : XShiftOp.eval .pslldq v 1 = v <<< 8 := rfl

/-- The two tweaks in `t` times `α⁸`. -/
theorem stepT_ok (t : XReg) (h10 : t ≠ .xmm10) (s : State)
    (hK : ∀ l < 2, qword (s.lane .xmm11 l) 0 = 0x87) :
    WP isa (.block (stepT t)) s fun s' =>
      (∀ l < 2, s'.lane t l = stepW (s.lane t l)) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ t → r ≠ .xmm10 → ∀ l < 2, s'.lane r l = s.lane r l) := by
  let s₁ := (VOp.vshift .psrldq .l256 .xmm10 t 15).exec s
  let s₂ := (VOp.vpclmulqdq .l256 .xmm10 .xmm10 .xmm11 0).exec s₁
  let s₃ := (VOp.vshift .pslldq .l256 t t 1).exec s₂
  let s₄ := (VOp.vbin .vpxor .l256 t t .xmm10).exec s₃
  rw [stepT, WP.block_cons_iff]; refine ⟨s₁, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨s₂, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨s₃, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨s₄, rfl, WP.block_nil ?_⟩
  have h10' : (XReg.xmm10 = t) = False := propext ⟨fun h => h10 h.symm, False.elim⟩
  have n1110 : (XReg.xmm11 = XReg.xmm10) = False := by decide
  have h10'' : (t = XReg.xmm10) = False := propext ⟨h10, False.elim⟩
  refine ⟨fun l hl => ?_, by simp [s₄, s₃, s₂, s₁], by simp [s₄, s₃, s₂, s₁], by simp [s₄, s₃, s₂, s₁],
    by simp [s₄, s₃, s₂, s₁], fun r h1 h2 l hl => ?_⟩
  · simp only [s₄, s₃, s₂, s₁, lane_vbin256, lane_vshift256, lane_vpclmul256, ite_true, h10', h10'', n1110,
      ite_false]
    rw [psrldq_15, pclmul_step _ _ (hK l hl), pslldq_1]
    rfl
  · simp [s₄, s₃, s₂, s₁, h1, h2]

end VG.Proof.AesXts.X86_64.Vaes
