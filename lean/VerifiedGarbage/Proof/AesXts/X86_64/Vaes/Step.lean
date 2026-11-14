module
public import VerifiedGarbage.Impl.AesXts.X86_64Vaes
public import VerifiedGarbage.Proof.AesXts.Alpha16
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.X86_64.Sse
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-! ### `AesXts.X86_64.Clmul87`, which only this module used -/

section

/-!
# XTS on x86-64: `clmul` by `0x87`

`clmul_87`: the carry-less product (`VG.X86_64.clmul`, PCLMULQDQ's) of a
quadword by `0x87` is `P` of it (`Proof/AesXts/Alpha16.lean`), which turns
`vpclmulqdq` of the top sixteen bits of a tweak into the reduction of sixteen
multiplications by `α`.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64

open VG VG.X86_64
open VG.Proof.AesXts (P P_xor P_shl P_zero)

theorem setWidth_succ (a : BitVec 64) {k : Nat} (hk : k < 64) :
    (a.setWidth (k + 1)).setWidth 128 =
      (a.setWidth k).setWidth 128 ^^^ (if a.getLsbD k then (1 : BitVec 128) <<< k else 0) := by
  ext i hi
  rcases Nat.lt_trichotomy i k with h | rfl | h
  · cases hb : a.getLsbD k <;> simp [BitVec.getElem_setWidth, BitVec.getElem_shiftLeft, h, show i < k + 1 by omega_using [h]]
  · cases hb : a.getLsbD i <;> simp [BitVec.getElem_setWidth, BitVec.getElem_shiftLeft, hb]
  · cases hb : a.getLsbD k <;> simp [BitVec.getElem_setWidth, BitVec.getElem_shiftLeft, show ¬ i < k + 1 by omega_using [h],
      show ¬ i < k by omega_using [h], show ¬ i - k = 0 by omega_using [h]]

/-- `clmul` of `a` by `0x87` is `P` of it. -/
theorem clmul_87 (a : BitVec 64) : clmul a 0x87 = P (a.setWidth 128) := by
  have h : ∀ k ≤ 64, (List.range k).foldl
      (fun acc j => if a.getLsbD j then acc ^^^ ((0x87 : BitVec 64).setWidth 128 <<< j) else acc) 0 =
      P ((a.setWidth k).setWidth 128) := by
    intro k hk
    induction k with
    | zero =>
      simp only [List.range_zero, List.foldl_nil]
      rw [show (a.setWidth 0).setWidth 128 = 0#128 by ext i; simp]
      rfl
    | succ k ih =>
      rw [List.range_succ, List.foldl_append, ih (by omega_using [hk]), setWidth_succ a (by omega_using [hk]), P_xor]
      cases hb : a.getLsbD k
      · simp only [List.foldl_cons, List.foldl_nil, hb, Bool.false_eq_true, ↓reduceIte]
        rw [show P 0 = 0 from rfl]; simp
      · simp only [List.foldl_cons, List.foldl_nil, hb, ↓reduceIte, P_shl]
        rw [show BitVec.setWidth 128 (0x87 : BitVec 64) = P 1 from rfl]
  rw [clmul, h 64 (Nat.le_refl _), BitVec.setWidth_eq]

end VG.Proof.AesXts.X86_64

end

end


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
    rw [BitVec.getLsbD_of_ge _ _ (by omega_using [h])]

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
