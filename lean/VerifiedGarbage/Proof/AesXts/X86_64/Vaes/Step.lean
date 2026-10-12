import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Common
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Ctr32

/-!
# One-pass XTS-AES on x86-64: the tweaks times `α¹⁶`

`stepT_ok`: `stepT k` replaces the two tweaks at `scratch + 256 + 32 k`,
words `v`, with `stepW v`, `v` shifted left by sixteen bits XORed with
`P (v >>> 112)` (`vpsrldq`, `vpclmulqdq` with `0x87`, `vpslldq`, `vpxor`),
whose bytes are those of the tweak sixteen blocks on (`next_b16`).
-/

namespace VG.Proof.AesXts.X86_64.Vaes

open VG VG.X86_64
open VG.Impl.AesXts.X86_64Vaes (bufOff stepT)
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Proof.Aes.X86_64.AesNi (ea_at inRegions_wr)
open VG.Proof.Aes.X86_64.Vaes (load256_lo load256_hi extract_lo extract_hi)
open VG.Proof.AesXts (P)

/-- A tweak sixteen blocks on, as a word. -/
def stepW (v : BitVec 128) : BitVec 128 := (v <<< 16) ^^^ P (v >>> 112)

theorem setWidth_qword_shr112 (v : BitVec 128) : (qword (v >>> 112) 0).setWidth 128 = v >>> 112 := by
  ext i hi
  simp only [qword, BitVec.getElem_setWidth, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight,
    BitVec.getElem_ushiftRight]
  by_cases h : i < 64
  · simp [h]
  · simp only [h, decide_false, Bool.false_and]
    rw [BitVec.getLsbD_of_ge _ _ (by omega)]

theorem pclmul_step (v k : BitVec 128) (hk : qword k 0 = 0x87) :
    pclmul (v >>> 112) k 0 = P (v >>> 112) := by
  simp only [pclmul, show (0 : BitVec 8).getLsbD 0 = false from rfl, show (0 : BitVec 8).getLsbD 4 = false from rfl,
    Bool.false_eq_true, ↓reduceIte, hk, clmul_87, setWidth_qword_shr112]

@[simp] theorem lane_vpclmul256 (d a b : XReg) (n : BitVec 8) (s : State) (r : XReg) (l : Nat) :
    ((VOp.vpclmulqdq .l256 d a b n).exec s).lane r l =
      if r = d then pclmul (s.lane a l) (s.lane b l) n else s.lane r l := by
  simp only [VOp.exec, State.lane, State.setV]
  by_cases h : r = d <;> by_cases hl : l = 0 <;> simp [h, hl]

theorem psrldq_14 (v : BitVec 128) : XShiftOp.eval .psrldq v 14 = v >>> 112 := rfl

theorem pslldq_2 (v : BitVec 128) : XShiftOp.eval .pslldq v 2 = v <<< 16 := rfl

/-- The two tweaks at `scratch + 256 + 32 k` times `α¹⁶`. -/
theorem stepT_ok (k : Nat) (s : State) (hK : ∀ l < 2, qword (s.lane .xmm11 l) 0 = 0x87)
    (hin : InRegions s.wr (s.gpr .r8 + BitVec.ofInt 64 ((bufOff + 32 * k : Nat) : Int)) 32) :
    WP isa (.block (stepT k)) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .r8 + BitVec.ofInt 64 ((bufOff + 32 * k : Nat) : Int))
        (stepW (s.mem.readW (s.gpr .r8 + BitVec.ofInt 64 ((bufOff + 32 * k : Nat) : Int) + BitVec.ofNat 64 16) 128) ++
          stepW (s.mem.readW (s.gpr .r8 + BitVec.ofInt 64 ((bufOff + 32 * k : Nat) : Int)) 128)) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .xmm9 → r ≠ .xmm10 → ∀ l < 2, s'.lane r l = s.lane r l) := by
  have hin' := inRegions_wr hin
  let a := s.gpr .r8 + BitVec.ofInt 64 ((bufOff + 32 * k : Nat) : Int)
  let v := s.mem.readW a 256
  let s₁ := s.setV .l256 .xmm9 (v.extractLsb' 0 128) (v.extractLsb' 128 128)
  let s₂ := (VOp.vshift .psrldq .l256 .xmm10 .xmm9 14).exec s₁
  let s₃ := (VOp.vpclmulqdq .l256 .xmm10 .xmm10 .xmm11 0).exec s₂
  let s₄ := (VOp.vshift .pslldq .l256 .xmm9 .xmm9 2).exec s₃
  let s₅ := (VOp.vbin .vpxor .l256 .xmm9 .xmm9 .xmm10).exec s₄
  rw [stepT, WP.block_cons_iff]
  refine ⟨s₁, by simp only [isa, exec, State.load256, ea_at, hin', ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨s₂, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨s₃, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨s₄, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨s₅, rfl, ?_⟩
  rw [WP.block_cons_iff]
  have hst : isa.exec (.vmovdquStore .l256 (at_ .r8 (bufOff + 32 * k)) .xmm9) s₅ =
      some (s₅.setMem (s.mem.writeW a (s₅.ymm .xmm9))) := by
    simp only [isa, exec, State.store256_eq, ea_at, s₅, s₄, s₃, s₂, s₁, VOp.exec_gpr, State.setV_gpr,
      VOp.exec_wr, State.setV_wr, VOp.exec_mem, State.setV_mem, hin, ite_true, a]
  refine ⟨_, hst, WP.block_nil ?_⟩
  refine ⟨?_, by simp [s₅, s₄, s₃, s₂, s₁], by simp [s₅, s₄, s₃, s₂, s₁], by simp [s₅, s₄, s₃, s₂, s₁],
    fun r h1 h2 l hl => ?_⟩
  · simp only [State.setMem_mem, State.ymm_eq]
    refine congrArg _ ?_
    have n910 : (XReg.xmm9 = XReg.xmm10) = False := by decide
    have n109 : (XReg.xmm10 = XReg.xmm9) = False := by decide
    have n119 : (XReg.xmm11 = XReg.xmm9) = False := by decide
    have n1110 : (XReg.xmm11 = XReg.xmm10) = False := by decide
    have e0 : s₅.lane .xmm9 0 = stepW (s.mem.readW a 128) := by
      simp only [s₅, s₄, s₃, s₂, s₁, lane_vbin256, lane_vshift256, lane_vpclmul256, State.lane_setV256,
        ite_true, ite_false, n910, n109, n119, n1110]
      rw [psrldq_14, pclmul_step _ _ (hK 0 (by decide))]
      simp only [v, load256_lo, pslldq_2, VBinOp.sse, stepW]
      rfl
    have e1 : s₅.lane .xmm9 1 = stepW (s.mem.readW (a + BitVec.ofNat 64 16) 128) := by
      simp only [s₅, s₄, s₃, s₂, s₁, lane_vbin256, lane_vshift256, lane_vpclmul256, State.lane_setV256,
        ite_true, ite_false, n910, n109, n119, n1110, Nat.one_ne_zero]
      rw [psrldq_14, pclmul_step _ _ (hK 1 (by decide))]
      simp only [v, load256_hi, pslldq_2, VBinOp.sse, stepW]
      rfl
    rw [e0, e1]
  · simp [s₅, s₄, s₃, s₂, s₁, State.lane_setV256, h1, h2]

end VG.Proof.AesXts.X86_64.Vaes
