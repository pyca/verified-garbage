module

public import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Step
public import VerifiedGarbage.Impl.AesXts.X86_64AesNi
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr32
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-!
# One-pass XTS-AES with AES-NI on x86-64: a tweak in the buffer times `α⁸`

`stepT_ok`: `X86_64AesNi.stepT k` replaces the tweak at `rax + 16 k`, a word
`v`, with `stepW v` (`Vaes/Step.lean`), through `xmm9` and `xmm10`.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.OnePassNi

open VG VG.X86_64
open VG.Impl.AesXts.X86_64AesNi (stepT)
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Proof.Aes.X86_64.AesNi (ea_at inRegions_wr)
open VG.Proof.AesXts.X86_64.Vaes (stepW psrldq_15 pslldq_1 pclmul_step)

theorem lane0_vshift128 (op : XShiftOp) (d a : XReg) (n : BitVec 8) (s : State) (r : XReg) :
    ((VOp.vshift op .l128 d a n).exec s).xmm r = if r = d then op.eval (s.xmm a) n else s.xmm r := by
  simp only [VOp.exec, State.setV]; split <;> simp_all [State.lane]

theorem lane0_vpclmul128 (d a b : XReg) (n : BitVec 8) (s : State) (r : XReg) :
    ((VOp.vpclmulqdq .l128 d a b n).exec s).xmm r = if r = d then pclmul (s.xmm a) (s.xmm b) n else s.xmm r := by
  simp only [VOp.exec, State.setV]; split <;> simp_all [State.lane]

theorem lane0_vbin128 (op : VBinOp) (d a b : XReg) (s : State) (r : XReg) :
    ((VOp.vbin op .l128 d a b).exec s).xmm r = if r = d then op.sse.eval (s.xmm a) (s.xmm b) else s.xmm r := by
  simp only [VOp.exec, State.setV]; split <;> simp_all [State.lane]

theorem xmm_setV128 (s : State) (d r : XReg) (lo hi : BitVec 128) :
    (s.setV .l128 d lo hi).xmm r = if r = d then lo else s.xmm r := by
  simp only [State.setV]

/-- The tweak at `rax + 16 k` times `α⁸`. -/
theorem stepT_ok (k : Nat) (s : State) (hK : qword (s.xmm .xmm11) 0 = 0x87)
    (hin : InRegions s.wr (s.gpr .rax + BitVec.ofInt 64 ((16 * k : Nat) : Int)) 16) :
    WP isa (.block (stepT k)) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .rax + BitVec.ofInt 64 ((16 * k : Nat) : Int))
        (stepW (s.mem.readW (s.gpr .rax + BitVec.ofInt 64 ((16 * k : Nat) : Int)) 128)) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .xmm9 → r ≠ .xmm10 → s'.xmm r = s.xmm r) := by
  have hin' := inRegions_wr hin
  let a := s.gpr .rax + BitVec.ofInt 64 ((16 * k : Nat) : Int)
  let v := s.mem.readW a 128
  let s₁ := s.setV .l128 .xmm9 v 0
  let s₂ := (VOp.vshift .psrldq .l128 .xmm10 .xmm9 15).exec s₁
  let s₃ := (VOp.vpclmulqdq .l128 .xmm10 .xmm10 .xmm11 0).exec s₂
  let s₄ := (VOp.vshift .pslldq .l128 .xmm9 .xmm9 1).exec s₃
  let s₅ := (VOp.vbin .vpxor .l128 .xmm9 .xmm9 .xmm10).exec s₄
  rw [stepT, WP.block_cons_iff]
  refine ⟨s₁, by simp only [isa, exec, State.load128, ea_at, hin', ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨s₂, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨s₃, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨s₄, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨s₅, rfl, ?_⟩
  rw [WP.block_cons_iff]
  have hst : isa.exec (.vmovdquStore .l128 (at_ .rax (16 * k)) .xmm9) s₅ =
      some (s₅.setMem (s.mem.writeW a (s₅.xmm .xmm9))) := by
    simp only [isa, exec, State.store128_eq, ea_at, s₅, s₄, s₃, s₂, s₁, VOp.exec_gpr, State.setV_gpr,
      VOp.exec_wr, State.setV_wr, VOp.exec_mem, State.setV_mem, hin, ite_true, a]
  refine ⟨_, hst, WP.block_nil ⟨?_, by simp [s₅, s₄, s₃, s₂, s₁], by simp [s₅, s₄, s₃, s₂, s₁],
    by simp [s₅, s₄, s₃, s₂, s₁], fun r h1 h2 => ?_⟩⟩
  · simp only [State.setMem_mem]
    refine congrArg _ ?_
    have n910 : (XReg.xmm9 = XReg.xmm10) = False := by decide
    have n109 : (XReg.xmm10 = XReg.xmm9) = False := by decide
    have n119 : (XReg.xmm11 = XReg.xmm9) = False := by decide
    have n1110 : (XReg.xmm11 = XReg.xmm10) = False := by decide
    simp only [s₅, s₄, s₃, s₂, s₁, lane0_vbin128, lane0_vshift128, lane0_vpclmul128, xmm_setV128,
      ite_true, ite_false, n910, n109, n119, n1110]
    rw [psrldq_15, pclmul_step _ _ hK, pslldq_1]
    rfl
  · simp [s₅, s₄, s₃, s₂, s₁, lane0_vbin128, lane0_vshift128, lane0_vpclmul128, xmm_setV128, h1, h2]

end VG.Proof.AesXts.X86_64.OnePassNi
