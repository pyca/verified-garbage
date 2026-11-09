module

public import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Step
public import VerifiedGarbage.Impl.AesXts.X86_64AesNi
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr32
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-!
# One-pass XTS-AES with AES-NI on x86-64: a tweak in the buffer times `α⁸`

`stepT_ok`: `X86_64AesNi.stepT k` replaces the tweak at `rax + 16 k`, a word
`v`, with `stepW v` (`Vaes/Step.lean`), through `xmm9` and `xmm10`, in legacy SSE.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.OnePassNi

open VG VG.X86_64
open VG.Impl.AesXts.X86_64AesNi (stepT)
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Proof.Aes.X86_64.AesNi (ea_at inRegions_wr)
open VG.Proof.AesXts.X86_64.Vaes (stepW psrldq_15 pslldq_1 pclmul_step)

/-- The tweak at `rax + 16 k` times `α⁸`. -/
theorem stepT_ok (k : Nat) (s : State) (hK : qword (s.xmm .xmm11) 0 = 0x87)
    (hin : InRegions s.wr (s.gpr .rax + BitVec.ofInt 64 ((16 * k : Nat) : Int)) 16) :
    WP isa (.block (stepT k)) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .rax + BitVec.ofInt 64 ((16 * k : Nat) : Int))
        (stepW (s.mem.readW (s.gpr .rax + BitVec.ofInt 64 ((16 * k : Nat) : Int)) 128)) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .xmm9 → r ≠ .xmm10 → s'.xmm r = s.xmm r) := by
  have hin' := inRegions_wr hin
  have n910 : (XReg.xmm9 = XReg.xmm10) = False := by decide
  have n109 : (XReg.xmm10 = XReg.xmm9) = False := by decide
  have n119 : (XReg.xmm11 = XReg.xmm9) = False := by decide
  have n1110 : (XReg.xmm11 = XReg.xmm10) = False := by decide
  apply WP.of_runBlock
  simp only [stepT, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, isa, State.setXmm,
    State.load128, State.store128_eq, ea_at, hin, hin', Option.map_some, Option.some.injEq, exists_eq_left',
    n910, n109, n119, n1110]
  refine ⟨?_, rfl, rfl, rfl, fun r h1 h2 => by simp [State.setMem, h1, h2]⟩
  simp only [State.setMem, XBinOp.eval]
  refine congrArg _ ?_
  rw [psrldq_15, pclmul_step _ _ hK, pslldq_1]
  rfl

end VG.Proof.AesXts.X86_64.OnePassNi
