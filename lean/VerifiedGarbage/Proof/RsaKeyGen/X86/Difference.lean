module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Difference
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Spec.RsaKeyGen
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.RsaKeyGen.Difference

/-! # Native absolute difference for the candidate distance check -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Difference
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.Difference

theorem code_ok {s : State} {base : Addr} {size n out tmp a b : Nat}
    (scratch : Scr s base size) (positive : 0 < n)
    (outFit : out + 4 * n ≤ size) (tmpFit : tmp + 4 * n ≤ size)
    (aFit : a + 4 * n ≤ size) (bFit : b + 4 * n ≤ size)
    (outA : out + 4 * n ≤ a ∨ a + 4 * n ≤ out) (outB : out + 4 * n ≤ b ∨ b + 4 * n ≤ out)
    (tmpA : tmp + 4 * n ≤ a ∨ a + 4 * n ≤ tmp) (tmpB : tmp + 4 * n ≤ b ∨ b + 4 * n ≤ tmp)
    (apart : out + 4 * n ≤ tmp ∨ tmp + 4 * n ≤ out) :
    WP isa (code n out tmp a b) s fun t =>
      val32 t.mem base out n = Spec.RsaKeyGen.absDiff (val32 s.mem base a n) (val32 s.mem base b n) ∧
      Outs base [(out, 4 * n), (tmp, 4 * n)] s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .esi] s t := by
  unfold code
  refine WP.seq (WP.mono (chainSubW_ok scratch positive outFit aFit bFit outA outB)
    fun u ⟨Ou, ⟨borrow, mask, forward⟩, Ku⟩ => ?_)
  refine WP.seq (wp_movS rfl fun v V _ => WP.block_nil ?_)
  have Kv : Keeps [.eax, .ecx, .edx, .ebp, .esi] s v := (Ku.mono (by decide)).widen V.keeps
  refine WP.seq (WP.mono (chainSubW_ok (scratch.of_keeps Kv (by decide)) positive tmpFit bFit aFit tmpB tmpA)
    fun z ⟨Oz, ⟨reverse, _, backward⟩, Kz⟩ => ?_)
  refine WP.seq (wp_movS rfl fun y Y _ => WP.block_nil ?_)
  have Ky : Keeps [.eax, .ecx, .edx, .ebp, .esi] s y := ((Kv.widen Kz).widen Y.keeps)
  have selected : y.gpr .ecx = if borrow then BitVec.allOnes 32 else 0 := by
    rw [Y.gpr, Kz.1 .esi (by decide), V.gpr, mask]
  refine WP.mono (selectsW_ok (scratch.of_keeps Ky (by decide)) borrow selected positive outFit tmpFit outFit
    (Or.inl rfl) (Or.inr apart)) fun t ⟨Ot, result, Kt⟩ => ?_
  have aSame : val32 v.mem base a n = val32 s.mem base a n := by
    rw [V.mem]
    exact Ou.val32 (by omega) (by have := scratch.nowrap; omega)
  have bSame : val32 v.mem base b n = val32 s.mem base b n := by
    rw [V.mem]
    exact Ou.val32 (by omega) (by have := scratch.nowrap; omega)
  rw [aSame, bSame] at backward
  have dSame : val32 y.mem base out n = val32 u.mem base out n := by
    rw [Y.mem, Oz.val32 (by omega) (by have := scratch.nowrap; omega), V.mem]
  have eSame : val32 y.mem base tmp n = val32 z.mem base tmp n := by rw [Y.mem]
  have values : val32 t.mem base out n =
      if borrow then val32 z.mem base tmp n else val32 u.mem base out n := by
    cases borrow <;> simp only [Bool.false_eq_true, ↓reduceIte] at result ⊢
    · exact result.trans dSame
    · exact result.trans eSame
  refine ⟨values.trans (VG.Proof.RsaKeyGen.absDiff_select forward backward
    (val32_lt ..) (val32_lt ..)), ?_, Ky.widen Kt⟩
  have O₁ : Outs base [(out, 4 * n), (tmp, 4 * n)] s.mem v.mem := by
    rw [V.mem]
    exact Outs.of_outside Ou (by simp)
  have O₂ : Outs base [(out, 4 * n), (tmp, 4 * n)] v.mem y.mem := by
    rw [Y.mem]
    exact Outs.of_outside Oz (by simp)
  exact (O₁.trans O₂).trans (Outs.of_outside Ot (by simp))

end VG.Proof.RsaKeyGen.X86.Difference
