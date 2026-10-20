module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.CandidateArithmetic
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.DivContext
import VerifiedGarbage.Proof.Rsa.X86.DivLoop

/-! # Reuse verified native division for the even 2q divisor -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

def candidateGeometry (base : Addr) (size n : Nat) : VG.Proof.Rsa.X86.Div.Geometry :=
  ⟨base, size, fun i => 512 * i.val, n⟩

theorem candidateGeometry_context {s : State} {base : Addr} {size n : Nat} (S : Scr s base size)
    (positive : 0 < n) (width : n ≤ 96) (room : 2048 ≤ size) :
    VG.Proof.Rsa.X86.Div.Context (candidateGeometry base size n) s := by
  refine ⟨S, positive, by change n < 2 ^ 24; omega, ?_, ?_⟩
  · intro i
    have hi := i.isLt
    simp only [candidateGeometry, VG.Proof.Rsa.X86.Div.Geometry.words]
    split <;> omega
  · intro i j ne
    have hi := i.isLt
    have hj := j.isLt
    have neq : i.val ≠ j.val := fun h => ne (Fin.ext h)
    simp only [candidateGeometry, VG.Proof.Rsa.X86.Div.Geometry.words]
    split <;> split <;> omega

theorem candidateDivision_ok {s : State} {base : Addr} {size n x q : Nat} (S : Scr s base size)
    (positive : 0 < n) (width : n ≤ 96) (room : 2048 ≤ size)
    (qpos : 0 < q) (qbound : 2 * q < 2 ^ (32 * n))
    (original : val32 s.mem base candidateQuotient n = x)
    (divisor : val32 s.mem base candidateDivisor (n + 1) = 2 * q) :
    WP isa (VG.Impl.Rsa.X86.Div.code n candidateQuotient candidateRemainder candidateDivisor candidateTemporary) s fun t =>
      val32 t.mem base candidateRemainder (n + 1) = x % (2 * q) ∧
      val32 t.mem base candidateQuotient n = x / (2 * q) ∧
      Outs base [(candidateQuotient, 4 * n), (candidateRemainder, 4 * (n + 1)), (candidateTemporary, 4 * (n + 1))]
        s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  refine WP.mono (VG.Proof.Rsa.X86.Div.code_ok (candidateGeometry_context S positive width room))
    fun t ⟨_, O, K, result⟩ => ?_
  have d : (candidateGeometry base size n).value s.mem 2 = 2 * q := divisor
  have v : (candidateGeometry base size n).value s.mem 0 = x := original
  rw [d, v] at result
  exact ⟨(result (by omega) qbound).1, (result (by omega) qbound).2, O, K⟩
end VG.Proof.Dsa.X86.Generation
