module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Close
public import VerifiedGarbage.Spec.RsaKeyGen
public import VerifiedGarbage.Proof.RsaKeyGen.X86.NearScalar
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.Difference
import VerifiedGarbage.Proof.RsaKeyGen.X86.Near
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Complete distance check agrees with the optional-prime candidate filter -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Close
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Close

theorem code_ok {s : State} {base : Addr} {size n out tmp a b : Nat}
    (scratch : Scr s base size) (positive : 4 < n)
    (outFit : out + 4 * n ≤ size) (tmpFit : tmp + 4 * n ≤ size)
    (aFit : a + 4 * n ≤ size) (bFit : b + 4 * n ≤ size)
    (outA : out + 4 * n ≤ a ∨ a + 4 * n ≤ out) (outB : out + 4 * n ≤ b ∨ b + 4 * n ≤ out)
    (tmpA : tmp + 4 * n ≤ a ∨ a + 4 * n ≤ tmp) (tmpB : tmp + 4 * n ≤ b ∨ b + 4 * n ≤ tmp)
    (apart : out + 4 * n ≤ tmp ∨ tmp + 4 * n ≤ out) :
    WP isa (code n out tmp a b) s fun t =>
      t.gpr .eax = Near.bit (Spec.RsaKeyGen.tooClose (32 * n)
        (some (val32 s.mem base b n)) (val32 s.mem base a n)) ∧
      Outs base [(out, 4 * n), (tmp, 4 * n)] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  refine WP.seq (WP.mono (Difference.code_ok scratch (by omega) outFit tmpFit aFit bFit outA outB tmpA tmpB apart)
    fun u ⟨D, O, K⟩ => ?_)
  refine WP.mono (Near.code_ok (scratch.of_keeps K (by decide)) positive outFit) fun t ⟨value, M, Kt⟩ => ?_
  rw [D] at value
  refine ⟨value, ?_, (K.mono (by decide)).widen Kt⟩
  rw [M]
  exact O

end VG.Proof.RsaKeyGen.X86.Close
