module
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Spec.Ffdh
public import VerifiedGarbage.Spec.Dsa
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PShape
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.X86.Generation.PShape

/-! # Numeric p shaping matches the shared full-width odd-candidate operation -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem pShape_value {s : State} {src out : BitVec 32} {len : Nat}
    (lengthMin : 2 ≤ len) (lengthMax : len < 2 ^ 32)
    (sourceFit : src.toNat + len ≤ 2 ^ 32) (outputFit : out.toNat + len ≤ 2 ^ 32)
    (apart : Region.Disjoint ⟨src.setWidth 64, len⟩ ⟨out.setWidth 64, len⟩)
    (si : s.gpr .esi = src) (di : s.gpr .edi = out)
    (read : ∀ i < len, InRegions (s.rd ++ s.wr) (off (src.setWidth 64) i) 1)
    (write : ∀ i < len, InRegions s.wr (off (out.setWidth 64) i) 1) :
    WP isa (pShape len) s fun t =>
      Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem (out.setWidth 64) len) =
        Spec.Ffdh.candidateOf (8 * len) (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (src.setWidth 64) len)) ∧
      Frame [⟨out.setWidth 64, len⟩] s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .esi] s t := by
  refine WP.mono (pShape_ok lengthMin lengthMax sourceFit outputFit apart si di read write) fun t ⟨bytes, O, K⟩ => ?_
  refine ⟨?_, O, K⟩
  rw [bytes]
  apply VG.Proof.Ffdh.ParameterCandidate.shapedOctets_value
  · intro empty
    have lenEq := congrArg List.length empty
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range, List.length_nil] at lenEq
    omega
  · decide
  · simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
    omega
end VG.Proof.Dsa.X86.Generation
