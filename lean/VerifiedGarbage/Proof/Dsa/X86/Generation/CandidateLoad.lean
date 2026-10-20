module
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.Impl.Dsa.X86.Generation.CandidateLoad
import VerifiedGarbage.Proof.Dsa.X86.Generation.CandidateDouble
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.X86.Bytes
import VerifiedGarbage.Proof.Framework.Mem

/-! # Decode q and double it exactly, retaining the high carry word -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem loadDivisor_ok {s : State} {base : Addr} {size len n : Nat}
    (S : Scr s base size) (width : n ≤ 48) (room : 2048 ≤ size)
    (fit : (s.gpr .esi).toNat + len ≤ 2 ^ 32) (h4 : 4 ≤ len) (hlen : len ≤ 8 * n) (hw4 : len % 4 = 0)
    (read : ∀ d, d + 4 ≤ len → InRegions (s.rd ++ s.wr) ((s.gpr .esi).setWidth 64 + BitVec.ofNat 64 d) 4)
    (apart : Region.Disjoint ⟨(s.gpr .esi).setWidth 64, len⟩ ⟨off base candidateDivisor, 8 * n⟩) :
    WP isa (loadDivisor len n) s fun t =>
      val32 t.mem base candidateDivisor (2 * n + 1) =
        2 * Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((s.gpr .esi).setWidth 64) len) ∧
      Outs base [(candidateDivisor, 4 * (2 * n + 1)), (candidateTemporary, 4 * (2 * n + 1))] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  unfold loadDivisor
  refine WP.seq (WP.mono (loadComponent_ok S (by unfold candidateDivisor; omega) fit h4 hlen hw4 read apart)
    fun a ⟨value, Ka, Oa⟩ => ?_)
  refine WP.seq (WP.mono (zeroPad_ok (S.of_keeps Ka (by decide))
    (o := candidateDivisor + 8 * n) (k := 1) (by unfold candidateDivisor; omega)) fun b ⟨zero, Kb, Ob⟩ => ?_)
  have extended : val32 b.mem base candidateDivisor (2 * n + 1) =
      Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((s.gpr .esi).setWidth 64) len) := by
    rw [val32_succ, show 4 * (2 * n) = 8 * n by omega]
    have z := zero 0 (by decide)
    simp only [Nat.mul_zero, Nat.add_zero] at z
    rw [z, Nat.mul_zero, Nat.add_zero, Ob.val32 (.inl (by omega))
      (by have := S.nowrap; unfold candidateDivisor at *; omega), ← wordsVal_eq_val32, value]
  have K : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s b :=
    (Ka.mono (by decide)).trans (Kb.mono (by decide))
  have lower : val32 b.mem base candidateDivisor (2 * n + 1) < 2 ^ (64 * n) := by
    rw [extended, ← value]
    exact wordsVal_lt _ _ _ _
  have fits : 2 * val32 b.mem base candidateDivisor (2 * n + 1) < 2 ^ (32 * (2 * n + 1)) := by
    have h := Nat.mul_lt_mul_of_pos_left lower (by decide : 0 < 2)
    have e : 2 * 2 ^ (64 * n) = 2 ^ (64 * n + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [e] at h
    exact Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by omega))
  refine WP.mono (doubleWords_ok (S.of_keeps K (by decide)) (by omega)
    (by unfold candidateDivisor; omega) (by unfold candidateTemporary; omega)
    (.inl (by unfold candidateDivisor candidateTemporary; omega)) fits) fun t ⟨result, Ot, Kt⟩ => ?_
  refine ⟨by rw [result, extended], ?_, K.trans (Kt.mono (by decide))⟩
  exact ((Outs.of_outside (Oa.mono (o' := candidateDivisor) (n' := 4 * (2 * n + 1)) (Nat.le_refl _) (by omega)) (by simp)).trans
    (Outs.of_outside (Ob.mono (o' := candidateDivisor) (n' := 4 * (2 * n + 1)) (by omega) (by omega)) (by simp))).trans Ot
end VG.Proof.Dsa.X86.Generation
