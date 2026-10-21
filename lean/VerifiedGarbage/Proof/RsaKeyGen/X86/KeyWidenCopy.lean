module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyWorkspace
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Rsa.X86.DivCopy
import VerifiedGarbage.Proof.Rsa.KeyWorkspace
import VerifiedGarbage.Proof.RsaKeyGen.WordBounds32

/-! # Widen a small inverse result into a persistent native RSA array -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

theorem widenCopy_ok {s : State} {B : Addr} {Z n N k out src : Nat}
    (h : Ws s B Z n N) (positive : 0 < k) (width : k ≤ n) (ho : out < N)
    (sourceBound : src + 4 * k ≤ Z)
    (separate : src + 4 * k ≤ arr n out ∨ arr n out + S n ≤ src) :
    WP isa (widenCopy n k out src) s fun t =>
      Ws t B Z n N ∧ Outside B (arr n out) (S n) s.mem t.mem ∧
      val32 t.mem B (arr n out) (n + 2) = val32 s.mem B src k ∧
      num t.mem B n out = val32 s.mem B src k ∧ Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have fit := h.arr_fit ho
  have hn := h.workspace.nowrap
  unfold widenCopy
  refine WP.seq (WP.mono (zerosW_ok h.workspace (by omega)
    (by change arr n out + 4 * (n + 2) ≤ Z; exact fit)) fun u ⟨Ou, zero, Ku⟩ => ?_)
  change Outside B (arr n out) (4 * (n + 2)) s.mem u.mem at Ou
  change val32 u.mem B (arr n out) (n + 2) = 0 at zero
  have hu := h.rest Ku
  have source : val32 u.mem B src k = val32 s.mem B src k := Ou.val32 separate (by omega)
  have high : val32 u.mem B (arr n out + 4 * k) (n + 2 - k) = 0 :=
    VG.Proof.Rsa.KeyWorkspace.val32_zero_part zero (by omega : k + (n + 2 - k) ≤ n + 2)
  refine WP.mono (VG.Proof.Rsa.X86.Div.copyWords_ok hu.workspace positive sourceBound
    (by change arr n out + 4 * k ≤ Z; unfold S at fit; omega)
    (Or.inr (by change arr n out + 4 * k ≤ src ∨ src + 4 * k ≤ arr n out; unfold S at separate; omega))) fun t ⟨Ot, copied, Kt⟩ => ?_
  change Outside B (arr n out) (4 * k) u.mem t.mem at Ot
  change val32 t.mem B (arr n out) k = val32 u.mem B src k at copied
  have highT : val32 t.mem B (arr n out + 4 * k) (n + 2 - k) = 0 := by
    rw [Ot.val32 (Or.inr (Nat.le_refl _)) (by unfold S at fit; omega), high]
  have full : val32 t.mem B (arr n out) (n + 2) = val32 s.mem B src k := by
    have append := val32_append t.mem B (arr n out) k (n + 2 - k)
    rw [show k + (n + 2 - k) = n + 2 by omega, highT, Nat.mul_zero, Nat.add_zero, copied, source] at append
    exact append
  have bound : val32 t.mem B (arr n out) (n + 2) < 2 ^ (32 * n) := by
    rw [full]
    exact Nat.lt_of_lt_of_le (val32_lt s.mem B src k) (Nat.pow_le_pow_right (by decide) (by omega))
  exact ⟨hu.rest Kt, Ou.trans (Ot.mono (Nat.le_refl _) (by omega)), full,
    (VG.Proof.RsaKeyGen.WordBounds32.low_eq (by omega : n ≤ n + 2) bound).trans full,
    (Ku.mono (by decide)).trans Kt⟩

end VG.Proof.RsaKeyGen.X86.Key
