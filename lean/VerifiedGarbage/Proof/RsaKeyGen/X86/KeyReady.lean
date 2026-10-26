module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutcome
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.Prop
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Basic
import Mathlib.Tactic.ToAdditive

/-! # Sorted factors and the specified inverse, ready for the retry branch -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

structure KeyReady (B : Addr) (n e p q : Nat) (m : Mem) : Prop where
  pValue : num m B n aPa = max p q
  qValue : num m B n aQa = min p q
  pm : num m B n aPm = max p q - 1
  qm : num m B n aQm = min p q - 1
  lcm : num m B n aL = Nat.lcm (max p q - 1) (min p q - 1)
  exponent : val32 m B kEv 2 = e
  loaded : num m B n aE = e
  one : num m B n aOne = 1
  inverse : Spec.Rsa.inverse e (Nat.lcm (max p q - 1) (min p q - 1)) =
    (if slot m B kOk = 0 then none else some (num m B n aD))
  bit : slot m B kOk ≤ 1

theorem KeyReady.small {s : State} {B : Addr} {Z n e p q : Nat} {m' : Mem}
    (h : Ws s B Z n 32) (R : KeyReady B n e p q s.mem)
    (O : Keep B n [aT1, aT2] [] s.mem m') : KeyReady B n e p q m' := by
  have same (j : Nat) (bound : j < 32) (persistent : 15 ≤ j) : num m' B n j = num s.mem B n j := by
    exact O.num (by
      intro a ha
      have H : ∀ a ∈ [aT1, aT2], a < 15 := by decide
      have Ha := H a ha
      omega) (by simp) (h.fit64 bound)
  have E : val32 m' B kEv 2 = val32 s.mem B kEv 2 := by
    apply O.val32 _ (by decide)
    intro r hr
    change r ∈ [(arr n aT1, S n), (arr n aT2, S n)] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    all_goals exact Or.inl (Nat.le_trans (by decide : kEv + 8 ≤ hdr) (Nat.le_add_right ..))
  have mask : slot m' B kOk = slot s.mem B kOk := O.slot (by decide) (by simp)
  refine ⟨(same _ (by decide) (by decide)).trans R.pValue,
    (same _ (by decide) (by decide)).trans R.qValue,
    (same _ (by decide) (by decide)).trans R.pm,
    (same _ (by decide) (by decide)).trans R.qm,
    (same _ (by decide) (by decide)).trans R.lcm, E.trans R.exponent,
    (same _ (by decide) (by decide)).trans R.loaded,
    (same _ (by decide) (by decide)).trans R.one, ?_, ?_⟩
  · rw [mask, same _ (by decide) (by decide)]
    exact R.inverse
  · rw [mask]
    exact R.bit

theorem KeyReady.retry {B : Addr} {n e p q : Nat} {m m' : Mem} (R : KeyReady B n e p q m)
    (unit : slot m B kOk = 1) (small : num m B n aD ≤ 2 ^ (16 * n))
    (mask : slot m' B kOk = 0) (status : slot m' B kStatus = 2) : CoreOutcome B n e p q m' := by
  have inverse := R.inverse
  rw [unit, ite_eq_right (by decide : ¬(1 : Nat) = 0)] at inverse
  unfold CoreOutcome
  rw [keyFromPrimes_retry inverse small]
  exact ⟨status, mask⟩

end VG.Proof.RsaKeyGen.X86.Key
