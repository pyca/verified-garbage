module
public import VerifiedGarbage.Proof.Bignum.Words

import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Mem
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit

/-! Join adjacent selected blocks without losing previously copied bytes. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.Proof.Bignum

theorem copy_append {m₀ m₁ m₂ : Mem} {B : Addr} {dst src n k : Nat}
    (hn : dst + n + k ≤ 2 ^ 64)
    (h₁ : Outside B dst n m₀ m₁) (h₂ : Outside B (dst + n) k m₁ m₂)
    (b₁ : ∀ j < n, m₁ (off B (dst + j)) = m₀ (off B (src + j)))
    (b₂ : ∀ j < k, m₂ (off B (dst + n + j)) = m₀ (off B (src + n + j))) :
    Outside B dst (n + k) m₀ m₂ ∧
      ∀ j < n + k, m₂ (off B (dst + j)) = m₀ (off B (src + j)) := by
  refine ⟨(h₁.mono (by omega) (by omega)).trans (h₂.mono (by omega) (by omega)), ?_⟩
  intro j hj
  by_cases h : j < n
  · rw [h₂ _ (by
      simp only [ofs, off, Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show dst + j < 2 ^ 64 by omega)]
      omega)]
    exact b₁ j h
  · have he₁ : dst + j = dst + n + (j - n) := by omega
    have he₂ : src + j = src + n + (j - n) := by omega
    rw [he₁,he₂]
    exact b₂ (j - n) (by omega)

theorem wv_copy {m m' : Mem} {P : Addr} {dst src w : Nat}
    (h : ∀ j < 8 * w, m' (off P (dst + j)) = m (off P (src + j))) :
    wv m' P dst w = wv m P src w := by
  apply wv_congr2
  intro i hi
  change m'.read (off P (dst + 8 * i)) 8 = m.read (off P (src + 8 * i)) 8
  apply Mem.read_eq_of_bytes
  intro j hj
  rw [Mem.extractLsb'_read m _ hj]
  simpa only [off, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc] using h (8 * i + j) (by omega)

end VG.Proof.Bignum.AArch64.WindowVector
