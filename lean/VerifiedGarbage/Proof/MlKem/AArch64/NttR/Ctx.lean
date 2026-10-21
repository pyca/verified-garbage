module

public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Step
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM on AArch64: the NTT halfword by halfword, the regions

The regions of the machine are apart, readable and writable (`Ctx`) when
each lies within a region of the caller's (`P k`), these are apart, and the
code may read them (and write those it writes) (`Ctx.of`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.NttR

open VG VG.AArch64

/-- A 16-byte chunk of a range a region contains. -/
theorem contains_chunk {P : Region} {b : Addr} {c j : Nat} (h : P.Contains b (16 * c)) (hj : j < c)
    (hc : 16 * c < 2 ^ 64) :
    P.Contains (b + BitVec.ofNat 64 (16 * j)) 16 := by
  unfold Region.Contains at *
  have hl : P.len < 2 ^ 64 ∨ 2 ^ 64 ≤ P.len := Nat.lt_or_ge _ _
  have hb := (b - P.base).isLt
  rw [show b + BitVec.ofNat 64 (16 * j) - P.base = (b - P.base) + BitVec.ofNat 64 (16 * j) by
    rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 _),
      ← BitVec.add_assoc], BitVec.toNat_add, BitVec.toNat_ofNat]
  have : 16 * j < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt this]
  have : (b - P.base).toNat + 16 * j < 2 ^ 64 ∨ 2 ^ 64 ≤ (b - P.base).toNat + 16 * j := Nat.lt_or_ge _ _
  rcases this with h1 | h1
  · rw [Nat.mod_eq_of_lt h1]; omega
  · omega

theorem Ctx.of {rs : List Rg} {s₀ : State} (P : Nat → Region) (hlen : rs.length ≤ 16)
    (hsmall : ∀ k < rs.length, (rs.getD k default).off + 16 * chunks rs k < 2 ^ 32)
    (hcont : ∀ k < rs.length, (P k).Contains (rbase rs s₀ k) (16 * chunks rs k))
    (hrd : ∀ k < rs.length, ∀ a, (P k).Contains a 16 → InRegions (s₀.rd ++ s₀.wr) a 16)
    (hwr : ∀ k < rs.length, (rs.getD k default).wr = true → ∀ a, (P k).Contains a 16 → InRegions s₀.wr a 16)
    (hdisj : ∀ k k', k < rs.length → k' < rs.length → k ≠ k' → (P k).Disjoint (P k')) : Ctx rs s₀ := by
  have hc : ∀ k < rs.length, 16 * chunks rs k < 2 ^ 64 := fun k hk => by have := hsmall k hk; omega
  refine ⟨hlen, hsmall, fun k hk j hj => hrd k hk _ (contains_chunk (hcont k hk) hj (hc k hk)),
    fun k hk hw j hj => hwr k hk hw _ (contains_chunk (hcont k hk) hj (hc k hk)),
    fun k j k' j' hk hj hk' hj' hne => ?_⟩
  by_cases hkk : k = k'
  · subst hkk
    have hj' : j ≠ j' := fun e => hne ⟨rfl, e⟩
    have hs := hsmall k hk
    unfold caddr
    exact Offset.sep _ (by omega) (by omega) (by omega)
  · exact (hdisj k k' hk hk' hkk).sep (contains_chunk (hcont k hk) hj (hc k hk))
      (contains_chunk (hcont k' hk') hj' (hc k' hk'))

end VG.Proof.MlKem.AArch64.NttR
