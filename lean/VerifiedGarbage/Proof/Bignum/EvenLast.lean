module

public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.Omega

/-!
# An odd exponent less one, byte by byte

`vg_rsa_public_precomputed_checked` exponentiates by `e - 1` for an odd
`e`, reading the bytes of `e` with bit 0 of the last one cleared
(`evenLast`), then multiplies by the input once more.
-/

@[expose] public section

namespace VG.Proof.Bignum

/-- `bs` with bit 0 of its last byte cleared. -/
def evenLast (bs : List Byte) : List Byte :=
  bs.mapIdx fun i b => if i + 1 = bs.length then b &&& 0xFE else b

theorem evenLast_length (bs : List Byte) : (evenLast bs).length = bs.length :=
  List.length_mapIdx

theorem evenLast_getElem (bs : List Byte) {i : Nat} (h : i < bs.length) :
    (evenLast bs)[i]'(by rw [evenLast_length]; exact h) =
      if i + 1 = bs.length then bs[i] &&& 0xFE else bs[i] :=
  List.getElem_mapIdx ..

/-- Clearing bit 0 of a byte subtracts its parity. -/
theorem clear0_toNat : ∀ b : Byte, (b &&& 0xFE).toNat + b.toNat % 2 = b.toNat := by decide

/-- The prefixes but the whole are unchanged. -/
theorem pre_evenLast (bs : List Byte) {i : Nat} (hi : i < bs.length) : pre (evenLast bs) i = pre bs i := by
  unfold pre
  congr 1
  apply List.ext_getElem (by simp only [List.length_take, evenLast_length])
  intro j h₁ h₂
  simp only [List.length_take] at h₁
  rw [List.getElem_take, List.getElem_take, evenLast_getElem bs (by omega)]
  simp only [show j + 1 ≠ bs.length by omega, ↓reduceIte]

/-- `evenLast bs` is `bs` less one, for `bs` of an odd number. -/
theorem os2ip_evenLast {bs : List Byte} (hodd : Spec.Rsa.os2ip bs % 2 = 1) :
    Spec.Rsa.os2ip (evenLast bs) + 1 = Spec.Rsa.os2ip bs := by
  have hL : 0 < bs.length := by
    rcases bs with _ | ⟨b, bs⟩
    · exact absurd hodd (by decide)
    · exact Nat.succ_pos _
  have hl : bs.length - 1 < bs.length := by omega
  have e₁ := pre_succ bs hl
  have e₂ : Spec.Rsa.os2ip (evenLast bs) = 256 * pre bs (bs.length - 1) + (bs[bs.length - 1] &&& 0xFE).toNat := by
    have h₁ : Spec.Rsa.os2ip (evenLast bs) = pre (evenLast bs) (bs.length - 1 + 1) := by
      rw [Nat.sub_add_cancel hL, ← evenLast_length, pre_len]
    rw [h₁, pre_succ (evenLast bs) (by rw [evenLast_length]; exact hl), pre_evenLast bs hl, evenLast_getElem bs hl]
    simp only [show bs.length - 1 + 1 = bs.length by omega, ↓reduceIte]
  rw [Nat.sub_add_cancel hL, pre_len] at e₁
  have hc := clear0_toNat bs[bs.length - 1]
  rw [e₁] at hodd
  omega

end VG.Proof.Bignum
