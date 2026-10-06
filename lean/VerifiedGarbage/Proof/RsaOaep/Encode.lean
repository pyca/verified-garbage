import VerifiedGarbage.Proof.RsaOaep.Decode

/-!
# RSAES-OAEP: the encoding, on any target

`EM` before masking in a working space (`EmAt`), `DB` read from it
(`EmAt.db`), `EM` masked (`emOf`), and `encrypt` as the public-key operation
of it (`encrypt_some`) or the failure for a long message (`encrypt_none`).
-/

namespace VG.Proof.RsaOaep

open VG
open VG.Proof.Mgf1 (ifp ifn)

/-- `EM` before masking: `0x00 ‖ seed ‖ lHash ‖ 0…0 ‖ 0x01 ‖ M`, in our working space. -/
structure EmAt (V : Nat → Byte) (k D : Nat) (sd lh m : List Byte) (mLen : Nat) : Prop where
  z0 : V 0 = 0
  sd : ∀ i < D, V (1 + i) = sd.getD i 0
  lh : ∀ i < D, V (1 + D + i) = lh.getD i 0
  ps : ∀ i, 1 + 2 * D ≤ i → i < k - mLen - 1 → V i = 0
  one : V (k - mLen - 1) = 1
  msg : ∀ i < mLen, V (k - mLen + i) = m.getD i 0

/-- `DB`, from `EM` before masking. -/
theorem EmAt.db {V : Nat → Byte} {k D : Nat} {sd lh m : List Byte} {mLen : Nat} (h : EmAt V k D sd lh m mLen)
    (hlh : lh.length = D) (hm : m.length = mLen) (hk : 2 * D + 2 + mLen ≤ k) :
    ∀ i < k - D - 1, V (1 + D + i) = (lh ++ Spec.RsaOaep.zeros (k - mLen - 2 * D - 2) ++ 0x01 :: m).getD i 0 := by
  intro i hi
  have hz : (Spec.RsaOaep.zeros (k - mLen - 2 * D - 2)).length = k - mLen - 2 * D - 2 := by
    simp [Spec.RsaOaep.zeros]
  rw [Proof.Mgf1.getD_append, List.length_append, hlh, hz]
  by_cases h1 : i < D + (k - mLen - 2 * D - 2)
  · rw [ifp h1, Proof.Mgf1.getD_append, hlh]
    by_cases h2 : i < D
    · rw [ifp h2]; exact h.lh i h2
    · rw [ifn h2, h.ps _ (by omega) (by omega)]
      simp only [Spec.RsaOaep.zeros, List.getD_eq_getElem?_getD, List.getElem?_replicate]
      rw [ifp (by omega)]; rfl
  · rw [ifn h1]
    by_cases h3 : i = D + (k - mLen - 2 * D - 2)
    · subst h3; rw [Nat.sub_self, show 1 + D + (D + (k - mLen - 2 * D - 2)) = k - mLen - 1 by omega, h.one]; rfl
    · obtain ⟨j, rfl⟩ : ∃ j, i = D + (k - mLen - 2 * D - 2) + 1 + j := ⟨i - (D + (k - mLen - 2 * D - 2) + 1), by omega⟩
      rw [show D + (k - mLen - 2 * D - 2) + 1 + j - (D + (k - mLen - 2 * D - 2)) = j + 1 by omega,
        show 1 + D + (D + (k - mLen - 2 * D - 2) + 1 + j) = k - mLen + j by omega, h.msg j (by omega)]
      simp [List.getD_eq_getElem?_getD]

/-- `EM`: `0x00 ‖ maskedSeed ‖ maskedDB`. -/
def emOf (G : Spec.Mgf1.Hash) (D k mLen : Nat) (sd lh m : List Byte) : List Byte :=
  let db := lh ++ Spec.RsaOaep.zeros (k - mLen - 2 * D - 2) ++ 0x01 :: m
  let mdb := Spec.Mgf1.xorBytes db (Spec.Mgf1.mgf1 G sd (k - D - 1))
  0 :: Spec.Mgf1.xorBytes sd (Spec.Mgf1.mgf1 G mdb D) ++ mdb

/-! ## The specification -/

theorem encrypt_none {H G : Spec.Mgf1.Hash} {nB eB label m seed : List Byte}
    (h : nB.length < 2 * H.len + 2 + m.length) : Spec.RsaOaep.encrypt H G nB eB label m seed = none := by
  simp only [Spec.RsaOaep.encrypt, Spec.RsaOaep.encode]
  rw [ifp (.inr h)]; rfl

theorem encrypt_some {H G : Spec.Mgf1.Hash} {nB eB label m seed : List Byte} (hs : seed.length = H.len)
    (h : 2 * H.len + 2 + m.length ≤ nB.length) :
    Spec.RsaOaep.encrypt H G nB eB label m seed =
      Spec.Rsa.publicOpChecked nB eB (emOf G H.len nB.length m.length seed (H.hash label) m) := by
  simp only [Spec.RsaOaep.encrypt, Spec.RsaOaep.encode]
  rw [ifn (by omega)]
  simp only [Option.bind_some, emOf]

end VG.Proof.RsaOaep
