module

public import VerifiedGarbage.Proof.RsaPss.X86_64.SHead
public import VerifiedGarbage.Proof.RsaPss.EncBytes
public import VerifiedGarbage.Proof.RsaOaep.Mask
import VerifiedGarbage.Proof.Framework.Omega

/-!
# RSASSA-PSS signing on x86-64: the encoding's bytes

From the bytes the blocks of `signEnc` leave (`V₃`, zero over `EM` with `H`
at `scratch + oDig`; `0x01` and the salt `sf`; `H`; `0xbc`; the mask XORed
into `DB` and its first byte ANDed with `c`), `EM`'s bytes are `emT`'s
(`em_bytes`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Impl.RsaOaep.X86_64 (oEm oSt oDig oRsa)
open VG.Proof.RsaOaep.X86_64 (upd cpV mOut mOut_iff)
open VG.Proof.RsaOaep (mixV srcB range_ext)
open VG.Proof.MlKem.X86_64 (ifp ifn)

/-- After `putSalt`: `0x01` at `P` and the salt after it. -/
abbrev sV4 (V₃ sf : Nat → Byte) (P sl : Nat) : Nat → Byte := cpV (upd V₃ P 1) sf (P + 1) sl

/-- After `putH`: `H` (at `scratch + oDig`) at `E` and `0xbc` at `K`. -/
abbrev sV5 (V₄ : Nat → Byte) (E D K : Nat) : Nat → Byte := upd (cpV V₄ (fun i => V₄ (oDig + i)) E D) K 0xbc

theorem em_bytes {G : Spec.Mgf1.Hash} {V₃ V₆ sf : Nat → Byte} {k lo db sl D : Nat} {h saltB : List Byte}
    {c : Byte} (hz : ∀ x < k, V₃ (oEm + x) = 0) (hdig : ∀ j < D, V₃ (oDig + j) = h.getD j 0)
    (hh : h.length = D) (hsf : ∀ j < sl, sf j = saltB.getD j 0) (hk : k ≤ 1024) (hlo : lo ≤ 1)
    (hdb : lo + db + D + 1 = k) (hfit : sl + 1 ≤ db)
    (h6 : ∀ o < oRsa, mOut o → V₆ o = mixV (sV5 (sV4 V₃ sf (oEm + lo + db - sl - 1) sl) (oEm + lo + db) D
      (oEm + k - 1)) (Spec.Mgf1.mgf1 G (srcB (sV5 (sV4 V₃ sf (oEm + lo + db - sl - 1) sl) (oEm + lo + db) D
        (oEm + k - 1)) (oEm + lo + db) D) db) (oEm + lo) db o) :
    ∀ i < k, upd V₆ (oEm + lo) (V₆ (oEm + lo) &&& c) (oEm + i) =
      RsaPss.emT lo db sl saltB h (Spec.Mgf1.mgf1 G h db) c i := by
  have c0 : oEm = 0 := rfl
  have c1 : oDig = 3328 := rfl
  have c2 : oRsa = 8192 := rfl
  have c3 : oSt = 3072 := rfl
  generalize hP : oEm + lo + db - sl - 1 = P at h6
  have hP' : P + 1 + sl = lo + db := by omega
  -- `V₄` and `V₅`, case by case.
  have h4 : ∀ x, sV4 V₃ sf P sl x =
      if P + 1 ≤ x ∧ x < P + 1 + sl then sf (x - (P + 1)) else if x = P then 1 else V₃ x := fun _ => rfl
  have h5 : ∀ x, sV5 (sV4 V₃ sf P sl) (oEm + lo + db) D (oEm + k - 1) x =
      if x = oEm + k - 1 then 0xbc else if oEm + lo + db ≤ x ∧ x < oEm + lo + db + D then
        sV4 V₃ sf P sl (oDig + (x - (oEm + lo + db))) else sV4 V₃ sf P sl x := fun _ => rfl
  have hH : srcB (sV5 (sV4 V₃ sf P sl) (oEm + lo + db) D (oEm + k - 1)) (oEm + lo + db) D = h :=
    range_ext hh fun j hj => by
      rw [h5, ifn (by omega), ifp ⟨by omega, by omega⟩, h4, ifn (by omega), ifn (by omega),
        show oEm + lo + db + j - (oEm + lo + db) = j by omega, hdig j hj]
  rw [hH] at h6
  intro i hi
  have hm : mOut (oEm + i) := (mOut_iff _).mpr (.inl (by omega))
  have e6 := h6 (oEm + i) (by omega) hm
  have e6' := h6 (oEm + lo) (by omega) ((mOut_iff _).mpr (.inl (by omega)))
  simp only [mixV] at e6 e6'
  show (if oEm + i = oEm + lo then V₆ (oEm + lo) &&& c else V₆ (oEm + i)) = _
  simp only [RsaPss.emT]
  by_cases hl : i < lo
  · rw [ifn (by omega), e6, ifn (by omega), h5, ifn (by omega), ifn (by omega), h4, ifn (by omega), ifn (by omega),
      hz i hi, ifp hl]
  rw [ifn hl]
  by_cases hd : i - lo < db
  · rw [ifp hd]
    have hv : sV5 (sV4 V₃ sf P sl) (oEm + lo + db) D (oEm + k - 1) (oEm + i) =
        if i - lo < db - sl - 1 then 0 else if i - lo = db - sl - 1 then 1 else saltB.getD (i - lo - (db - sl)) 0 := by
      rw [h5, ifn (by omega), ifn (by omega), h4]
      by_cases hs : P + 1 ≤ oEm + i
      · rw [ifp ⟨hs, by omega⟩, hsf _ (by omega), ifn (by omega), ifn (by omega),
          show oEm + i - (P + 1) = i - lo - (db - sl) by omega]
      · rw [ifn (by omega)]
        by_cases hq : oEm + i = P
        · rw [ifp hq, ifn (by omega), ifp (by omega)]
        · rw [ifn hq, hz i hi, ifp (by omega)]
    by_cases h0 : i = lo
    · subst h0
      rw [ifp (by omega), e6', ifp ⟨by omega, by omega⟩, ifp (by omega), Nat.sub_self]
      rw [show oEm + i = oEm + i from rfl] at hv
      rw [hv]
      simp only [Nat.sub_self]
    · rw [ifn (show ¬ oEm + i = oEm + lo by omega), e6, ifp ⟨by omega, by omega⟩, hv,
        ifn (show ¬ i - lo = 0 by omega), show oEm + i - (oEm + lo) = i - lo by omega]
  · rw [ifn hd, ifn (show ¬ oEm + i = oEm + lo by omega), e6,
      ifn (show ¬ (oEm + lo ≤ oEm + i ∧ oEm + i < oEm + lo + db) by omega), hh]
    by_cases hH' : i - lo < db + D
    · rw [ifp hH', h5, ifn (by omega), ifp ⟨by omega, by omega⟩, h4, ifn (by omega), ifn (by omega),
        show oEm + i - (oEm + lo + db) = i - lo - db by omega, hdig _ (by omega)]
    · rw [ifn hH', h5, ifp (by omega)]

end VG.Proof.RsaPss.X86_64
