module

import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Spec
public import VerifiedGarbage.Proof.RsaOaep.Mask
import VerifiedGarbage.Proof.RsaPss.CtPad
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Mgf1.Bytes
public import VerifiedGarbage.Impl.RsaPss.PPC64LE
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Base
public import VerifiedGarbage.Proof.RsaPss.EncBytes

/-!
# RSASSA-PSS signing on PPC64LE: the bytes written, as views

Untrusted: everything here is checked by Lean. Pure facts about the views of
our part of `scratch` (`view`): `M'`'s bytes after `mPrime` (`mPrime_bytes`);
`EM` before masking (`emPre`) after `clearEm`, `putSalt` and `putH`
(`emPre_of`); and `EM` after MGF1's mask and `clearTop` is `emT`
(`emT_of`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE.Sg

open VG VG.PPC64LE VG.WriteBytes
open VG.Impl.RsaOaep.PPC64LE (oEm oRsa)
open VG.Impl.RsaPss.PPC64LE (oY)
open VG.Proof.RsaOaep.PPC64LE (off off_off view view_wb view_w8)
open VG.Proof.RsaOaep (mixV range_ext)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)
open VG.Proof.RsaPss (getD_app)

theorem getD_rep0 (n i : Nat) : (List.replicate n (0 : Byte)).getD i 0 = 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl

theorem bytesAt_eq_view (m : Mem) (S : Addr) (d n : Nat) :
    Spec.Rsa.bytesAt m (off S d) n = (List.range n).map fun i => view m S (d + i) := by
  simp only [Spec.Rsa.bytesAt, view]
  exact List.map_congr_left fun i _ => by rw [← off_off]

/-- `M'` after `mPrime`. -/
theorem mPrime_bytes (m : Mem) (S : Addr) {D : Nat} (dig salt : List Byte) (hd : dig.length = D)
    (hl : oY + 8 + D + salt.length ≤ oRsa) :
    Spec.Rsa.bytesAt (writeBytes (writeBytes (writeBytes m (off S oY) (List.replicate 8 0)) (off S (oY + 8)) dig)
      (off S (oY + 8 + D)) salt) (off S oY) (8 + D + salt.length) = Spec.RsaPss.zeros 8 ++ dig ++ salt := by
  rw [bytesAt_eq_view]
  refine range_ext (by simp [Spec.RsaPss.zeros, hd]; omega) fun i hi => ?_
  rw [view_wb _ _ (by omega) (by omega), view_wb _ _ (by rw [hd]; omega) (by omega),
    view_wb _ _ (by simp; omega) (by omega), getD_app, getD_app]
  simp only [List.length_replicate, hd, Spec.RsaPss.zeros, List.length_append, getD_rep0]
  by_cases h1 : i < 8
  · rw [ifn (by omega), ifn (by omega), ifp ⟨by omega, by omega⟩, ifp (by omega), ifp h1]
  by_cases h2 : i < 8 + D
  · rw [ifn (by omega), ifp ⟨by omega, by omega⟩, ifp (by omega), ifn h1, show oY + i - (oY + 8) = i - 8 by omega]
  · rw [ifp ⟨by omega, by omega⟩, ifn (by omega), show oY + i - (oY + 8 + D) = i - (8 + D) by omega,
      show i - (8 + D) = i - 8 - D by omega]

/-- `EM` before masking, at offset `o < k`: zeros, `0x01`, the salt, `H` and
`0xbc`. -/
def emPre (k D sl : Nat) (salt h : List Byte) (o : Nat) : Byte :=
  if o = k - 1 then 0xbc else if k - D - 1 ≤ o then h.getD (o - (k - D - 1)) 0
  else if k - sl - D - 1 ≤ o then salt.getD (o - (k - sl - D - 1)) 0 else if o = k - sl - D - 2 then 1 else 0

/-- `EM` before masking, from the writes of `clearEm`, `putSalt` and `putH`. -/
theorem emPre_of {m m₁ m₂ m₃ : Mem} {S : Addr} {k D sl : Nat} {salt h : List Byte} (hs : salt.length = sl)
    (hh : h.length = D) (hk : k ≤ 1024) (hfit : sl + D + 2 ≤ k)
    (h₁ : m₁ = writeBytes m (off S oEm) (List.replicate k 0))
    (h₂ : m₂ = writeBytes (m₁.writeW (off S (oEm + (k - sl - D - 2))) (1 : Byte)) (off S (oEm + (k - sl - D - 1)))
      salt)
    (h₃ : m₃ = (writeBytes m₂ (off S (oEm + (k - D - 1))) h).writeW (off S (oEm + (k - 1))) (0xbc : Byte))
    {o : Nat} (ho : o < k) : view m₃ S o = emPre k D sl salt h o := by
  have hE : oEm = 0 := rfl
  have hR : oRsa = 8192 := rfl
  subst h₁ h₂ h₃
  rw [view_w8 _ _ (by omega) (by omega), view_wb _ _ (by rw [hh]; omega) (by omega),
    view_wb _ _ (by rw [hs]; omega) (by omega), view_w8 _ _ (by omega) (by omega),
    view_wb _ _ (by simp; omega) (by omega)]
  simp only [emPre, hE, Nat.zero_add, hs, hh, List.length_replicate, getD_rep0]
  rcases (by omega : o = k - 1 ∨ (k - D - 1 ≤ o ∧ o < k - 1) ∨ (k - sl - D - 1 ≤ o ∧ o < k - D - 1) ∨
      o = k - sl - D - 2 ∨ o < k - sl - D - 2) with h | h | h | h | h <;>
    simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right]

/-- `EM` after the mask with `mk` on `DB` (at `lo`, `db` bytes) and its first
byte ANDed with `c`: `emT`. -/
theorem emT_of {k D sl lo db : Nat} (salt h mk : List Byte) (c : Byte) (hh : h.length = D) (hlo : lo ≤ 1)
    (hdb : db = k - lo - D - 1) (hfit : sl + D + 2 ≤ k - lo) {V : Nat → Byte}
    (hV : ∀ o < k, V o = emPre k D sl salt h o) {o : Nat} (ho : o < k) :
    (if o = lo then mixV V mk lo db o &&& c else mixV V mk lo db o) = RsaPss.emT lo db sl salt h mk c o := by
  simp only [RsaPss.emT, mixV, hV o ho, emPre, hh]
  rcases (by omega : o < lo ∨ (lo ≤ o ∧ o < k - sl - D - 2) ∨ o = k - sl - D - 2 ∨
      (k - sl - D - 1 ≤ o ∧ o < k - D - 1) ∨ (k - D - 1 ≤ o ∧ o < k - 1) ∨ o = k - 1) with h | h | h | h | h | h
  · simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right]
  · by_cases h5 : o = lo
    · subst h5; simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right]
    · simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right]
  · by_cases h5 : o = lo
    · subst h5; simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right]
    · simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right]
  · rw [show o - (k - sl - D - 1) = o - lo - (db - sl) by omega]
    simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right]
  · rw [show o - (k - D - 1) = o - lo - db by omega]
    simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right]
  · simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right]

end VG.Proof.RsaPss.PPC64LE.Sg
