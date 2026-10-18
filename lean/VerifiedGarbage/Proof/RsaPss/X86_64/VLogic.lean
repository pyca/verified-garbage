module

public import VerifiedGarbage.Proof.RsaPss.X86_64.Scan
public import VerifiedGarbage.Proof.RsaPss.AnyHash
import VerifiedGarbage.Proof.Framework.Omega

/-!
# RSASSA-PSS verification on x86-64: what the code computes, against the checks

`vlogic`: the accumulator of the failed checks is zero and the salt's hash
is `H` exactly when the encoding is valid (`Any.EncOk`), byte by byte, for
the digest's hash function `H` and MGF1's `G`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64
open VG.Proof.RsaPss (lz)
open VG.Proof.MlKem.X86_64 (ifp ifn)

theorem list_eq_iff_getD {a b : List Byte} {n : Nat} (ha : a.length = n) (hb : b.length = n) :
    a = b ↔ ∀ i < n, a.getD i 0 = b.getD i 0 := by
  constructor
  · rintro rfl _ _; rfl
  · intro h
    apply List.ext_getElem (by omega)
    intro i h₁ h₂
    have := h i (by omega)
    rwa [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁,
      List.getElem?_eq_getElem h₂] at this

theorem ofNat_eq_iff {a : Nat} (ha : a < 2 ^ 64) (b : BitVec 64) : BitVec.ofNat 64 a = b ↔ a = b.toNat := by
  constructor
  · rintro rfl; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
  · rintro rfl; simp

/-- What the code computes, against the checks of `verifyEncoding`. -/
theorem vlogic {H G : Spec.Mgf1.Hash} (hH : Proof.Mgf1.Valid H) (x mHash : List Byte) {k lo z : Nat}
    (fixed : Bool) (slen : BitVec 64) {sLen : Option Nat} (hsl : sLen = if fixed then some slen.toNat else none)
    (hx : x.length = k) (hlo : lo ≤ 1) (hfit : H.len + 2 ≤ k - lo) (hk : k ≤ 1024) :
    let em := x.drop lo
    let L := k - lo - H.len - 1
    let dbL := Any.vDb H G em L z
    let fd := decide (lz dbL < L)
    let pos := if lz dbL < L then lz dbL else 0
    let val := if lz dbL < L then dbL.getD (lz dbL) 0 else 0
    (acc1V (acc0V (x.getD (k - 1) 0) (x.getD 0 0) (x.getD lo 0) ((0xFF : Byte) >>> z) lo) fd val fixed
        (BitVec.ofNat 64 (L - pos - 1)) slen = 0 ∧
      ∀ i < H.len, (H.hash (Spec.RsaPss.zeros 8 ++ mHash ++ dbL.drop (pos + 1))).getD i 0 =
        (Any.vH H em L).getD i 0) ↔
    ((lo = 1 → x.getD 0 0 = 0) ∧ Any.EncOk H G mHash em (k - lo) z sLen) := by
  dsimp only
  have hvH : (Any.vH H (x.drop lo) (k - lo - H.len - 1)).length = H.len := by simp [Any.vH]; omega
  rw [acc1V_eq_zero, acc0V_eq_zero _ _ _ _ hlo]
  have e1 : x.getD (k - 1) 0 = (x.drop lo).getD (k - lo - 1) 0 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]; congr 2; omega
  have e2 : x.getD lo 0 = (x.drop lo).getD 0 0 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_zero]
  rw [e1, e2]
  unfold Any.EncOk
  rw [← list_eq_iff_getD (hH.2 _) hvH]
  generalize Any.vDb H G (x.drop lo) (k - lo - H.len - 1) z = dbL
  by_cases hf : lz dbL < k - lo - H.len - 1
  · rw [ifp hf, ifp hf, decide_eq_true hf, ofNat_eq_iff (by omega)]
    subst hsl
    constructor
    · rintro ⟨⟨⟨hA, hP, hB⟩, hC, -, hS⟩, hH'⟩
      refine ⟨hP, hA, hB, hf, hC, ?_, hH'⟩
      cases fixed
      · exact .inl rfl
      · exact .inr (by rw [ifp rfl]; congr 1; have := hS rfl; omega)
    · rintro ⟨hP, hA, hB, -, hC, hS, hH'⟩
      refine ⟨⟨⟨hA, hP, hB⟩, hC, rfl, fun hfx => ?_⟩, hH'⟩
      subst hfx
      rw [ifp rfl] at hS
      rcases hS with h | h
      · cases h
      · have := Option.some.inj h; omega
  · rw [decide_eq_false hf]
    constructor
    · rintro ⟨⟨_, _, h, _⟩, _⟩; cases h
    · rintro ⟨_, _, _, h, _⟩; exact absurd h hf

end VG.Proof.RsaPss.X86_64
