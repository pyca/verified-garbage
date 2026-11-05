module

-- separate module: it builds in parallel with the constant-time proofs (`CTHash`, `CTPost`), which `Verified`
-- also needs.

public import VerifiedGarbage.Proof.RsaPss.RISCV64.Post
public import VerifiedGarbage.Proof.RsaPss.VerifyCases
import VerifiedGarbage.Proof.RsaPss.EncBytes
import VerifiedGarbage.Proof.RsaPss.Encoding
import VerifiedGarbage.Proof.Mgf1.Bytes
public import VerifiedGarbage.Proof.RsaPss.RISCV64.Call
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Mgf
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
public import VerifiedGarbage.Impl.RsaPss.RISCV64
public import VerifiedGarbage.Proof.RsaPss.RISCV64.Pre
public import VerifiedGarbage.Proof.RsaPss.RISCV64.Prefix

/-!
# RSASSA-PSS verification on RISC-V: correctness

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPss/PPC64LE/Correct.lean`): the checks (`checks_done`), a
modulus whose first byte is zero (`verify_zero`), and an encoding too short
for the digest (`chkEm`) or the salt length expected (`expLen`, `chkSalt`:
`verify_short`) return 0; otherwise RSAVP1 of the signature (`call_ok`) and
the checks of `EM` (`post_ok`) return 1 exactly when EMSA-PSS-VERIFY accepts
it (`res_iff`, `verify_bytes`), if `pre` holds the modulus' values.
`code_correct`: the function against its shared contract.
-/

@[expose] public section

/-!
# RSASSA-PSS verification on RISC-V: the checks are EMSA-PSS-VERIFY's

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPss/PPC64LE/Logic.lean`): for `EM` of `emLen = E`
bytes after `lo` (`lN`) in the view `V`, `DB` unmasked as the code does
(`wR`) is `Proof.RsaPss.vDb` (`wR_eq`), and `Res` (`Post.lean`) holds
exactly when the leading byte is zero if `lo = 1` and the encoding is
consistent byte by byte (`Proof.RsaPss.EncOk`, `res_iff`).
-/


namespace VG.Proof.RsaPss.RISCV64

open VG
open VG.Proof.RsaPss (lz vDb vH EncOk vDb₂ EncOk₂)
open VG.Proof.RsaPss (xorBytes_getD clearTop_getD zeros_getD eq_range_map)
open VG.Proof.RsaOaep (mixV srcB)
open VG.Proof.Mgf1 (ifp ifn Valid mgf1_length xorBytes_length)
open VG.Spec.RsaPss (zeros clearTop)

section
variable {Gs Hs : Spec.Mgf1.Hash} {V : Nat → Byte} {em : List Byte} {lN E : Nat} {c : Byte} {z : Nat}

theorem vH_getD (hfE : Hs.len + 2 ≤ E) (hV : ∀ i < E, V (lN + i) = em.getD i 0) {i : Nat} (hi : i < Hs.len) :
    (vH Hs em (E - Hs.len - 1)).getD i 0 = V (lN + (E - Hs.len - 1) + i) := by
  simp only [vH, List.getD_eq_getElem?_getD, List.getElem?_take, ifp hi, List.getElem?_drop]
  rw [← List.getD_eq_getElem?_getD, Nat.add_assoc, hV _ (by omega)]

theorem vH_length (hE : em.length = E) (hfE : Hs.len + 2 ≤ E) : (vH Hs em (E - Hs.len - 1)).length = Hs.len := by
  simp only [vH, List.length_take, List.length_drop, hE]; omega

theorem srcB_vH (hE : em.length = E) (hfE : Hs.len + 2 ≤ E) (hV : ∀ i < E, V (lN + i) = em.getD i 0) :
    srcB (v1 V lN c (lN + E)) (lN + (E - Hs.len - 1)) Hs.len = vH Hs em (E - Hs.len - 1) := by
  refine (eq_range_map (vH_length hE hfE) fun i hi => ?_).symm
  rw [vH_getD hfE hV hi, v1, ifn (by omega)]

theorem wR_eq (hGv : Valid Gs) (hc : c = (0xFF : Byte) >>> z) (hE : em.length = E) (hfE : Hs.len + 2 ≤ E)
    (hV : ∀ i < E, V (lN + i) = em.getD i 0) {j : Nat} (hj : j < E - Hs.len - 1) :
    wR Gs V Hs.len lN (E - Hs.len - 1) c (lN + E) j = (vDb₂ Gs Hs em (E - Hs.len - 1) z).getD j 0 := by
  have hmk := mgf1_length hGv (vH Hs em (E - Hs.len - 1)) (E - Hs.len - 1)
  have ht : ∀ {i}, i < E - Hs.len - 1 → (em.take (E - Hs.len - 1)).getD i 0 = em.getD i 0 := fun hi => by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, ifp hi]
  let mk := Spec.Mgf1.mgf1 Gs (vH Hs em (E - Hs.len - 1)) (E - Hs.len - 1)
  have hm : mixV (v1 V lN c (lN + E)) (Spec.Mgf1.mgf1 Gs (srcB (v1 V lN c (lN + E)) (lN + (E - Hs.len - 1)) Hs.len)
      (E - Hs.len - 1)) lN (E - Hs.len - 1) (lN + j) = em.getD j 0 ^^^ mk.getD j 0 := by
    rw [srcB_vH hE hfE hV, mixV, ifp ⟨by omega, by omega⟩, v1, ifn (by omega), hV _ (by omega),
      Nat.add_sub_cancel_left]
  have hx : (Spec.Mgf1.xorBytes (em.take (E - Hs.len - 1)) mk).getD j 0 = em.getD j 0 ^^^ mk.getD j 0 := by
    rw [xorBytes_getD (by rw [List.length_take, hE]; omega) (by simp only [mk]; omega), ht hj]
  show (if lN + j = lN then _ &&& c else _) = _
  rw [vDb₂, clearTop_getD]
  by_cases e : j = 0
  · subst e
    rw [ifp (Nat.add_zero lN), ifp rfl, hm, ← hx, hc]
  · rw [ifn (by omega), ifn e, hm, ← hx]

end

section
variable {Gs Hs : Spec.Mgf1.Hash} (hGv : Valid Gs) {V : Nat → Byte} {em mh : List Byte} {lN E : Nat} {c : Byte}
  {z : Nat} (hc : c = (0xFF : Byte) >>> z) (hE : em.length = E) (hfE : Hs.len + 2 ≤ E)
  (hV : ∀ i < E, V (lN + i) = em.getD i 0)

include hGv hc hE hfE hV in
theorem db_eq : vDb₂ Gs Hs em (E - Hs.len - 1) z = (List.range (E - Hs.len - 1)).map (wR Gs V Hs.len lN (E - Hs.len - 1) c (lN + E)) := by
  refine eq_range_map (by simp [vDb₂, VG.Proof.RsaPss.clearTop_length, xorBytes_length, mgf1_length hGv, hE]; omega)
    fun j hj => (wR_eq hGv hc hE hfE hV hj).symm

include hGv hc hE hfE hV in
theorem lzr_eq : lzr (wR Gs V Hs.len lN (E - Hs.len - 1) c (lN + E)) (E - Hs.len - 1) = lz (vDb₂ Gs Hs em (E - Hs.len - 1) z) := by
  rw [db_eq hGv hc hE hfE hV]; rfl

include hGv hc hE hfE hV in
/-- `M'` is the specification's once the delimiter is found and the salt
length is the expected one. -/
theorem mR_eq (hmh : mh.length = Hs.len) {any saltLen : BitVec 64}
    (hlz : lz (vDb₂ Gs Hs em (E - Hs.len - 1) z) < E - Hs.len - 1)
    (hsl : any = 0 → saltLen.toNat = E - Hs.len - 1 - 1 - lz (vDb₂ Gs Hs em (E - Hs.len - 1) z)) :
    mR Gs V Hs.len lN (E - Hs.len - 1) c (lN + E) mh any saltLen =
      zeros 8 ++ mh ++ (vDb₂ Gs Hs em (E - Hs.len - 1) z).drop (lz (vDb₂ Gs Hs em (E - Hs.len - 1) z) + 1) := by
  have hl := lzr_eq hGv hc hE hfE hV
  generalize hdb : vDb₂ Gs Hs em (E - Hs.len - 1) z = db at hl hlz hsl
  have hdl : db.length = E - Hs.len - 1 := by
    rw [← hdb]; simp [vDb₂, VG.Proof.RsaPss.clearTop_length, xorBytes_length, mgf1_length hGv, hE]; omega
  have hp : posR Gs V Hs.len lN (E - Hs.len - 1) c (lN + E) = lz db := by rw [posR, hl, ifp hlz]
  have hw : ∀ j < E - Hs.len - 1, dbV Gs (v1 V lN c (lN + E)) lN (E - Hs.len - 1) Hs.len c (lN + j) = db.getD j 0 :=
    fun j hj => by rw [← hdb, ← wR_eq hGv hc hE hfE hV hj]; rfl
  have hd : ∀ j < E - Hs.len - 1 - lz db - 1, (db.drop (lz db + 1)).getD j 0 =
      dbV Gs (v1 V lN c (lN + E)) lN (E - Hs.len - 1) Hs.len c (lN + (j + (lz db + 1))) := fun j hj => by
    rw [hw _ (by omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
    congr 2; omega
  have hdd : (db.drop (lz db + 1)).length = E - Hs.len - 1 - lz db - 1 := by rw [List.length_drop, hdl]; omega
  rw [mR]
  split
  · rename_i h0
    have h1 := hsl h0
    rw [mFix, h1, show E - Hs.len - 1 - 1 - lz db = E - Hs.len - 1 - lz db - 1 by omega]
    refine congrArg (List.replicate 8 0 ++ mh ++ ·) (eq_range_map hdd fun j hj => ?_).symm
    rw [hd j (by omega)]; congr 1; omega
  · rw [mAny, hp, slR, hp]
    refine congrArg (List.replicate 8 0 ++ mh ++ ·) (eq_range_map hdd fun j hj => ?_).symm
    rw [hd j (by omega), ifp (by omega)]

end

theorem setWidth64_eq_zero (a : Byte) : a.setWidth 64 = 0#64 ↔ a = 0 := by
  constructor
  · intro h
    have := congrArg (BitVec.setWidth 8) h
    rwa [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq] at this
  · rintro rfl; rfl

theorem setWidth64_xor1 (a : Byte) : (a.setWidth 64 ^^^ 1#64) = 0#64 ↔ a = 1 := by
  rw [BitVec.xor_eq_zero_iff]
  constructor
  · intro h
    have := congrArg (BitVec.setWidth 8) h
    rwa [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq] at this
  · rintro rfl; rfl

section
variable {Gs Hs : Spec.Mgf1.Hash} (hGv : Valid Gs) (hHv : Valid Hs) {V : Nat → Byte} {em mh : List Byte}
  {lN E : Nat} {c : Byte}
  {z : Nat} (hc : c = (0xFF : Byte) >>> z) (hE : em.length = E) (hfE : Hs.len + 2 ≤ E)
  (hV : ∀ i < E, V (lN + i) = em.getD i 0) (hmh : mh.length = Hs.len)
include hGv hHv hc hE hfE hV hmh

theorem res_iff {any saltLen : BitVec 64} {sLen : Option Nat} (hs : sLen = if any = 0 then some saltLen.toNat else none)
    (hE64 : E < 2 ^ 64) :
    Res Gs V Hs.len lN (E - Hs.len - 1) c (lN + E) mh any saltLen Hs ↔
      (lN = 1 → V 0 = 0) ∧ EncOk₂ Gs Hs mh em E z sLen := by
  have hl := lzr_eq hGv hc hE hfE hV
  have hw : ∀ j < E - Hs.len - 1, wR Gs V Hs.len lN (E - Hs.len - 1) c (lN + E) j =
      (vDb₂ Gs Hs em (E - Hs.len - 1) z).getD j 0 := fun j hj => wR_eq hGv hc hE hfE hV hj
  have hk1 : lN + E - 1 = lN + (E - 1) := by omega
  have hV0 : V lN = em.getD 0 0 := hV 0 (by omega)
  have hVk : V (lN + E - 1) = em.getD (E - 1) 0 := by rw [hk1]; exact hV _ (by omega)
  have hnot : ~~~c = ~~~((0xFF : Byte) >>> z) := by rw [hc]
  -- The hash compared, as lists.
  have hcmp : ∀ M : List Byte, (∀ i < Hs.len, V (lN + (E - Hs.len - 1) + i) = (Hs.hash M).getD i 0) ↔
      Hs.hash M = vH Hs em (E - Hs.len - 1) := fun M => by
    constructor
    · intro h
      refine List.ext_getElem (by rw [hHv.2, vH_length hE hfE]) fun i h₁ h₂ => ?_
      have e := h i (by rw [hHv.2] at h₁; exact h₁)
      rw [← vH_getD hfE hV (by rw [hHv.2] at h₁; exact h₁), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem h₁, List.getElem?_eq_getElem h₂] at e
      exact e.symm
    · intro h i hi; rw [h, vH_getD hfE hV hi]
  have hval : valR Gs V Hs.len lN (E - Hs.len - 1) c (lN + E) = 1 ↔
      lz (vDb₂ Gs Hs em (E - Hs.len - 1) z) < E - Hs.len - 1 ∧
        (vDb₂ Gs Hs em (E - Hs.len - 1) z).getD (lz (vDb₂ Gs Hs em (E - Hs.len - 1) z)) 0 = 1 := by
    unfold valR; rw [hl]
    by_cases h : lz (vDb₂ Gs Hs em (E - Hs.len - 1) z) < E - Hs.len - 1
    · rw [ifp h, hw _ h]; simp [h]
    · rw [ifn h]; simp [h]
  have hsl : lz (vDb₂ Gs Hs em (E - Hs.len - 1) z) < E - Hs.len - 1 →
      slR Gs V Hs.len lN (E - Hs.len - 1) c (lN + E) = E - Hs.len - 1 - 1 - lz (vDb₂ Gs Hs em (E - Hs.len - 1) z) :=
    fun h => by unfold slR posR; rw [hl, ifp h]; omega
  have hsv : (sLen = none ∨ sLen = some (E - Hs.len - 1 - 1 - lz (vDb₂ Gs Hs em (E - Hs.len - 1) z))) ↔
      (any = 0 → saltLen.toNat = E - Hs.len - 1 - 1 - lz (vDb₂ Gs Hs em (E - Hs.len - 1) z)) := by
    rw [hs]; split
    · rename_i h0; simp [h0]
    · rename_i h0; exact ⟨fun _ e => absurd e h0, fun _ => Or.inl rfl⟩
  have hany : lz (vDb₂ Gs Hs em (E - Hs.len - 1) z) < E - Hs.len - 1 →
      ((if any = 0 then BitVec.ofNat 64 (slR Gs V Hs.len lN (E - Hs.len - 1) c (lN + E)) ^^^ saltLen else 0#64) =
        0#64 ↔ (any = 0 → saltLen.toNat = E - Hs.len - 1 - 1 - lz (vDb₂ Gs Hs em (E - Hs.len - 1) z))) := fun h => by
    rw [hsl h]
    split
    · rename_i h0
      rw [BitVec.xor_eq_zero_iff]
      constructor
      · intro e _; rw [← e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      · intro e; rw [← e h0, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rename_i h0; exact ⟨fun _ e => absurd e h0, fun _ => rfl⟩
  unfold Res accR accW EncOk₂
  rw [BitVec.or_eq_zero_iff, BitVec.or_eq_zero_iff, setWidth64_eq_zero, accB_eq_zero, setWidth64_xor1, hVk, hV0, hnot]
  constructor
  · rintro ⟨⟨⟨⟨ha1, ha2, ha3⟩, hv⟩, hy⟩, hh⟩
    obtain ⟨hlz, h1⟩ := hval.mp hv
    have hy' := (hany hlz).mp hy
    refine ⟨ha3, ha1, ha2, hlz, h1, hsv.mpr hy', ?_⟩
    rw [← mR_eq hGv hc hE hfE hV hmh hlz hy']
    exact (hcmp _).mp hh
  · rintro ⟨ha3, ha1, ha2, hlz, h1, hy, hh⟩
    have hy' := hsv.mp hy
    refine ⟨⟨⟨⟨ha1, ha2, ha3⟩, hval.mpr ⟨hlz, h1⟩⟩, (hany hlz).mpr hy'⟩, ?_⟩
    rw [mR_eq hGv hc hE hfE hV hmh hlz hy']
    exact (hcmp _).mpr hh
end

end VG.Proof.RsaPss.RISCV64


namespace VG.Proof.RsaPss.RISCV64

open VG VG.RISCV64 VG.Impl.RsaPss.RISCV64
open VG.Impl.RsaOaep.RISCV64 (frameBytes restore)
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.RsaOaep.RISCV64 (Base Fits SC off off_off view kR fx fixed Saves restore_ok ne_zero_ltBit msgBit
  stackBytes TabS stackArgAddr_eq)
open VG.Impl.RsaOaep.RISCV64 (Fns)
open VG.Spec.RsaPss (emLength bitLength verify verifyEncoding zeros)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only wp_li wp_sub wp_subi wp_srl wp_or wp_mov wp_nil eval_zero eval_nonzero)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)
open VG.Proof.Mgf1 (ifp ifn)

/-! ## The specification's cases, with the hash function `Hs` and MGF1's `Gs` -/

/-- An encoding too short for the digest and the salt is refused. -/
theorem verify_short₂ (Gs Hs : Spec.Mgf1.Hash) {nB : List Byte} (eB mHash sB : List Byte) {sLen : Option Nat}
    (h : emLength (bitLength (Spec.Rsa.os2ip nB) - 1) < Hs.len + sLen.getD 0 + 2) :
    verify Hs Gs nB eB mHash sB sLen = false := by
  unfold verify
  cases Spec.Rsa.publicOpChecked nB eB sB with
  | none => simp
  | some x =>
    have : verifyEncoding Hs Gs mHash (x.drop (nB.length - emLength (bitLength (Spec.Rsa.os2ip nB) - 1)))
        (bitLength (Spec.Rsa.os2ip nB) - 1) sLen = false := by
      unfold verifyEncoding
      rw [ifp (Or.inr (Or.inr h))]
    simp [this]

/-- `verify`, byte by byte, as `Proof.RsaPss.verify_bytes`, with the hash
function `Hs` and MGF1's `Gs`. -/
theorem verify_bytes₂ (Gs Hs : Spec.Mgf1.Hash) (hG : Proof.Mgf1.Valid Gs) {n₀ : Byte} {rest eB mHash sB : List Byte}
    {sLen : Option Nat} (hm : mHash.length = Hs.len) (hs : sB.length = (n₀ :: rest).length) {emBits emLen lo : Nat}
    (hb : bitLength (Spec.Rsa.os2ip (n₀ :: rest)) - 1 = emBits) (he : emLength emBits = emLen)
    (hk : emLen + lo = (n₀ :: rest).length) (hlo : lo ≤ 1) (hfit : Hs.len + sLen.getD 0 + 2 ≤ emLen) :
    verify Hs Gs (n₀ :: rest) eB mHash sB sLen = true ↔
      (lo = 1 → ((Spec.Rsa.publicOpChecked (n₀ :: rest) eB sB).getD (zeros (n₀ :: rest).length)).getD 0 0 = 0) ∧
      EncOk₂ Gs Hs mHash (((Spec.Rsa.publicOpChecked (n₀ :: rest) eB sB).getD (zeros (n₀ :: rest).length)).drop lo)
        emLen (8 * emLen - emBits) sLen := by
  have hlo' : (n₀ :: rest).length - emLen = lo := by omega
  unfold verify
  simp only [hb, he, hs, beq_self_eq_true, Bool.true_and, hlo']
  cases hp : Spec.Rsa.publicOpChecked (n₀ :: rest) eB sB with
  | none =>
    simp only [Option.getD_none, Bool.false_eq_true, false_iff, not_and]
    intro _ h
    have := h.1
    simp only [zeros, List.getD_eq_getElem?_getD, List.getElem?_drop, List.getElem?_replicate] at this
    split at this <;> simp at this
  | some x =>
    have hx := Proof.RsaPss.publicOpChecked_length' hp
    simp only [Option.getD_some, Bool.and_eq_true, beq_iff_eq]
    rw [← he, Proof.RsaPss.verifyEncoding_bytes₂ Gs Hs hG hm (by rw [List.length_drop, hx]; omega) (by omega), he]
    refine and_congr_left fun _ => ?_
    rcases (show lo = 0 ∨ lo = 1 by omega) with rfl | rfl
    · simp [zeros]
    · obtain ⟨b, xs, rfl⟩ := List.exists_cons_of_ne_nil (show x ≠ [] from fun h => by simp [h] at hx)
      simp [zeros]

/-- What the function returns, from its entry state, with the hash function
`Hs` and MGF1's `Gs`. -/
def vOut (Hs Gs : Spec.Mgf1.Hash) (s : State) : Bool :=
  Spec.RsaPss.verify Hs Gs (Spec.Rsa.bytesAt s.mem (s.gpr .a0) (kk s))
    (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) (mh Hs.len s) (Spec.Rsa.bytesAt s.mem (s.gpr .a6) (kk s))
    (Spec.RsaPss.expectedSaltLen (stackArg s 0) ((stackArg s 1).setWidth 32))

/-- The result, from the entry state `s`. -/
def Post (Hs Gs : Spec.Mgf1.Hash) (s s' : State) : Prop :=
  abiPreserved s s' ∧ (PreOk s → s'.gpr .a0 = if vOut Hs Gs s then 1 else 0)

/-- Before the restores. -/
def Done (Hs Gs : Spec.Mgf1.Hash) (s t : State) : Prop :=
  Saves s t ∧ (PreOk s → t.gpr .a0 = if vOut Hs Gs s then 1 else 0)

/-- `lo` and `c`, from the modulus' first byte. -/
def loN (s : State) : Nat := if (s.mem (s.gpr .a0)).toNat = 1 then 1 else 0
def cB (s : State) : Byte :=
  if (s.mem (s.gpr .a0)).toNat = 1 then 0xFF else BitVec.ofNat 8 (2 ^ Nat.log2 (s.mem (s.gpr .a0)).toNat - 1)

theorem anyL_eq (s : State) : anyL s = 0 ↔ (stackArg s 1).setWidth 32 = 0 := by
  have e : (anyL s).toNat = ((stackArg s 1).setWidth 32).toNat := by
    have := (stackArg s 1).isLt
    simp only [anyL, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq,
      Nat.shiftRight_eq_div_pow]
    omega
  constructor <;> intro h <;> apply BitVec.eq_of_toNat_eq
  · rw [← e, h]; rfl
  · rw [e, h]; rfl

theorem sLen_eq (s : State) : Spec.RsaPss.expectedSaltLen (stackArg s 0) ((stackArg s 1).setWidth 32) =
    if anyL s = 0 then some (stackArg s 0).toNat else none := by
  unfold Spec.RsaPss.expectedSaltLen
  by_cases h : anyL s = 0
  · rw [ifp h, ifp ((anyL_eq s).mp h)]
  · rw [ifn h, ifn fun h' => h ((anyL_eq s).mpr h')]

theorem bytesAt_cons (m : Mem) (p : Addr) (n : Nat) :
    ∃ rest : List Byte, Spec.Rsa.bytesAt m p (n + 1) = m p :: rest ∧ rest.length = n :=
  ⟨(List.range n).map fun i => m (p + BitVec.ofNat 64 (i + 1)), by
    simp only [Spec.Rsa.bytesAt, List.range_succ_eq_map, List.map_cons, List.map_map]
    rw [show p + BitVec.ofNat 64 0 = p by simp]; rfl, by simp⟩

theorem bytesAt_getD (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (Spec.Rsa.bytesAt m p n).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, hi]

theorem emOf_length (s : State) : (emOf s).length = kk s := by
  unfold emOf
  cases hp : Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .a0) (kk s))
    (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .a6) (kk s)) with
  | none => simp
  | some y => rw [Option.getD_some, Proof.RsaPss.publicOpChecked_length' hp, bytesAt_length]

/-! ## The specification's cases -/

section
variable (Hs Gs : Spec.Mgf1.Hash) {s : State} (hk : 1 ≤ kk s)
include hk

theorem nB_cons : ∃ rest : List Byte, Spec.Rsa.bytesAt s.mem (s.gpr .a0) (kk s) = s.mem (s.gpr .a0) :: rest ∧
    rest.length = kk s - 1 := by
  obtain ⟨rest, h, hl⟩ := bytesAt_cons s.mem (s.gpr .a0) (kk s - 1)
  rw [show kk s - 1 + 1 = kk s by omega] at h
  exact ⟨rest, h, hl⟩

theorem zero_false (h0 : s.mem (s.gpr .a0) = 0) : vOut Hs Gs s = false := by
  obtain ⟨rest, hn, -⟩ := nB_cons hk
  rw [vOut, hn, h0]
  exact Proof.RsaPss.verify_zero₂ Gs Hs _ _ _ _ _

theorem emLen_eq (h0 : s.mem (s.gpr .a0) ≠ 0) {rest : List Byte} (hr : rest.length = kk s - 1) :
    Spec.RsaPss.emLength (Spec.RsaPss.bitLength (Spec.Rsa.os2ip (s.mem (s.gpr .a0) :: rest)) - 1) =
      kk s - loN s := by
  rw [Proof.RsaPss.emLength_eq rest h0, hr, loN]; split <;> omega

theorem short_false (h0 : s.mem (s.gpr .a0) ≠ 0)
    (h : kk s - loN s < Hs.len + (Spec.RsaPss.expectedSaltLen (stackArg s 0) ((stackArg s 1).setWidth 32)).getD 0 + 2) :
    vOut Hs Gs s = false := by
  obtain ⟨rest, hn, hr⟩ := nB_cons hk
  rw [vOut, hn]
  exact verify_short₂ Gs Hs _ _ _ (by rw [emLen_eq hk h0 hr]; exact h)

end

/-- `Res` is verification, for `EM` in place. -/
theorem res_vOut {Hs Gs : Spec.Mgf1.Hash} (hGv : Proof.Mgf1.Valid Gs) (hHv : Proof.Mgf1.Valid Hs) {s : State}
    (P : PreP Hs.len s)
    (h0 : s.mem (s.gpr .a0) ≠ 0) {m : Mem} (hm : Spec.Rsa.bytesAt m (off (Sp s) 0) (kk s) = emOf s)
    (hem : Hs.len + 2 ≤ kk s - loN s)
    (hfit : anyL s = 0 → (stackArg s 0).toNat + 1 ≤ kk s - loN s - Hs.len - 1) :
    Res Gs (view m (Sp s)) Hs.len (loN s) (kk s - loN s - Hs.len - 1) (cB s) (kk s) (mh Hs.len s) (anyL s)
      (stackArg s 0) Hs ↔ vOut Hs Gs s = true := by
  have hk1 : 64 ≤ kk s := P.k1; have hk2 : kk s ≤ 1024 := P.k2
  have hl1 : loN s ≤ 1 := by unfold loN; split <;> omega
  obtain ⟨rest, hn, hr⟩ := nB_cons (show 1 ≤ kk s by omega)
  have hE := emLen_eq (by omega) h0 hr
  have hM := Proof.RsaPss.mask_eq rest h0
  have hx : (Spec.Rsa.publicOpChecked (s.mem (s.gpr .a0) :: rest) (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .a6) (kk s))).getD (Spec.RsaPss.zeros (s.mem (s.gpr .a0) :: rest).length) =
      emOf s := by
    rw [emOf, hn, Spec.RsaPss.zeros, List.length_cons, hr, show kk s - 1 + 1 = kk s by omega]
  generalize hB : Spec.RsaPss.bitLength (Spec.Rsa.os2ip (s.mem (s.gpr .a0) :: rest)) - 1 = eb at hE hM
  generalize hEg : Spec.RsaPss.emLength eb = E at hE hM
  have hc : cB s = (0xFF : Byte) >>> (8 * E - eb) := by rw [hM]; rfl
  have hV : ∀ i < E, view m (Sp s) (loN s + i) = ((emOf s).drop (loN s)).getD i 0 := fun i hi => by
    show m (off (Sp s) (loN s + i)) = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD, ← hm,
      bytesAt_getD _ _ (by omega), show off (Sp s) 0 + BitVec.ofNat 64 (loN s + i) = off (off (Sp s) 0) (loN s + i)
      from rfl, off_off, Nat.zero_add]
  have hV0 : view m (Sp s) 0 = (emOf s).getD 0 0 := by
    rw [← hm, bytesAt_getD _ _ (by omega), BitVec.add_zero]; rfl
  have hEl : ((emOf s).drop (loN s)).length = E := by rw [List.length_drop, emOf_length]; omega
  rw [show kk s - loN s - Hs.len - 1 = E - Hs.len - 1 by omega, show kk s = loN s + E by omega,
    res_iff (E := E) hGv hHv hc hEl (by omega) hV (bytesAt_length _ _ _) (sLen_eq s) (by omega), vOut, hn,
    verify_bytes₂ Gs Hs hGv (bytesAt_length _ _ _) (by rw [bytesAt_length, List.length_cons, hr]; omega)
      hB hEg (by rw [List.length_cons, hr]; omega) hl1 ?_, hx, hV0]
  rw [sLen_eq]; split
  · rename_i h; have := hfit h; simp only [Option.getD_some]; omega
  · simp only [Option.getD_none]; omega

/-! ## The tables, after the public operation -/

section
variable {D : Nat} {s : State} (P : PreP D s)
include P

omit P in
theorem tabSub {p : Addr} {n k : Nat} (hk : 8 * k + 8 ≤ n * 8) :
    Region.Sub ⟨p + BitVec.ofNat 64 (8 * k), 8⟩ (Sig.tableRegion 64 p n) :=
  Offset.sub_base p (by show 8 * k + 8 ≤ n * (64 / 8); omega)

/-- The stack argument `j` is apart from the stack and the working space. -/
theorem arg_dis {j : Nat} (hj : j < 8) : ∀ r ∈ [kR s, scR s], Region.Disjoint ⟨stackArgAddr s j, 8⟩ r := by
  intro r hr
  have hs : Region.Sub ⟨stackArgAddr s j, 8⟩ (aR s) := by
    rw [stackArgAddr_eq]; exact Offset.sub_base _ (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (P.ka.sub_right hs).symm
  · exact (P.sa.sub_right hs).symm

/-- So are the first five words of the table `hash`… -/
theorem tabH_dis : ∀ k < 5, ∀ r ∈ [kR s, scR s],
    Region.Disjoint ⟨stackArg s 6 + BitVec.ofNat 64 (8 * k), 8⟩ r := by
  intro k hk r hr
  have hs := tabSub (p := stackArg s 6) (n := 11) (k := k) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (P.kth.sub_right hs).symm
  · exact (P.sth.sub_right hs).symm

/-- …and of the table `mgf1`. -/
theorem tabG_dis : ∀ k < 5, ∀ r ∈ [kR s, scR s],
    Region.Disjoint ⟨stackArg s 7 + BitVec.ofNat 64 (8 * k), 8⟩ r := by
  intro k hk r hr
  have hs := tabSub (p := stackArg s 7) (n := 5) (k := k) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (P.ktg.sub_right hs).symm
  · exact (P.stg.sub_right hs).symm

end

/-! ## The code -/

section
variable {Hs Gs : Spec.Mgf1.Hash} {s : State} (P : PreP Hs.len s)
include P

theorem fail_ok {t : State} (h : Base Sp (vP Hs.len) s t) (hv : vOut Hs Gs s = false) :
    WP isa Impl.RsaPss.RISCV64.fail t (Done Hs Gs s) :=
  wp_li (imm := 0) (by decide) fun t' o e => wp_nil ⟨(h.only P.fits o).sv, fun _ => by rw [e, hv]; rfl⟩

omit P in
theorem expLen_ok {t : State} (x : Xs s t) :
    WP isa expLen t fun u => Only [.a1] t u ∧ u.gpr .a1 = if anyL s = 0 then stackArg s 0 else 0 := by
  refine WP.ite _ (eval_zero _ _) (fun hz => wp_mov fun u o e => wp_nil ⟨o, ?_⟩)
    (fun hz => wp_li (imm := 0) (by decide) fun u o e => wp_nil ⟨o, ?_⟩)
  · rw [ifp (by rw [← x.s7]; simpa using hz), e, x.s6]
  · rw [ifn (by rw [← x.s7]; simpa using hz), e]; rfl

theorem cm_reE {m : Mem} (hf : Frame [kR s, scR s] s.mem m) : cm (reE s m) = cm s := by
  rw [cm, cm, reE_lo P hf]; simp only [smear, reE_n0 P hf]

theorem lay_reE {H : Hash} (hH : HashOK H) (hHl : Hs.len = H.D) {m : Mem} (hf : Frame [kR s, scR s] s.mem m)
    (h0 : s.mem (s.gpr .a0) ≠ 0) (hem : Hs.len + 2 ≤ kk s - loN s) :
    Lay Hs.len (reE s m) (loN s) (kk s - loN s - Hs.len - 1) (cB s) where
  F := reE_fits P hf
  hlo := by rw [reE_lo P hf, lo_eq h0]; rfl
  hdb := by
    show s.gpr .a1 - lo (reE s m) - BitVec.ofNat 64 (Hs.len + 1) = _
    have e : (s.gpr .a1).toNat = kk s := rfl
    have := P.k2
    rw [reE_lo P hf, lo_eq h0, show (if (s.mem (s.gpr .a0)).toNat = 1 then 1 else 0) = loN s from rfl,
      ← ofNat_toNat (s.gpr .a1), Offset.ofNat_sub_ofNat (by omega), Offset.ofNat_sub_ofNat (by omega),
      show (s.gpr .a1).toNat - loN s - (Hs.len + 1) = kk s - loN s - Hs.len - 1 by omega]
  hc := by rw [cm_reE P hf, cm_eq h0]; rfl
  l1 := by unfold loN; split <;> omega
  d1 := by omega
  hk := by show _ = kk s; omega
  k2 := P.k2
  D0 := by rw [hHl]; exact hH.hD0
  D64 := by rw [hHl]; exact hH.hD64
  dr := by show dR Hs.len s ∈ s.rd; rw [P.hrd]; simp
  dsc := by
    rw [show SC Sp (reE s m) = SC Sp s by simp only [SC, reE_Sp P hf]]; exact P.ds.sub_right (sc_sub P)
  dk := P.kd
  wd := P.wd
  al := by show (Sp (reE s m)).toNat % 8 = 0; rw [reE_Sp P hf]; exact P.al2

/-- The registers the checks keep. -/
abbrev ckR : List Reg := [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .t1]

theorem Entered.only {t t' : State} {rs : List Reg} (E : Entered Hs.len s t) (o : Only rs t t')
    (hrs : ∀ r ∈ rs, r ∉ ckR := by decide) : Entered Hs.len s t' := by
  have g : ∀ r ∈ ckR, t'.gpr r = t.gpr r := fun r hr => o.gpr r fun h => hrs r h hr
  have hf : ∀ r ∈ fixed, r ∈ ckR := by decide
  exact ⟨E.base.only P.fits o fun r h h' => hrs r h (hf r h'), E.xs.of fun r hr => g r (by revert r; decide),
    (g _ (by decide)).trans E.s8, (g _ (by decide)).trans E.s9, (g _ (by decide)).trans E.s10,
    (g _ (by decide)).trans E.t1⟩

omit P in
theorem Entered.before {t : State} (E : Entered Hs.len s t) : Before Hs.len s t :=
  ⟨E.base, E.xs, E.s8, E.s9, E.s10⟩

omit P in
theorem n0_eq {t : State} (E : Entered Hs.len s t) (hz : (t.gpr .t1 == 0) = true) : s.mem (s.gpr .a0) = 0 := by
  have : n0 s = 0#64 := by rw [← E.t1]; simpa using hz
  exact (setWidth64_eq_zero _).mp this

omit P in
theorem n0_ne {t : State} (E : Entered Hs.len s t) (hz : (t.gpr .t1 == 0) = false) : s.mem (s.gpr .a0) ≠ 0 :=
  fun h => by rw [E.t1, n0, h] at hz; simp at hz

theorem lo_N (h0 : s.mem (s.gpr .a0) ≠ 0) : s.gpr .a1 - lo s = BitVec.ofNat 64 (kk s - loN s) := by
  have hk1 : 64 ≤ kk s := P.k1
  have ek : (s.gpr .a1).toNat = kk s := rfl
  have hl1 : loN s ≤ 1 := by unfold loN; split <;> omega
  rw [lo_eq h0, show (if (s.mem (s.gpr .a0)).toNat = 1 then 1 else 0) = loN s from rfl, ← ofNat_toNat (s.gpr .a1),
    Offset.ofNat_sub_ofNat (by omega)]

/-- `chkEm`: whether `emLen < hLen + 2`. -/
theorem chkEm_ok {H : Hash} (hHl : Hs.len = H.D) (hD64 : Hs.len ≤ 64) {t : State} (E : Entered Hs.len s t)
    (h0 : s.mem (s.gpr .a0) ≠ 0) :
    WP isa (.block (chkEm H)) t fun t' => Entered Hs.len s t' ∧
      (t'.gpr .a0 != 0) = decide (kk s - loN s < Hs.len + 2) := by
  have hk2 : kk s ≤ 1024 := P.k2
  refine wp_sub fun t₁ o₁ e₁ => wp_subi (imm := H.D + 2) (h := by omega) fun t₂ o₂ e₂ =>
    wp_srl fun t₃ o₃ e₃ => wp_nil ?_
  have k₃ : Only [.a0] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  refine ⟨E.only P k₃, ?_⟩
  rw [e₃, e₂, e₁, E.base.pk, E.base.plo, lo_N P h0, ← hHl]
  exact ne_zero_ltBit (by omega) (by omega)

/-- `chkSalt`: whether the salt length expected is more than `emLen - hLen - 2`. -/
theorem chkSalt_ok {H : Hash} (hHl : Hs.len = H.D) (hD64 : Hs.len ≤ 64) {t : State} (E : Entered Hs.len s t)
    (h0 : s.mem (s.gpr .a0) ≠ 0) (hem : Hs.len + 2 ≤ kk s - loN s)
    (h1 : t.gpr .a1 = if anyL s = 0 then stackArg s 0 else 0) :
    WP isa (.block (chkSalt H)) t fun t' => Entered Hs.len s t' ∧
      (t'.gpr .a0 != 0) = decide (kk s - loN s - (Hs.len + 2) < (if anyL s = 0 then stackArg s 0 else 0).toNat) := by
  have hk2 : kk s ≤ 1024 := P.k2
  refine wp_sub fun t₅ o₅ e₅ => wp_subi (imm := H.D + 2) (h := by omega) fun t₆ o₆ e₆ => wp_sub fun t₇ o₇ e₇ =>
    wp_srl fun t₈ o₈ e₈ => wp_srl fun t₉ o₉ e₉ => wp_or fun t₁₀ o₁₀ e₁₀ => wp_nil ?_
  have k₁₀ : Only [.a0, .a2] t t₁₀ := (o₅.trans (o₆.trans (o₇.trans (o₈.trans (o₉.trans o₁₀))))).mono
  refine ⟨E.only P k₁₀, ?_⟩
  rw [e₁₀, o₉.get .a0, e₉, e₈, o₈.get .a1, e₇, o₇.get .a1, e₆, o₆.get .a1, e₅, o₅.get .a1, E.base.pk, E.base.plo,
    lo_N P h0, h1, ← hHl, Offset.ofNat_sub_ofNat hem, BitVec.or_comm]
  have := msgBit (x := kk s - loN s - (Hs.len + 2)) (y := (if anyL s = 0 then stackArg s 0 else 0).toNat)
    (by omega) (BitVec.isLt _)
  rwa [ofNat_toNat] at this

section
variable {H : Hash} (hH : HashOK H) (hF : H.F ≤ 208) {M : MdL H hH} {dg : String} {f : MdFns} {p : Addr}
  (T : TabM M dg f 6 Sp s p) (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D)
  (hHv : Proof.Mgf1.Valid Hs) {G : Hash} (hG : HashOK G) (hGF : G.F ≤ 208) {g : Fns} {pg : Addr}
  (TG : TabS G g 7 Sp s pg) (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D)
  (hGv : Proof.Mgf1.Valid Gs)
include hH hF T hHh hHl hHv hG hGF TG hGh hGl hGv

theorem main_done {t : State} (B : Before Hs.len s t) (sy : t.syms = s.syms) (h0 : s.mem (s.gpr .a0) ≠ 0)
    (hem : Hs.len + 2 ≤ kk s - loN s) (hfit : anyL s = 0 → (stackArg s 0).toNat + 1 ≤ kk s - loN s - Hs.len - 1) :
    WP isa (verifyMain H M.be f g) t (Done Hs Gs s) := by
  refine WP.seq (WP.mono_syms (pubArgs_ok P B) fun t₁ a₁ y₁ =>
    WP.seq (WP.mono_syms (call_ok P a₁) fun t₂ c₂ y₂ => ?_))
  have L := lay_reE P hH hHl c₂.mem h0 hem
  have hS := reE_Sp P c₂.mem
  have hSC : SC Sp (reE s t₂.mem) = SC Sp s := by simp only [SC, hS]
  have hmh : mh Hs.len (reE s t₂.mem) = mh Hs.len s :=
    VG.Proof.RsaOaep.RISCV64.bytes_entry c₂.mem P.kd P.ds.symm (by have := hH.hD64; omega)
  have hany : anyL (reE s t₂.mem) = anyL s := by unfold anyL; rw [reE_args P c₂.mem 1 (by decide)]
  have e6 : p = stackArg s 6 := T.arg.symm
  have e7 : pg = stackArg s 7 := TG.arg.symm
  have T' : TabM M dg f 6 Sp (reE s t₂.mem) p := T.transfer rfl rfl rfl hSC c₂.mem (arg_dis P (by decide))
    (by rw [e6]; exact tabH_dis P)
  have TG' : TabS G g 7 Sp (reE s t₂.mem) pg := TG.transfer rfl rfl rfl hSC c₂.mem (arg_dis P (by decide))
    (by rw [e7]; exact tabG_dis P)
  refine WP.mono (post_ok L hH hF T' hG hGF TG' hHl.symm hHh hGh hGl hGv c₂.base (y₂.trans (y₁.trans sy)) c₂.xs
    (by rw [hany, reE_args P c₂.mem 0 (by decide)]; exact hfit))
    fun t' ⟨b', r'⟩ => ⟨⟨b'.sv.sp, b'.sv.wr, b'.sv.sv⟩, fun hc => ?_⟩
  rw [r', hS, hmh, hany, reE_gpr, reE_args P c₂.mem 0 (by decide)]
  have e := res_vOut hGv hHv P h0 (c₂.em hc) hem hfit
  by_cases hv : vOut Hs Gs s = true
  · rw [ifp (e.mpr hv), ifp hv]; rfl
  · rw [ifn (fun h => hv (e.mp h)), ifn hv]; rfl

theorem checks_done {t : State} (E : Entered Hs.len s t) (sy : t.syms = s.syms) :
    WP isa (checks H M.be f g) t (Done Hs Gs s) := by
  have hk1 : 64 ≤ kk s := P.k1
  have hD64 : Hs.len ≤ 64 := hHl ▸ hH.hD64
  refine WP.ite _ (eval_zero _ _) (fun hz => fail_ok P E.base (zero_false Hs Gs (by omega) (n0_eq E hz)))
    (fun hz => ?_)
  have h0 := n0_ne E hz
  -- `emLen < hLen + 2`.
  refine WP.seq (WP.mono_syms (chkEm_ok P hHl hD64 E h0) fun t₃ ⟨E₃, r3⟩ y₃ => ?_)
  refine WP.ite _ (eval_nonzero _ _) (fun hc => fail_ok P E₃.base (short_false Hs Gs (by omega) h0 ?_))
    (fun hc => ?_)
  · rw [r3] at hc; simp at hc; omega
  have hem : Hs.len + 2 ≤ kk s - loN s := by rw [r3] at hc; simp at hc; omega
  -- The salt length expected.
  refine WP.seq (WP.mono_syms (expLen_ok E₃.xs) fun t₄ ⟨o₄, e₄⟩ y₄ => ?_)
  refine WP.seq (WP.mono_syms (chkSalt_ok P hHl hD64 (E₃.only P o₄) h0 hem e₄) fun t₁₀ ⟨E₁₀, r3'⟩ y₁₀ => ?_)
  refine WP.ite _ (eval_nonzero _ _) (fun hc => fail_ok P E₁₀.base (short_false Hs Gs (by omega) h0 ?_))
    (fun hc => ?_)
  · rw [r3'] at hc
    rw [sLen_eq]
    by_cases ha : anyL s = 0
    · rw [ifp ha] at hc ⊢; simp only [Option.getD_some]; simp at hc; omega
    · rw [ifn ha] at hc; simp at hc
  have hfit : anyL s = 0 → (stackArg s 0).toNat + 1 ≤ kk s - loN s - Hs.len - 1 := fun ha => by
    rw [r3', ifp ha] at hc; simp at hc; omega
  exact main_done P hH hF T hHh hHl hHv hG hGF TG hGh hGl hGv E₁₀.before (y₁₀.trans (y₄.trans (y₃.trans sy))) h0
    hem hfit

/-- The code for the hash function `H`, in its frame. -/
theorem code_ok : WP isa (verifyFor H M.be f g) s (Post Hs Gs s) := by
  refine WP.alloc (by decide) (by have := P.sp1; unfold frameBytes; unfold stackBytes at this; omega) ?_
  refine WP.seq (WP.mono_syms (entry_ok P hHl.symm (hHl ▸ hH.hD64)) fun t E y => WP.seq (WP.mono
    (checks_done P hH hF T hHh hHl hHv hG hGF TG hGh hGl hGv E (y.trans rfl)) fun t' ⟨sv, res⟩ =>
      WP.mono (restore_ok sv (fb_al8 P)) fun w ⟨habi, h3, _⟩ => ⟨habi, fun hc => ?_⟩))
  show w.gpr .a0 = _
  rw [h3]
  exact res hc

end

end

end VG.Proof.RsaPss.RISCV64
