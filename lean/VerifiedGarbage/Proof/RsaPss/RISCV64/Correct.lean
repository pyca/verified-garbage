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
open VG.Proof.RsaPss (lz vDb vH EncOk)
open VG.Proof.RsaPss (xorBytes_getD clearTop_getD zeros_getD eq_range_map)
open VG.Proof.RsaOaep (mixV srcB)
open VG.Proof.Mgf1 (ifp ifn Valid mgf1_length xorBytes_length)
open VG.Spec.RsaPss (zeros clearTop)

section
variable {Gs : Spec.Mgf1.Hash} {V : Nat → Byte} {em : List Byte} {lN E : Nat} {c : Byte} {z : Nat}

theorem vH_getD (hfE : Gs.len + 2 ≤ E) (hV : ∀ i < E, V (lN + i) = em.getD i 0) {i : Nat} (hi : i < Gs.len) :
    (vH Gs em (E - Gs.len - 1)).getD i 0 = V (lN + (E - Gs.len - 1) + i) := by
  simp only [vH, List.getD_eq_getElem?_getD, List.getElem?_take, ifp hi, List.getElem?_drop]
  rw [← List.getD_eq_getElem?_getD, Nat.add_assoc, hV _ (by omega)]

theorem vH_length (hE : em.length = E) (hfE : Gs.len + 2 ≤ E) : (vH Gs em (E - Gs.len - 1)).length = Gs.len := by
  simp only [vH, List.length_take, List.length_drop, hE]; omega

theorem srcB_vH (hE : em.length = E) (hfE : Gs.len + 2 ≤ E) (hV : ∀ i < E, V (lN + i) = em.getD i 0) :
    srcB (v1 V lN c (lN + E)) (lN + (E - Gs.len - 1)) Gs.len = vH Gs em (E - Gs.len - 1) := by
  refine (eq_range_map (vH_length hE hfE) fun i hi => ?_).symm
  rw [vH_getD hfE hV hi, v1, ifn (by omega)]

theorem wR_eq (hGv : Valid Gs) (hc : c = (0xFF : Byte) >>> z) (hE : em.length = E) (hfE : Gs.len + 2 ≤ E)
    (hV : ∀ i < E, V (lN + i) = em.getD i 0) {j : Nat} (hj : j < E - Gs.len - 1) :
    wR Gs V Gs.len lN (E - Gs.len - 1) c (lN + E) j = (vDb Gs em (E - Gs.len - 1) z).getD j 0 := by
  have hmk := mgf1_length hGv (vH Gs em (E - Gs.len - 1)) (E - Gs.len - 1)
  have ht : ∀ {i}, i < E - Gs.len - 1 → (em.take (E - Gs.len - 1)).getD i 0 = em.getD i 0 := fun hi => by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, ifp hi]
  let mk := Spec.Mgf1.mgf1 Gs (vH Gs em (E - Gs.len - 1)) (E - Gs.len - 1)
  have hm : mixV (v1 V lN c (lN + E)) (Spec.Mgf1.mgf1 Gs (srcB (v1 V lN c (lN + E)) (lN + (E - Gs.len - 1)) Gs.len)
      (E - Gs.len - 1)) lN (E - Gs.len - 1) (lN + j) = em.getD j 0 ^^^ mk.getD j 0 := by
    rw [srcB_vH hE hfE hV, mixV, ifp ⟨by omega, by omega⟩, v1, ifn (by omega), hV _ (by omega),
      Nat.add_sub_cancel_left]
  have hx : (Spec.Mgf1.xorBytes (em.take (E - Gs.len - 1)) mk).getD j 0 = em.getD j 0 ^^^ mk.getD j 0 := by
    rw [xorBytes_getD (by rw [List.length_take, hE]; omega) (by simp only [mk]; omega), ht hj]
  show (if lN + j = lN then _ &&& c else _) = _
  rw [vDb, clearTop_getD]
  by_cases e : j = 0
  · subst e
    rw [ifp (Nat.add_zero lN), ifp rfl, hm, ← hx, hc]
  · rw [ifn (by omega), ifn e, hm, ← hx]

end

section
variable {Gs : Spec.Mgf1.Hash} (hGv : Valid Gs) {V : Nat → Byte} {em mh : List Byte} {lN E : Nat} {c : Byte}
  {z : Nat} (hc : c = (0xFF : Byte) >>> z) (hE : em.length = E) (hfE : Gs.len + 2 ≤ E)
  (hV : ∀ i < E, V (lN + i) = em.getD i 0)

include hGv hc hE hfE hV in
theorem db_eq : vDb Gs em (E - Gs.len - 1) z = (List.range (E - Gs.len - 1)).map (wR Gs V Gs.len lN (E - Gs.len - 1) c (lN + E)) := by
  refine eq_range_map (by simp [vDb, VG.Proof.RsaPss.clearTop_length, xorBytes_length, mgf1_length hGv, hE]; omega)
    fun j hj => (wR_eq hGv hc hE hfE hV hj).symm

include hGv hc hE hfE hV in
theorem lzr_eq : lzr (wR Gs V Gs.len lN (E - Gs.len - 1) c (lN + E)) (E - Gs.len - 1) = lz (vDb Gs em (E - Gs.len - 1) z) := by
  rw [db_eq hGv hc hE hfE hV]; rfl

include hGv hc hE hfE hV in
/-- `M'` is the specification's once the delimiter is found and the salt
length is the expected one. -/
theorem mR_eq (hmh : mh.length = Gs.len) {any saltLen : BitVec 64}
    (hlz : lz (vDb Gs em (E - Gs.len - 1) z) < E - Gs.len - 1)
    (hsl : any = 0 → saltLen.toNat = E - Gs.len - 1 - 1 - lz (vDb Gs em (E - Gs.len - 1) z)) :
    mR Gs V Gs.len lN (E - Gs.len - 1) c (lN + E) mh any saltLen =
      zeros 8 ++ mh ++ (vDb Gs em (E - Gs.len - 1) z).drop (lz (vDb Gs em (E - Gs.len - 1) z) + 1) := by
  have hl := lzr_eq hGv hc hE hfE hV
  generalize hdb : vDb Gs em (E - Gs.len - 1) z = db at hl hlz hsl
  have hdl : db.length = E - Gs.len - 1 := by
    rw [← hdb]; simp [vDb, VG.Proof.RsaPss.clearTop_length, xorBytes_length, mgf1_length hGv, hE]; omega
  have hp : posR Gs V Gs.len lN (E - Gs.len - 1) c (lN + E) = lz db := by rw [posR, hl, ifp hlz]
  have hw : ∀ j < E - Gs.len - 1, dbV Gs (v1 V lN c (lN + E)) lN (E - Gs.len - 1) Gs.len c (lN + j) = db.getD j 0 :=
    fun j hj => by rw [← hdb, ← wR_eq hGv hc hE hfE hV hj]; rfl
  have hd : ∀ j < E - Gs.len - 1 - lz db - 1, (db.drop (lz db + 1)).getD j 0 =
      dbV Gs (v1 V lN c (lN + E)) lN (E - Gs.len - 1) Gs.len c (lN + (j + (lz db + 1))) := fun j hj => by
    rw [hw _ (by omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
    congr 2; omega
  have hdd : (db.drop (lz db + 1)).length = E - Gs.len - 1 - lz db - 1 := by rw [List.length_drop, hdl]; omega
  rw [mR]
  split
  · rename_i h0
    have h1 := hsl h0
    rw [mFix, h1, show E - Gs.len - 1 - 1 - lz db = E - Gs.len - 1 - lz db - 1 by omega]
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
variable {Gs : Spec.Mgf1.Hash} (hGv : Valid Gs) {V : Nat → Byte} {em mh : List Byte} {lN E : Nat} {c : Byte}
  {z : Nat} (hc : c = (0xFF : Byte) >>> z) (hE : em.length = E) (hfE : Gs.len + 2 ≤ E)
  (hV : ∀ i < E, V (lN + i) = em.getD i 0) (hmh : mh.length = Gs.len)
include hGv hc hE hfE hV hmh

theorem res_iff {any saltLen : BitVec 64} {sLen : Option Nat} (hs : sLen = if any = 0 then some saltLen.toNat else none)
    (hE64 : E < 2 ^ 64) :
    Res Gs V Gs.len lN (E - Gs.len - 1) c (lN + E) mh any saltLen ↔
      (lN = 1 → V 0 = 0) ∧ EncOk Gs mh em E z sLen := by
  have hl := lzr_eq hGv hc hE hfE hV
  have hw : ∀ j < E - Gs.len - 1, wR Gs V Gs.len lN (E - Gs.len - 1) c (lN + E) j =
      (vDb Gs em (E - Gs.len - 1) z).getD j 0 := fun j hj => wR_eq hGv hc hE hfE hV hj
  have hk1 : lN + E - 1 = lN + (E - 1) := by omega
  have hV0 : V lN = em.getD 0 0 := hV 0 (by omega)
  have hVk : V (lN + E - 1) = em.getD (E - 1) 0 := by rw [hk1]; exact hV _ (by omega)
  have hnot : ~~~c = ~~~((0xFF : Byte) >>> z) := by rw [hc]
  -- The hash compared, as lists.
  have hcmp : ∀ M : List Byte, (∀ i < Gs.len, V (lN + (E - Gs.len - 1) + i) = (Gs.hash M).getD i 0) ↔
      Gs.hash M = vH Gs em (E - Gs.len - 1) := fun M => by
    constructor
    · intro h
      refine List.ext_getElem (by rw [hGv.2, vH_length hE hfE]) fun i h₁ h₂ => ?_
      have e := h i (by rw [hGv.2] at h₁; exact h₁)
      rw [← vH_getD hfE hV (by rw [hGv.2] at h₁; exact h₁), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem h₁, List.getElem?_eq_getElem h₂] at e
      exact e.symm
    · intro h i hi; rw [h, vH_getD hfE hV hi]
  have hval : valR Gs V Gs.len lN (E - Gs.len - 1) c (lN + E) = 1 ↔
      lz (vDb Gs em (E - Gs.len - 1) z) < E - Gs.len - 1 ∧
        (vDb Gs em (E - Gs.len - 1) z).getD (lz (vDb Gs em (E - Gs.len - 1) z)) 0 = 1 := by
    unfold valR; rw [hl]
    by_cases h : lz (vDb Gs em (E - Gs.len - 1) z) < E - Gs.len - 1
    · rw [ifp h, hw _ h]; simp [h]
    · rw [ifn h]; simp [h]
  have hsl : lz (vDb Gs em (E - Gs.len - 1) z) < E - Gs.len - 1 →
      slR Gs V Gs.len lN (E - Gs.len - 1) c (lN + E) = E - Gs.len - 1 - 1 - lz (vDb Gs em (E - Gs.len - 1) z) :=
    fun h => by unfold slR posR; rw [hl, ifp h]; omega
  have hsv : (sLen = none ∨ sLen = some (E - Gs.len - 1 - 1 - lz (vDb Gs em (E - Gs.len - 1) z))) ↔
      (any = 0 → saltLen.toNat = E - Gs.len - 1 - 1 - lz (vDb Gs em (E - Gs.len - 1) z)) := by
    rw [hs]; split
    · rename_i h0; simp [h0]
    · rename_i h0; exact ⟨fun _ e => absurd e h0, fun _ => Or.inl rfl⟩
  have hany : lz (vDb Gs em (E - Gs.len - 1) z) < E - Gs.len - 1 →
      ((if any = 0 then BitVec.ofNat 64 (slR Gs V Gs.len lN (E - Gs.len - 1) c (lN + E)) ^^^ saltLen else 0#64) =
        0#64 ↔ (any = 0 → saltLen.toNat = E - Gs.len - 1 - 1 - lz (vDb Gs em (E - Gs.len - 1) z))) := fun h => by
    rw [hsl h]
    split
    · rename_i h0
      rw [BitVec.xor_eq_zero_iff]
      constructor
      · intro e _; rw [← e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      · intro e; rw [← e h0, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rename_i h0; exact ⟨fun _ e => absurd e h0, fun _ => rfl⟩
  unfold Res accR accW EncOk
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
  stackBytes)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only wp_li wp_sub wp_subi wp_srl wp_or wp_mov wp_nil eval_zero eval_nonzero)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)
open VG.Proof.Mgf1 (ifp ifn)

/-- What the function returns, from its entry state. -/
def vOut (Gs : Spec.Mgf1.Hash) (s : State) : Bool :=
  Spec.RsaPss.verify Gs Gs (Spec.Rsa.bytesAt s.mem (s.gpr .a0) (kk s))
    (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) (mh Gs.len s) (Spec.Rsa.bytesAt s.mem (s.gpr .a5) (kk s))
    (Spec.RsaPss.expectedSaltLen (s.gpr .a7) ((stackArg s 0).setWidth 32))

/-- The result, from the entry state `s`. -/
def Post (Gs : Spec.Mgf1.Hash) (s s' : State) : Prop :=
  abiPreserved s s' ∧ (PreOk s → s'.gpr .a0 = if vOut Gs s then 1 else 0)

/-- Before the restores. -/
def Done (Gs : Spec.Mgf1.Hash) (s t : State) : Prop :=
  Saves s t ∧ (PreOk s → t.gpr .a0 = if vOut Gs s then 1 else 0)

/-- `lo` and `c`, from the modulus' first byte. -/
def loN (s : State) : Nat := if (s.mem (s.gpr .a0)).toNat = 1 then 1 else 0
def cB (s : State) : Byte :=
  if (s.mem (s.gpr .a0)).toNat = 1 then 0xFF else BitVec.ofNat 8 (2 ^ Nat.log2 (s.mem (s.gpr .a0)).toNat - 1)

theorem anyL_eq (s : State) : anyL s = 0 ↔ (stackArg s 0).setWidth 32 = 0 := by
  have e : (anyL s).toNat = ((stackArg s 0).setWidth 32).toNat := by
    have := (stackArg s 0).isLt
    simp only [anyL, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq,
      Nat.shiftRight_eq_div_pow]
    omega
  constructor <;> intro h <;> apply BitVec.eq_of_toNat_eq
  · rw [← e, h]; rfl
  · rw [e, h]; rfl

theorem sLen_eq (s : State) : Spec.RsaPss.expectedSaltLen (s.gpr .a7) ((stackArg s 0).setWidth 32) =
    if anyL s = 0 then some (s.gpr .a7).toNat else none := by
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
    (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .a5) (kk s)) with
  | none => simp
  | some y => rw [Option.getD_some, Proof.RsaPss.publicOpChecked_length' hp, bytesAt_length]

/-! ## The specification's cases -/

section
variable (Gs : Spec.Mgf1.Hash) {s : State} (hk : 1 ≤ kk s)
include hk

theorem nB_cons : ∃ rest : List Byte, Spec.Rsa.bytesAt s.mem (s.gpr .a0) (kk s) = s.mem (s.gpr .a0) :: rest ∧
    rest.length = kk s - 1 := by
  obtain ⟨rest, h, hl⟩ := bytesAt_cons s.mem (s.gpr .a0) (kk s - 1)
  rw [show kk s - 1 + 1 = kk s by omega] at h
  exact ⟨rest, h, hl⟩

theorem zero_false (h0 : s.mem (s.gpr .a0) = 0) : vOut Gs s = false := by
  obtain ⟨rest, hn, -⟩ := nB_cons hk
  rw [vOut, hn, h0]
  exact Proof.RsaPss.verify_zero Gs _ _ _ _ _

theorem emLen_eq (h0 : s.mem (s.gpr .a0) ≠ 0) {rest : List Byte} (hr : rest.length = kk s - 1) :
    Spec.RsaPss.emLength (Spec.RsaPss.bitLength (Spec.Rsa.os2ip (s.mem (s.gpr .a0) :: rest)) - 1) =
      kk s - loN s := by
  rw [Proof.RsaPss.emLength_eq rest h0, hr, loN]; split <;> omega

theorem short_false (h0 : s.mem (s.gpr .a0) ≠ 0)
    (h : kk s - loN s < Gs.len + (Spec.RsaPss.expectedSaltLen (s.gpr .a7) ((stackArg s 0).setWidth 32)).getD 0 + 2) :
    vOut Gs s = false := by
  obtain ⟨rest, hn, hr⟩ := nB_cons hk
  rw [vOut, hn]
  exact Proof.RsaPss.verify_short Gs _ _ _ (by rw [emLen_eq hk h0 hr]; exact h)

end

/-- `Res` is verification, for `EM` in place. -/
theorem res_vOut {Gs : Spec.Mgf1.Hash} (hGv : Proof.Mgf1.Valid Gs) {s : State} (P : PreP Gs.len s)
    (h0 : s.mem (s.gpr .a0) ≠ 0) {m : Mem} (hm : Spec.Rsa.bytesAt m (off (Sp s) 0) (kk s) = emOf s)
    (hem : Gs.len + 2 ≤ kk s - loN s)
    (hfit : anyL s = 0 → (s.gpr .a7).toNat + 1 ≤ kk s - loN s - Gs.len - 1) :
    Res Gs (view m (Sp s)) Gs.len (loN s) (kk s - loN s - Gs.len - 1) (cB s) (kk s) (mh Gs.len s) (anyL s)
      (s.gpr .a7) ↔ vOut Gs s = true := by
  have hk1 : 64 ≤ kk s := P.k1; have hk2 : kk s ≤ 1024 := P.k2
  have hl1 : loN s ≤ 1 := by unfold loN; split <;> omega
  obtain ⟨rest, hn, hr⟩ := nB_cons (show 1 ≤ kk s by omega)
  have hE := emLen_eq (by omega) h0 hr
  have hM := Proof.RsaPss.mask_eq rest h0
  have hx : (Spec.Rsa.publicOpChecked (s.mem (s.gpr .a0) :: rest) (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .a5) (kk s))).getD (Spec.RsaPss.zeros (s.mem (s.gpr .a0) :: rest).length) =
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
  rw [show kk s - loN s - Gs.len - 1 = E - Gs.len - 1 by omega, show kk s = loN s + E by omega,
    res_iff (E := E) hGv hc hEl (by omega) hV (bytesAt_length _ _ _) (sLen_eq s) (by omega), vOut, hn,
    Proof.RsaPss.verify_bytes Gs hGv (bytesAt_length _ _ _) (by rw [bytesAt_length, List.length_cons, hr]; omega)
      hB hEg (by rw [List.length_cons, hr]; omega) hl1 ?_, hx, hV0]
  rw [sLen_eq]; split
  · rename_i h; have := hfit h; simp only [Option.getD_some]; omega
  · simp only [Option.getD_none]; omega

/-! ## The code -/

section
variable {Gs : Spec.Mgf1.Hash} {s : State} (P : PreP Gs.len s)
include P

theorem fail_ok {t : State} (h : Base Sp (vP Gs.len) s t) (hv : vOut Gs s = false) :
    WP isa Impl.RsaPss.RISCV64.fail t (Done Gs s) :=
  wp_li (imm := 0) (by decide) fun t' o e => wp_nil ⟨(h.only P.fits o).sv, fun _ => by rw [e, hv]; rfl⟩

omit P in
theorem expLen_ok {t : State} (x : Xs s t) :
    WP isa expLen t fun u => Only [.a1] t u ∧ u.gpr .a1 = if anyL s = 0 then s.gpr .a7 else 0 := by
  refine WP.ite _ (eval_zero _ _) (fun hz => wp_mov fun u o e => wp_nil ⟨o, ?_⟩)
    (fun hz => wp_li (imm := 0) (by decide) fun u o e => wp_nil ⟨o, ?_⟩)
  · rw [ifp (by rw [← x.s7]; simpa using hz), e, x.s6]
  · rw [ifn (by rw [← x.s7]; simpa using hz), e]; rfl

theorem cm_reE {m : Mem} (hf : Frame [kR s, scR s] s.mem m) : cm (reE s m) = cm s := by
  rw [cm, cm, reE_lo P hf]; simp only [smear, reE_n0 P hf]

theorem lay_reE {H : Hash} (hH : HashOK H) (hGl : Gs.len = H.D) {m : Mem} (hf : Frame [kR s, scR s] s.mem m)
    (h0 : s.mem (s.gpr .a0) ≠ 0) (hem : Gs.len + 2 ≤ kk s - loN s) :
    Lay Gs.len (reE s m) (loN s) (kk s - loN s - Gs.len - 1) (cB s) where
  F := reE_fits P hf
  hlo := by rw [reE_lo P hf, lo_eq h0]; rfl
  hdb := by
    show s.gpr .a1 - lo (reE s m) - BitVec.ofNat 64 (Gs.len + 1) = _
    have e : (s.gpr .a1).toNat = kk s := rfl
    have := P.k2
    rw [reE_lo P hf, lo_eq h0, show (if (s.mem (s.gpr .a0)).toNat = 1 then 1 else 0) = loN s from rfl,
      ← ofNat_toNat (s.gpr .a1), Offset.ofNat_sub_ofNat (by omega), Offset.ofNat_sub_ofNat (by omega),
      show (s.gpr .a1).toNat - loN s - (Gs.len + 1) = kk s - loN s - Gs.len - 1 by omega]
  hc := by rw [cm_reE P hf, cm_eq h0]; rfl
  l1 := by unfold loN; split <;> omega
  d1 := by omega
  hk := by show _ = kk s; omega
  k2 := P.k2
  D0 := by rw [hGl]; exact hH.hD0
  D64 := by rw [hGl]; exact hH.hD64
  dr := by show dR Gs.len s ∈ s.rd; rw [P.hrd]; simp
  dsc := by
    rw [show SC Sp (reE s m) = SC Sp s by simp only [SC, reE_Sp P hf]]; exact P.ds.sub_right (sc_sub P)
  dk := P.kd
  wd := P.wd
  al := by show (Sp (reE s m)).toNat % 8 = 0; rw [reE_Sp P hf]; exact P.al1

/-- The registers the checks keep. -/
abbrev ckR : List Reg := [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .t1]

theorem Entered.only {t t' : State} {rs : List Reg} (E : Entered Gs.len s t) (o : Only rs t t')
    (hrs : ∀ r ∈ rs, r ∉ ckR := by decide) : Entered Gs.len s t' := by
  have g : ∀ r ∈ ckR, t'.gpr r = t.gpr r := fun r hr => o.gpr r fun h => hrs r h hr
  have hf : ∀ r ∈ fixed, r ∈ ckR := by decide
  exact ⟨E.base.only P.fits o fun r h h' => hrs r h (hf r h'), E.xs.of fun r hr => g r (by revert r; decide),
    (g _ (by decide)).trans E.s8, (g _ (by decide)).trans E.s9, (g _ (by decide)).trans E.s10,
    (g _ (by decide)).trans E.t1⟩

omit P in
theorem Entered.before {t : State} (E : Entered Gs.len s t) : Before Gs.len s t :=
  ⟨E.base, E.xs, E.s8, E.s9, E.s10⟩

omit P in
theorem n0_eq {t : State} (E : Entered Gs.len s t) (hz : (t.gpr .t1 == 0) = true) : s.mem (s.gpr .a0) = 0 := by
  have : n0 s = 0#64 := by rw [← E.t1]; simpa using hz
  exact (setWidth64_eq_zero _).mp this

omit P in
theorem n0_ne {t : State} (E : Entered Gs.len s t) (hz : (t.gpr .t1 == 0) = false) : s.mem (s.gpr .a0) ≠ 0 :=
  fun h => by rw [E.t1, n0, h] at hz; simp at hz

theorem lo_N (h0 : s.mem (s.gpr .a0) ≠ 0) : s.gpr .a1 - lo s = BitVec.ofNat 64 (kk s - loN s) := by
  have hk1 : 64 ≤ kk s := P.k1
  have ek : (s.gpr .a1).toNat = kk s := rfl
  have hl1 : loN s ≤ 1 := by unfold loN; split <;> omega
  rw [lo_eq h0, show (if (s.mem (s.gpr .a0)).toNat = 1 then 1 else 0) = loN s from rfl, ← ofNat_toNat (s.gpr .a1),
    Offset.ofNat_sub_ofNat (by omega)]

/-- `chkEm`: whether `emLen < hLen + 2`. -/
theorem chkEm_ok {H : Hash} (hGl : Gs.len = H.D) (hD64 : Gs.len ≤ 64) {t : State} (E : Entered Gs.len s t)
    (h0 : s.mem (s.gpr .a0) ≠ 0) :
    WP isa (.block (chkEm H)) t fun t' => Entered Gs.len s t' ∧
      (t'.gpr .a0 != 0) = decide (kk s - loN s < Gs.len + 2) := by
  have hk2 : kk s ≤ 1024 := P.k2
  refine wp_sub fun t₁ o₁ e₁ => wp_subi (imm := H.D + 2) (h := by omega) fun t₂ o₂ e₂ =>
    wp_srl fun t₃ o₃ e₃ => wp_nil ?_
  have k₃ : Only [.a0] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  refine ⟨E.only P k₃, ?_⟩
  rw [e₃, e₂, e₁, E.base.pk, E.base.plo, lo_N P h0, ← hGl]
  exact ne_zero_ltBit (by omega) (by omega)

/-- `chkSalt`: whether the salt length expected is more than `emLen - hLen - 2`. -/
theorem chkSalt_ok {H : Hash} (hGl : Gs.len = H.D) (hD64 : Gs.len ≤ 64) {t : State} (E : Entered Gs.len s t)
    (h0 : s.mem (s.gpr .a0) ≠ 0) (hem : Gs.len + 2 ≤ kk s - loN s)
    (h1 : t.gpr .a1 = if anyL s = 0 then s.gpr .a7 else 0) :
    WP isa (.block (chkSalt H)) t fun t' => Entered Gs.len s t' ∧
      (t'.gpr .a0 != 0) = decide (kk s - loN s - (Gs.len + 2) < (if anyL s = 0 then s.gpr .a7 else 0).toNat) := by
  have hk2 : kk s ≤ 1024 := P.k2
  refine wp_sub fun t₅ o₅ e₅ => wp_subi (imm := H.D + 2) (h := by omega) fun t₆ o₆ e₆ => wp_sub fun t₇ o₇ e₇ =>
    wp_srl fun t₈ o₈ e₈ => wp_srl fun t₉ o₉ e₉ => wp_or fun t₁₀ o₁₀ e₁₀ => wp_nil ?_
  have k₁₀ : Only [.a0, .a2] t t₁₀ := (o₅.trans (o₆.trans (o₇.trans (o₈.trans (o₉.trans o₁₀))))).mono
  refine ⟨E.only P k₁₀, ?_⟩
  rw [e₁₀, o₉.get .a0, e₉, e₈, o₈.get .a1, e₇, o₇.get .a1, e₆, o₆.get .a1, e₅, o₅.get .a1, E.base.pk, E.base.plo,
    lo_N P h0, h1, ← hGl, Offset.ofNat_sub_ofNat hem, BitVec.or_comm]
  have := msgBit (x := kk s - loN s - (Gs.len + 2)) (y := (if anyL s = 0 then s.gpr .a7 else 0).toNat)
    (by omega) (BitVec.isLt _)
  rwa [ofNat_toNat] at this

section
variable {H : Hash} (hH : HashOK H) (hF : H.F ≤ 208) (hGh : ∀ x, Gs.hash x = hH.SH.H.hash x)
  (hGl : Gs.len = H.D) (hGv : Proof.Mgf1.Valid Gs)
include hH hF hGh hGl hGv

theorem main_done {t : State} (B : Before Gs.len s t) (h0 : s.mem (s.gpr .a0) ≠ 0)
    (hem : Gs.len + 2 ≤ kk s - loN s) (hfit : anyL s = 0 → (s.gpr .a7).toNat + 1 ≤ kk s - loN s - Gs.len - 1) :
    WP isa (verifyMain H) t (Done Gs s) := by
  refine WP.seq (WP.mono (pubArgs_ok P B) fun t₁ a₁ => WP.seq (WP.mono (call_ok P a₁) fun t₂ c₂ => ?_))
  have L := lay_reE P hH hGl c₂.mem h0 hem
  have hS := reE_Sp P c₂.mem
  have hmh : mh Gs.len (reE s t₂.mem) = mh Gs.len s :=
    VG.Proof.RsaOaep.RISCV64.bytes_entry c₂.mem P.kd P.ds.symm (by have := hH.hD64; omega)
  have hany : anyL (reE s t₂.mem) = anyL s := by unfold anyL; rw [reE_args P c₂.mem 0 (by decide)]
  refine WP.mono (post_ok L hH hF hGl.symm hGh hGl hGv c₂.base c₂.xs (by rw [hany]; exact hfit))
    fun t' ⟨b', r'⟩ => ⟨⟨b'.sv.sp, b'.sv.wr, b'.sv.sv⟩, fun hc => ?_⟩
  rw [r', hS, hmh, hany, reE_gpr]
  have e := res_vOut hGv P h0 (c₂.em hc) hem hfit
  by_cases hv : vOut Gs s = true
  · rw [ifp (e.mpr hv), ifp hv]; rfl
  · rw [ifn (fun h => hv (e.mp h)), ifn hv]; rfl

theorem checks_done {t : State} (E : Entered Gs.len s t) : WP isa (checks H) t (Done Gs s) := by
  have hk1 : 64 ≤ kk s := P.k1
  have hD64 : Gs.len ≤ 64 := hGl ▸ hH.hD64
  refine WP.ite _ (eval_zero _ _) (fun hz => fail_ok P E.base (zero_false Gs (by omega) (n0_eq E hz)))
    (fun hz => ?_)
  have h0 := n0_ne E hz
  -- `emLen < hLen + 2`.
  refine WP.seq (WP.mono (chkEm_ok P hGl hD64 E h0) fun t₃ ⟨E₃, r3⟩ => ?_)
  refine WP.ite _ (eval_nonzero _ _) (fun hc => fail_ok P E₃.base (short_false Gs (by omega) h0 ?_))
    (fun hc => ?_)
  · rw [r3] at hc; simp at hc; omega
  have hem : Gs.len + 2 ≤ kk s - loN s := by rw [r3] at hc; simp at hc; omega
  -- The salt length expected.
  refine WP.seq (WP.mono (expLen_ok E₃.xs) fun t₄ ⟨o₄, e₄⟩ => ?_)
  refine WP.seq (WP.mono (chkSalt_ok P hGl hD64 (E₃.only P o₄) h0 hem e₄) fun t₁₀ ⟨E₁₀, r3'⟩ => ?_)
  refine WP.ite _ (eval_nonzero _ _) (fun hc => fail_ok P E₁₀.base (short_false Gs (by omega) h0 ?_))
    (fun hc => ?_)
  · rw [r3'] at hc
    rw [sLen_eq]
    by_cases ha : anyL s = 0
    · rw [ifp ha] at hc ⊢; simp only [Option.getD_some]; simp at hc; omega
    · rw [ifn ha] at hc; simp at hc
  have hfit : anyL s = 0 → (s.gpr .a7).toNat + 1 ≤ kk s - loN s - Gs.len - 1 := fun ha => by
    rw [r3', ifp ha] at hc; simp at hc; omega
  exact main_done P hH hF hGh hGl hGv E₁₀.before h0 hem hfit

theorem code_ok : WP isa (verifyPrecomputed H) s (Post Gs s) := by
  refine WP.alloc (by decide) (by have := P.sp1; unfold frameBytes; unfold stackBytes at this; omega) ?_
  refine WP.seq (WP.mono (entry_ok P hGl.symm (hGl ▸ hH.hD64)) fun t E => WP.seq (WP.mono
    (checks_done P hH hF hGh hGl hGv E) fun t' ⟨sv, res⟩ =>
      WP.mono (restore_ok sv (fb_al8 P)) fun w ⟨habi, h3, _⟩ => ⟨habi, fun hc => ?_⟩))
  show w.gpr .a0 = _
  rw [h3]
  exact res hc

end

end

/-- The correctness of `vg_rsa_pss_<H>_mgf1_<H>_verify_precomputed`, against
its shared contract. -/
theorem code_correct {H : Hash} (hH : HashOK H) (hF : H.F ≤ 208) {Gs : Spec.Mgf1.Hash}
    (hGh : ∀ x, Gs.hash x = hH.SH.H.hash x) (hGl : Gs.len = H.D) (hGv : Proof.Mgf1.Valid Gs) (s : State)
    (h : (Spec.RsaPss.verifyPrecomputedContract Gs Gs abi stackBytes).pre s) :
    ∃ t s', Exec isa (verifyPrecomputed H) s t s' ∧ abiPreserved s s' ∧
      (Spec.RsaPss.verifyPrecomputedContract Gs Gs abi stackBytes).post s s' := by
  obtain ⟨t, s', he, habi, hr⟩ := code_ok (preP_of h) hH hF hGh hGl hGv
  refine ⟨t, s', he, habi, ?_⟩
  sig_post [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi, argRegs,
    stackArgs_five, List.append_eq]
  intro hc
  rw [hr hc]
  unfold vOut
  split <;> rfl

end VG.Proof.RsaPss.RISCV64
