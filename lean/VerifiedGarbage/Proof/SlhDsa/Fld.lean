module

public import VerifiedGarbage.Proof.SlhDsa.Internal
public import VerifiedGarbage.Spec.SlhDsa
import VerifiedGarbage.Proof.SlhDsa.Lemmas

/-!
# SLH-DSA: addresses as their five fields

The addresses the WOTS⁺ and tree code of every target writes a field at a
time (`fld`), and the member functions of the specification on them.
-/

@[expose] public section

/-! ## addresses as their five fields

An address whose layer and tree addresses are `a16` is
`a16 ‖ toByte(type, 4) ‖ toByte(kp, 4) ‖ toByte(c, 4) ‖ toByte(h, 4)`
(`fld`), as the code writes it, a field at a time; the member functions of
the specification (Table 1) set one field of it (`setTypeAndClear` the type,
and clears the rest). So every address the WOTS⁺ code hashes is a `fld`,
and the specification's are too.
-/

namespace VG.Proof.SlhDsa

open VG.Spec.SlhDsa

/-- The address with the layer and tree addresses `a16` and the fields
`ty`, `kp`, `c`, `h`. -/
def fld (a16 : List Byte) (ty kp c h : Nat) : Adrs :=
  a16 ++ (toByte ty 4 ++ (toByte kp 4 ++ (toByte c 4 ++ toByte h 4)))

theorem toByte_length (x n : Nat) : (toByte x n).length = n := by simp [toByte]

theorem toByte_zero (n : Nat) : toByte 0 n = List.replicate n 0 := by
  apply List.ext_getElem (by simp [toByte])
  intro i h₁ h₂
  simp [toByte]

variable {a16 : List Byte} (h16 : a16.length = 16)
include h16

theorem fld_length (ty kp c h : Nat) : (fld a16 ty kp c h).length = 32 := by
  simp [fld, toByte_length, h16]

omit h16 in
theorem treeAdrs_eq : treeAdrs a16 = fld a16 0 0 0 0 := by
  simp only [treeAdrs, fld, toByte_zero]
  rfl

omit h16 in
/-- `setBytes` over a part of the same length. -/
theorem setBytes_mid {P Y Q X : List Byte} (hY : Y.length = X.length) :
    setBytes (P ++ (Y ++ Q)) P.length X = P ++ (X ++ Q) := by
  unfold setBytes
  rw [List.take_left', List.drop_append, ← hY, List.drop_eq_nil_of_le (Nat.le_add_right _ _), List.nil_append,
    Nat.add_sub_cancel_left, List.drop_left' rfl, List.append_assoc]
  rfl

theorem setKeyPairAddress_fld (ty kp c h i : Nat) :
    setKeyPairAddress (fld a16 ty kp c h) i = fld a16 ty i c h := by
  have e := setBytes_mid (P := a16 ++ toByte ty 4) (Y := toByte kp 4) (Q := toByte c 4 ++ toByte h 4)
    (X := toByte i 4) (by simp [toByte_length])
  simp only [List.length_append, h16, toByte_length, List.append_assoc] at e
  exact e

theorem setChainAddress_fld (ty kp c h i : Nat) :
    setChainAddress (fld a16 ty kp c h) i = fld a16 ty kp i h := by
  have e := setBytes_mid (P := a16 ++ (toByte ty 4 ++ toByte kp 4)) (Y := toByte c 4) (Q := toByte h 4)
    (X := toByte i 4) (by simp [toByte_length])
  simp only [List.length_append, h16, toByte_length, List.append_assoc] at e
  exact e

theorem setTreeHeight_fld (ty kp c h i : Nat) :
    setTreeHeight (fld a16 ty kp c h) i = fld a16 ty kp i h :=
  setChainAddress_fld h16 ty kp c h i

theorem setHashAddress_fld (ty kp c h i : Nat) :
    setHashAddress (fld a16 ty kp c h) i = fld a16 ty kp c i := by
  have e := setBytes_mid (P := a16 ++ (toByte ty 4 ++ (toByte kp 4 ++ toByte c 4))) (Y := toByte h 4) (Q := [])
    (X := toByte i 4) (by simp [toByte_length])
  simp only [List.length_append, h16, toByte_length, List.append_assoc, List.append_nil] at e
  exact e

theorem setTreeIndex_fld (ty kp c h i : Nat) :
    setTreeIndex (fld a16 ty kp c h) i = fld a16 ty kp c i :=
  setHashAddress_fld h16 ty kp c h i

theorem setTypeAndClear_fld (ty kp c h Y : Nat) :
    setTypeAndClear (fld a16 ty kp c h) Y = fld a16 Y 0 0 0 := by
  have e := setBytes_mid (P := a16) (Y := toByte ty 4 ++ (toByte kp 4 ++ (toByte c 4 ++ toByte h 4))) (Q := [])
    (X := toByte Y 4 ++ toByte 0 12) (by simp [toByte_length])
  simp only [h16, List.append_nil] at e
  simp only [setTypeAndClear, fld]
  rw [e, show toByte 0 12 = toByte 0 4 ++ (toByte 0 4 ++ toByte 0 4) by simp only [toByte_zero]; rfl]

theorem getKeyPairAddress_fld (ty kp c h : Nat) :
    getKeyPairAddress (fld a16 ty kp c h) = kp % 2 ^ 32 := by
  simp only [getKeyPairAddress, fld]
  rw [show (a16 ++ (toByte ty 4 ++ (toByte kp 4 ++ (toByte c 4 ++ toByte h 4)))).drop 20 =
      toByte kp 4 ++ (toByte c 4 ++ toByte h 4) by
    simp [List.drop_append, h16, toByte_length]]
  rw [toInt, List.take_append_of_le_length (by simp [toByte_length]), List.take_of_length_le (by simp [toByte_length])]
  exact VG.Proof.SlhDsa.toInt_toByte4 kp

/-! ## The WOTS⁺ addresses -/

theorem wotsAdrs_fld (kp : Nat) : wotsAdrs a16 kp = fld a16 WOTS_HASH kp 0 0 := by
  rw [wotsAdrs, treeAdrs_eq, setTypeAndClear_fld h16, setKeyPairAddress_fld h16]

theorem wotsSkAdrs_fld (ty kp c h : Nat) (hkp : kp < 2 ^ 32) :
    wotsSkAdrs (fld a16 ty kp c h) = fld a16 WOTS_PRF kp 0 0 := by
  rw [wotsSkAdrs, getKeyPairAddress_fld h16, Nat.mod_eq_of_lt hkp, setTypeAndClear_fld h16,
    setKeyPairAddress_fld h16]

theorem wotsPkAdrs_fld (ty kp c h : Nat) (hkp : kp < 2 ^ 32) :
    wotsPkAdrs (fld a16 ty kp c h) = fld a16 WOTS_PK kp 0 0 := by
  rw [wotsPkAdrs, getKeyPairAddress_fld h16, Nat.mod_eq_of_lt hkp, setTypeAndClear_fld h16,
    setKeyPairAddress_fld h16]

end VG.Proof.SlhDsa
