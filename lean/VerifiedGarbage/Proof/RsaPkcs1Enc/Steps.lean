import VerifiedGarbage.Proof.RsaPkcs1Enc.Decrypt
import VerifiedGarbage.Proof.Rsa.Octets
import Mathlib.Data.Fintype.Card
import VerifiedGarbage.Proof.RsaPkcs1Sig.Octets

/-!
# RSAES-PKCS1-v1_5 decryption with implicit rejection: the steps of an implementation

What an implementation computes, step by step, characterized against the
specification (`Spec/RsaPkcs1Enc.lean`), whatever the target:

* `firstZero EM j`: the first index in `[2, j)` at which `EM` holds a zero, as
  a scan over the indices finds it (`firstZero_succ`); at `j = k` it is the
  separator (`separator_eq`), from which `valid` and `msgLength` follow
  (`valid_eq`, `msgLength_eq`).
* `altLength`: a fold over the 128 candidates (`altLength_eq`), each
  candidate masked by `bitMask (k - 11)`, which a loop of doublings computes
  (`bitMask_step`).
* `irprf`: the HMACs of the blocks, one after the other (`irprf_eq`).
* `kdk`: `I2OSP(d, k)` is `d` after `k - dLen` zeros (`i2osp_os2ip_pad`).
* The output: the last `l` octets of a `k`-octet string, after zeros, is the
  string with its first `k - l` octets zeroed (`out_eq`).
-/

namespace VG.Proof.RsaPkcs1Enc

open Spec.RsaPkcs1Enc
open Spec.Rsa (os2ip i2osp)

/-! ## The separator -/

/-- The first index in `[2, j)` at which `EM` holds a zero, if any. -/
def firstZero (EM : List Byte) : Nat → Option Nat
  | 0 => none
  | j + 1 => match firstZero EM j with
    | some i => some i
    | none => if 2 ≤ j ∧ EM.getD j 1 = 0 then some j else none

theorem firstZero_some {EM : List Byte} : ∀ {j i : Nat}, firstZero EM j = some i →
    2 ≤ i ∧ i < j ∧ EM.getD i 1 = 0 ∧ ∀ i', 2 ≤ i' → i' < i → EM.getD i' 1 ≠ 0
  | 0, _, h => by cases h
  | j + 1, i, h => by
    simp only [firstZero] at h
    split at h
    · rename_i i₀ h₀
      cases h
      obtain ⟨a, b, c, d⟩ := firstZero_some h₀
      exact ⟨a, by omega, c, d⟩
    · rename_i h₀
      split at h
      · rename_i hj
        cases h
        refine ⟨hj.1, by omega, hj.2, fun i' h₁ h₂ hz => ?_⟩
        exact absurd (firstZero_none h₀ i' h₁ h₂) (fun h => h hz)
      · cases h
where
  firstZero_none {EM : List Byte} : ∀ {j : Nat}, firstZero EM j = none →
      ∀ i, 2 ≤ i → i < j → EM.getD i 1 ≠ 0
    | 0, _, _, _, h => by omega
    | j + 1, h, i, h₁, h₂ => by
      simp only [firstZero] at h
      split at h
      · cases h
      · rename_i h₀
        split at h
        · cases h
        · rename_i hj
          rcases Nat.lt_succ_iff_lt_or_eq.mp h₂ with h₂ | rfl
          · exact firstZero_none h₀ i h₁ h₂
          · exact fun hz => hj ⟨h₁, hz⟩

theorem firstZero_none {EM : List Byte} {j : Nat} (h : firstZero EM j = none) :
    ∀ i, 2 ≤ i → i < j → EM.getD i 1 ≠ 0 :=
  firstZero_some.firstZero_none h

/-- The separator is the first zero from index 2 on. -/
theorem separator_eq (EM : List Byte) : separator EM = firstZero EM EM.length := by
  unfold separator
  cases hf : firstZero EM EM.length with
  | some i =>
    obtain ⟨h2, hi, hz, hmin⟩ := firstZero_some hf
    have hlt : i - 2 < (EM.drop 2).length := by simp; omega
    have : (EM.drop 2).findIdx? (· == 0) = some (i - 2) := by
      rw [List.findIdx?_eq_some_iff_getElem]
      refine ⟨hlt, ?_, fun j hj => ?_⟩
      · simp only [List.getElem_drop]
        have := hz; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)] at this
        simpa [show 2 + (i - 2) = i by omega] using this
      · simp only [List.getElem_drop]
        have := hmin (j + 2) (by omega) (by omega)
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp at hlt; omega)] at this
        simpa [Nat.add_comm] using this
    rw [this]; simp; omega
  | none =>
    have hn := firstZero_none hf
    have : (EM.drop 2).findIdx? (· == 0) = none := by
      rw [List.findIdx?_eq_none_iff]
      intro x hx
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
      simp only [List.getElem_drop]
      have := hn (2 + j) (by omega) (by simp at hj; omega)
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp at hj; omega)] at this
      simpa using this
    rw [this]; rfl

theorem valid_eq (EM : List Byte) :
    valid EM = (EM.getD 0 1 == 0 && EM.getD 1 0 == 2 &&
      match firstZero EM EM.length with
      | some i => 10 ≤ i
      | none => false) := by
  rw [valid, separator_eq]; rfl

theorem msgLength_eq (EM : List Byte) :
    msgLength EM = match firstZero EM EM.length with
      | some i => EM.length - i - 1
      | none => 0 := by
  rw [msgLength, separator_eq]; rfl

/-! ## The alternative length -/

/-- `2 ^ bitLength x - 1`: the mask of the candidates. -/
def bitMask (x : Nat) : Nat := 2 ^ bitLength x - 1

/-- A loop of doublings, `m ↦ 2 m + 1` from 0 while `m < x`, ends at
`bitMask x`: the step it takes from `2 ^ j - 1`. -/
theorem bitMask_step {x j : Nat} (hx : 1 ≤ x) (hj : 2 ^ j - 1 < x) :
    (2 * (2 ^ j - 1) + 1 = 2 ^ (j + 1) - 1) ∧ (x ≤ 2 ^ (j + 1) - 1 → bitMask x = 2 ^ (j + 1) - 1) := by
  have hp := Nat.one_le_two_pow (n := j)
  refine ⟨by rw [Nat.pow_succ]; omega, fun hle => ?_⟩
  have hb : bitLength x = j + 1 := by
    have hne : x ≠ 0 := by omega
    simp only [bitLength, hne, ↓reduceIte, Nat.add_right_cancel_iff]
    have h1 : x < 2 ^ (j + 1) := by omega
    have h2 : 2 ^ j ≤ x := by omega
    exact (Nat.log2_eq_iff hne).mpr ⟨h2, h1⟩
  rw [bitMask, hb]

/-- A candidate, masked. -/
theorem cand_eq (k : Nat) (a b : Byte) :
    os2ip [a, b] % 2 ^ bitLength (k - 11) = (256 * a.toNat + b.toNat) % 2 ^ bitLength (k - 11) := by
  simp [os2ip]

/-- One step of the fold that `altLength` is. -/
def altStep (k : Nat) (CL : List Byte) (al i : Nat) : Nat :=
  let c := os2ip [CL.getD (2 * i) 0, CL.getD (2 * i + 1) 0] % 2 ^ bitLength (k - 11)
  if c ≤ k - 11 then c else al

theorem altLength_eq (k : Nat) (CL : List Byte) :
    altLength k CL = (List.range 128).foldl (altStep k CL) 0 := rfl

theorem foldl_range_succ (f : Nat → Nat → Nat) (a j : Nat) :
    (List.range (j + 1)).foldl f a = f ((List.range j).foldl f a) j := by
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-! ## IRPRF -/

/-- Block `i` of IRPRF's output, before the truncation. -/
def prfBlock (kdk label : List Byte) (length i : Nat) : List Byte :=
  Spec.Hmac.hmac Spec.Hmac.sha256 kdk (i2osp i 2 ++ label ++ i2osp (8 * length) 2)

theorem irprf_eq (kdk label : List Byte) (length : Nat) :
    irprf kdk label length = ((List.range ((length + 31) / 32)).flatMap (prfBlock kdk label length)).take length :=
  rfl

/-- Two octets, most significant first. -/
theorem i2osp_two (x : Nat) : i2osp x 2 = [BitVec.ofNat 8 (x / 256), BitVec.ofNat 8 x] := by
  simp [i2osp, List.range_succ]

/-! ## The key derivation key -/

/-- `I2OSP(x, n + l)` of `x < 256^l`: zeros, then `I2OSP(x, l)`. -/
theorem i2osp_add {x : Nat} (n l : Nat) (hx : x < 256 ^ l) :
    i2osp x (n + l) = List.replicate n 0 ++ i2osp x l := by
  refine List.ext_getElem (by simp [i2osp]) fun i h₁ _ => ?_
  simp only [i2osp, List.getElem_map, List.getElem_range]
  by_cases hi : i < n
  · rw [List.getElem_append_left (by simpa using hi)]
    simp only [List.getElem_replicate]
    have : x / 256 ^ (n + l - 1 - i) = 0 :=
      Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))
    rw [this]; rfl
  · rw [List.getElem_append_right (by simp; omega)]
    simp only [List.length_replicate, List.getElem_map, List.getElem_range]
    rw [show n + l - 1 - i = l - 1 - (i - n) by omega]

/-- `I2OSP(OS2IP(d), k)` for `d` of at most `k` octets: `d` after zeros. -/
theorem i2osp_os2ip_pad (dB : List Byte) {k : Nat} (h : dB.length ≤ k) :
    i2osp (os2ip dB) k = List.replicate (k - dB.length) 0 ++ dB := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left, Nat.add_comm, i2osp_add n _ (Proof.Rsa.lt_of_os2ip dB), Proof.Rsa.i2osp_os2ip]

/-! ## The output -/

/-- The last `l` octets of a `k`-octet string after zeros: the string with
its first `k - l` octets zeroed. -/
theorem out_eq {X : List Byte} {l : Nat} (hl : l ≤ X.length) :
    List.replicate (X.length - l) 0 ++ lastN l X =
      (List.range X.length).map fun i => if X.length - l ≤ i then X.getD i 0 else 0 := by
  refine List.ext_getElem (by simp [lastN]) fun i h₁ h₂ => ?_
  simp only [List.getElem_map, List.getElem_range]
  by_cases hi : X.length - l ≤ i
  · simp only [hi, ↓reduceIte]
    rw [List.getElem_append_right (by simp; omega)]
    simp only [lastN, List.length_replicate, List.getElem_drop]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp at h₂; omega)]
    simp only [Option.getD_some]
    congr 1; omega
  · simp only [hi, ↓reduceIte]
    rw [List.getElem_append_left (by simp; omega)]
    simp

end VG.Proof.RsaPkcs1Enc
