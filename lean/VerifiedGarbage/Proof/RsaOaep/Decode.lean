import VerifiedGarbage.Proof.RsaOaep.Mask
import VerifiedGarbage.Proof.RsaOaep.Scan
import VerifiedGarbage.Spec.Rsa.Contract

/-!
# RSAES-OAEP: the decoding, on any target

What decryption returns for the private-key operation's outcome (`decOut`),
and the lemmas that read it from a working space: `EM` unmasked by MGF1
twice (`chain_eq`), `decode` with `DB` read from it (`decode_eq`), and the
output written under a mask (`out_list`, `out_zero`).
-/

namespace VG.Proof.RsaOaep

open VG
open VG.Proof.Mgf1 (ifp ifn)

theorem mixV_congr {V V' : Nat → Byte} (mk : List Byte) (e n : Nat) {o : Nat} (h : V o = V' o) :
    mixV V mk e n o = mixV V' mk e n o := by simp only [mixV, h]

theorem mk_eq_zero (p : Prop) [Decidable p] : mk p = 0 ↔ ¬ p := by
  unfold mk; by_cases hp : p
  · rw [ifp hp]; exact ⟨fun h => absurd h (by decide), fun h => absurd hp h⟩
  · rw [ifn hp]; exact ⟨fun _ => hp, fun _ => rfl⟩

theorem zM_mk (x : BitVec 64) : zM x = mk (x = 0) := rfl

/-- `out`, from the buffer shifted by `idx + 1` under the mask all ones. -/
theorem out_list {m : Mem} {o : Addr} {k : Nat} {T : List Byte} {idx : Nat} (hT : T.length ≤ k) (hi : idx < T.length)
    (h : ∀ i < k, m (o + BitVec.ofNat 64 i) = T.getD (i + (idx + 1)) 0) :
    Spec.Rsa.bytesAt m o k = T.drop (idx + 1) ++ Spec.RsaOaep.zeros (k - (T.drop (idx + 1)).length) := by
  simp only [Spec.Rsa.bytesAt]
  refine range_ext (by simp [Spec.RsaOaep.zeros]; omega) fun i hi' => ?_
  rw [h i hi', Proof.Mgf1.getD_append, List.length_drop]
  by_cases hl : i < T.length - (idx + 1)
  · rw [ifp hl, drop_getD']; congr 1; omega
  · rw [ifn hl]
    simp [Spec.RsaOaep.zeros, List.getD_eq_getElem?_getD, List.getElem?_replicate]
    rw [List.getElem?_eq_none (by omega), ifp (by omega)]; rfl

theorem out_zero {m : Mem} {o : Addr} {k : Nat} (h : ∀ i < k, m (o + BitVec.ofNat 64 i) = 0) :
    Spec.Rsa.bytesAt m o k = Spec.RsaOaep.zeros k := by
  simp only [Spec.Rsa.bytesAt, Spec.RsaOaep.zeros]
  exact (List.map_congr_left fun i hi => h i (List.mem_range.mp hi)).trans (by rw [List.map_const', List.length_range])

/-! ## The decoding's lists -/

open VG.Spec.Mgf1 (mgf1 xorBytes) in
/-- The working space after the label's hash and MGF1 twice, on `EM`'s
place: `EM` unmasked. -/
theorem chain_eq {G : Spec.Mgf1.Hash} {V V1 V3 V5 : Nat → Byte} {D k : Nat} (hk : 2 * D + 2 ≤ k)
    (h1 : ∀ x < k, V1 x = V x)
    (h3 : ∀ x < k, V3 x = mixV V1 (mgf1 G (srcB V1 (1 + D) (k - (D + 1))) D) 1 D x)
    (h5 : ∀ x < k, V5 x = mixV V3 (mgf1 G (srcB V3 1 D) (k - (D + 1))) (1 + D) (k - (D + 1)) x) :
    ∀ x < k, V5 x = mixV (mixV V (mgf1 G (srcB V (1 + D) (k - D - 1)) D) 1 D)
      (mgf1 G (srcB (mixV V (mgf1 G (srcB V (1 + D) (k - D - 1)) D) 1 D) 1 D) (k - D - 1)) (1 + D) (k - D - 1) x := by
  have e0 : k - (D + 1) = k - D - 1 := by omega
  rw [e0] at h3 h5
  have s1 : srcB V1 (1 + D) (k - D - 1) = srcB V (1 + D) (k - D - 1) :=
    List.map_congr_left fun i hi => h1 _ (by have := List.mem_range.mp hi; omega)
  have v3 : ∀ x < k, V3 x = mixV V (mgf1 G (srcB V (1 + D) (k - D - 1)) D) 1 D x := fun x hx => by
    rw [h3 x hx, s1]; exact mixV_congr _ _ _ (h1 x hx)
  have s3 : srcB V3 1 D = srcB (mixV V (mgf1 G (srcB V (1 + D) (k - D - 1)) D) 1 D) 1 D :=
    List.map_congr_left fun i hi => v3 _ (by have := List.mem_range.mp hi; omega)
  intro x hx
  rw [h5 x hx, s3]; exact mixV_congr _ _ _ (v3 x hx)

theorem srcB_drop (V : Nat → Byte) (a n d : Nat) :
    (srcB V a n).drop d = srcB V (a + d) (n - d) := by
  refine (srcB_eq (by simp [srcB]) fun i hi => ?_).symm
  rw [drop_getD', srcB, map_range_getD' _ (by omega)]; congr 1; omega

theorem srcB_take (V : Nat → Byte) (a n d : Nat) (hd : d ≤ n) : (srcB V a n).take d = srcB V a d := by
  refine (srcB_eq (by simp [srcB]; omega) fun i hi => ?_).symm
  rw [take_getD' _ hi, srcB, map_range_getD' _ (by omega)]

theorem scanS_congr {f g : Nat → Byte} (c₀ : BitVec 64) : ∀ n, (∀ i < n, f i = g i) → scanS f c₀ n = scanS g c₀ n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [scanS]
    rw [scanS_congr c₀ n fun i hi => h i (by omega), h n (by omega)]

open VG.Spec.Mgf1 (mgf1 xorBytes) in
/-- `decode`, with `DB` read from the working space after the unmasking. -/
theorem decode_eq {H G : Spec.Mgf1.Hash} (hGv : Proof.Mgf1.Valid G) (label : List Byte) {V V5 : Nat → Byte}
    {D k : Nat} (hk : 2 * D + 2 ≤ k) (hHl : H.len = D)
    (h5 : ∀ x < k, V5 x = mixV (mixV V (mgf1 G (srcB V (1 + D) (k - D - 1)) D) 1 D)
      (mgf1 G (srcB (mixV V (mgf1 G (srcB V (1 + D) (k - D - 1)) D) 1 D) 1 D) (k - D - 1)) (1 + D) (k - D - 1) x) :
    Spec.RsaOaep.decode H G label ((List.range k).map V) =
      match (srcB V5 (1 + 2 * D) (k - (2 * D + 1))).dropWhile (· == 0) with
      | 0x01 :: m => if ((List.range k).map V).take 1 = [0x00] ∧ srcB V5 (1 + D) D = H.hash label then some m
        else none
      | _ => none := by
  have hdb := (unmask hGv V hk).2
  have h5' : srcB (mixV (mixV V (mgf1 G (srcB V (1 + D) (k - D - 1)) D) 1 D)
      (mgf1 G (srcB (mixV V (mgf1 G (srcB V (1 + D) (k - D - 1)) D) 1 D) 1 D) (k - D - 1)) (1 + D) (k - D - 1))
      (1 + D) (k - D - 1) = srcB V5 (1 + D) (k - D - 1) :=
    List.map_congr_left fun i hi => (h5 _ (by have := List.mem_range.mp hi; omega)).symm
  rw [h5'] at hdb
  simp only [Spec.RsaOaep.decode, List.length_map, List.length_range, hHl]
  rw [ifn (by omega), ← hdb, srcB_drop, srcB_take _ _ _ _ (by omega),
    show 1 + D + D = 1 + 2 * D by omega, show k - D - 1 - D = k - (2 * D + 1) by omega]
  rfl

/-! ## The outcome -/

/-- What decryption returns for the private-key operation's outcome. -/
def decOut (H G : Spec.Mgf1.Hash) (label : List Byte) : Spec.Rsa.Outcome → Spec.Rsa.Outcome
  | .ok em => match Spec.RsaOaep.decode H G label em with
    | some m => .ok m
    | none => .invalid
  | .invalid => .invalid
  | .fault => .fault

/-- `EM` too short for the hash: the decoding fails. -/
theorem decOut_short {H G : Spec.Mgf1.Hash} {label : List Byte} {o : Spec.Rsa.Outcome} {k : Nat}
    (hl : ∀ em, o = .ok em → em.length = k) (hk : k < 2 * H.len + 2) :
    decOut H G label o = match o with | .fault => .fault | _ => .invalid := by
  cases o with
  | ok em =>
    simp only [decOut, Spec.RsaOaep.decode]
    rw [ifp (by rw [hl em rfl]; exact hk)]
  | invalid => rfl
  | fault => rfl

end VG.Proof.RsaOaep
