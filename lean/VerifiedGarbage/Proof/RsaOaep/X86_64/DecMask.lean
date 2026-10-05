import VerifiedGarbage.Proof.RsaOaep.X86_64.EncSpec
import VerifiedGarbage.Proof.RsaOaep.X86_64.DecSpec

/-!
# RSAES-OAEP decryption on x86-64: unmasking

`EM`, at the start of our working space (`V`), unmasked as the code does it
(the seed with MGF1 of `maskedDB`, then `maskedDB` with MGF1 of the seed,
each a `mixV`), gives the seed and `DB` that `decode` computes (`unmask`).
-/

namespace VG.Proof.RsaOaep.X86_64

open VG
open VG.Spec.Mgf1 (Hash xorBytes mgf1)
open VG.Proof.MlKem.X86_64 (ifp ifn)
open VG.Proof.Mgf1 (Valid xorBytes_getD mgf1_length)

theorem map_range_getD' (V : Nat → Byte) {k i : Nat} (hi : i < k) : ((List.range k).map V).getD i 0 = V i := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem drop_getD' (l : List Byte) (n i : Nat) : (l.drop n).getD i 0 = l.getD (n + i) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem take_getD' (l : List Byte) {n i : Nat} (hi : i < n) : (l.take n).getD i 0 = l.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, hi]

/-- The seed and `DB`, unmasked from `EM` (`k` bytes of `V`). -/
theorem unmask {G : Hash} (hG : Valid G) (V : Nat → Byte) {D k : Nat} (hk : 2 * D + 2 ≤ k) :
    srcB (mixV V (mgf1 G (srcB V (1 + D) (k - D - 1)) D) 1 D) 1 D =
      xorBytes ((((List.range k).map V).drop 1).take D) (mgf1 G (((List.range k).map V).drop (D + 1)) D) ∧
    srcB (mixV (mixV V (mgf1 G (srcB V (1 + D) (k - D - 1)) D) 1 D)
        (mgf1 G (srcB (mixV V (mgf1 G (srcB V (1 + D) (k - D - 1)) D) 1 D) 1 D) (k - D - 1)) (1 + D) (k - D - 1))
        (1 + D) (k - D - 1) =
      xorBytes (((List.range k).map V).drop (D + 1))
        (mgf1 G (xorBytes ((((List.range k).map V).drop 1).take D) (mgf1 G (((List.range k).map V).drop (D + 1)) D))
          (k - D - 1)) := by
  have hlen : ((List.range k).map V).length = k := by simp
  have e1 : srcB V (1 + D) (k - D - 1) = ((List.range k).map V).drop (D + 1) := by
    refine srcB_eq (by simp; omega) fun i hi => ?_
    rw [drop_getD', map_range_getD' V (by omega)]; congr 1; omega
  have hms : ((((List.range k).map V).drop 1).take D).length = D := by simp; omega
  have hm1 := mgf1_length hG (((List.range k).map V).drop (D + 1)) D
  have hseedl : (xorBytes ((((List.range k).map V).drop 1).take D)
      (mgf1 G (((List.range k).map V).drop (D + 1)) D)).length = D := by
    rw [Proof.Mgf1.xorBytes_length, hms, hm1, Nat.min_self]
  have e2 : srcB (mixV V (mgf1 G (srcB V (1 + D) (k - D - 1)) D) 1 D) 1 D =
      xorBytes ((((List.range k).map V).drop 1).take D) (mgf1 G (((List.range k).map V).drop (D + 1)) D) := by
    refine srcB_eq hseedl fun i hi => ?_
    rw [mixV, ifp (by omega), e1, xorBytes_getD (by omega) (by omega), take_getD' _ hi, drop_getD',
      map_range_getD' V (by omega), Nat.add_sub_cancel_left]
  refine ⟨e2, ?_⟩
  rw [e2]
  have hmdb : (((List.range k).map V).drop (D + 1)).length = k - D - 1 := by simp; omega
  refine srcB_eq (by rw [Proof.Mgf1.xorBytes_length, hmdb, mgf1_length hG, Nat.min_self]) fun i hi => ?_
  rw [mixV, ifp (by omega), mixV, ifn (by omega), xorBytes_getD (by omega) (by rw [mgf1_length hG]; omega),
    drop_getD', map_range_getD' V (by omega), Nat.add_sub_cancel_left]
  congr 2; omega

end VG.Proof.RsaOaep.X86_64
