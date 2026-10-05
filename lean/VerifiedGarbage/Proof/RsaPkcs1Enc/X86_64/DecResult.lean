import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecSel

/-!
# RSAES-PKCS1-v1_5 decryption on x86-64: the selected message

What the output loop writes, for the validity, length and message the scan
and the derivation found, is the message `implicitDecode` returns, after
zeros (`sel_eq`).
-/

namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec

open VG VG.X86_64 Spec.RsaPkcs1Enc

theorem vEM_eq {EM : List Byte} {k : Nat} (hEM : EM.length = k) (hk : 2 ≤ k) : vEM EM k = valid EM := by
  rw [valid_eq, hEM, show EM.getD 1 0 = EM.getD 1 1 by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl]
  simp only [vEM, vOf]
  cases hf : firstZero EM k with
  | none => simp
  | some i =>
    simp only [Option.isSome_some, Option.getD_some]
    generalize EM.getD 0 1 = x
    generalize EM.getD 1 1 = y
    by_cases a : x = 0 <;> by_cases b : y = 2 <;> by_cases c : 10 ≤ i <;> simp [a, b, c, Bool.beq_eq_decide_eq]

theorem msgLength_le {EM : List Byte} : msgLength EM ≤ EM.length := by
  rw [msgLength_eq]; split
  · exact Nat.le_trans (Nat.sub_le _ _) (Nat.sub_le _ _)
  · exact Nat.zero_le _

theorem lastN_length {l : Nat} {X : List Byte} (h : l ≤ X.length) : (lastN l X).length = l := by
  simp [lastN]; omega

/-- The output of the selection, for a successful private-key operation. -/
theorem sel_eq {EM AM : List Byte} {k al : Nat} (hEM : EM.length = k) (hAM : AM.length = k) (hk : 11 ≤ k)
    (hal : al ≤ k - 11) :
    let M := if valid EM then lastN (msgLength EM) EM else lastN al AM
    lselOf (vEM EM k) ((firstZero EM k).getD 0) al k = M.length ∧
    (List.range k).map (fun i => outByte (vEM EM k) true (k - lselOf (vEM EM k) ((firstZero EM k).getD 0) al k) i
      (EM.getD i 1) (AM.getD i 0)) = List.replicate (k - M.length) 0 ++ M := by
  intro M
  rw [vEM_eq hEM (by omega)]
  have hL : lselOf (valid EM) ((firstZero EM k).getD 0) al k = M.length := by
    simp only [lselOf, M]
    cases hv : valid EM
    · simp [lastN_length (show al ≤ AM.length by omega)]
    · simp only [↓reduceIte]
      rw [lastN_length msgLength_le, msgLength_eq, hEM]
      rw [valid_eq, hEM] at hv
      cases hf : firstZero EM k with
      | none => simp [hf] at hv
      | some i => rfl
  refine ⟨hL, ?_⟩
  rw [hL]
  cases hv : valid EM
  · simp only [M, hv, Bool.false_eq_true, ↓reduceIte]
    have hl : al ≤ AM.length := by omega
    rw [lastN_length hl, show k = AM.length from hAM.symm, out_eq hl]
    refine List.map_congr_left fun i hi => ?_
    simp only [outByte, and_true, Bool.false_eq_true, ↓reduceIte]
  · simp only [M, hv, ↓reduceIte]
    have hl := (msgLength_le (EM := EM))
    rw [lastN_length hl, show k = EM.length from hEM.symm, out_eq hl]
    refine List.map_congr_left fun i hi => ?_
    simp only [outByte, and_true, ↓reduceIte]
    rw [List.mem_range] at hi
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    rfl

end VG.Proof.RsaPkcs1Enc.X86_64.Dec
