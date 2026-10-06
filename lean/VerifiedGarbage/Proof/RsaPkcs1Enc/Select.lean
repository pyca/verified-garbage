import VerifiedGarbage.Proof.RsaPkcs1Enc.Steps

/-!
# RSAES-PKCS1-v1_5 decryption with implicit rejection: the selection

What an implementation's last steps compute, whatever the target: the mask
of the candidate lengths by doublings (`bitMask_lt`, `bitMask_ge`), the
alternative length as a fold of masked candidates (`altFold_le`,
`altStep_eq`), the validity of the padding as a scan finds it (`vEM_eq`),
and the output, byte by byte (`outByte`), which is the message
`implicitDecode` returns after zeros (`sel_eq`).
-/

namespace VG.Proof.RsaPkcs1Enc

open Spec.RsaPkcs1Enc

/-! ## The mask of the candidates -/

/-- Before the last doubling, the mask is below `x`. -/
theorem bitMask_lt {x j : Nat} (hx : x ≠ 0) (hj : j < bitLength x) : 2 ^ j - 1 < x := by
  have : j ≤ x.log2 := by simp only [bitLength, hx, ↓reduceIte] at hj; omega
  have := (Nat.le_log2 hx).1 this
  omega

/-- After the last doubling, it is not. -/
theorem bitMask_ge {x : Nat} (hx : x ≠ 0) : x ≤ 2 ^ bitLength x - 1 := by
  have := Nat.lt_log2_self (n := x)
  simp only [bitLength, hx, ↓reduceIte]
  omega

theorem bitMask_le {x : Nat} (hx : x ≠ 0) : bitMask x ≤ 2 * x := by
  have h1 := Nat.log2_self_le hx
  simp only [bitMask, bitLength, hx, ↓reduceIte, Nat.pow_succ]
  omega

/-! ## The alternative length -/

theorem altFold_le (k : Nat) (CL : List Byte) (j : Nat) :
    (List.range j).foldl (altStep k CL) 0 ≤ k - 11 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [foldl_range_succ]
    simp only [altStep]
    split <;> omega

/-- The candidate, as a loop computes it. -/
theorem altStep_eq (k : Nat) (CL : List Byte) (al i : Nat) (h : 2 * i + 1 < CL.length) :
    altStep k CL al i = (let c := (256 * (CL[2 * i]'(by omega)).toNat + (CL[2 * i + 1]'h).toNat) &&& bitMask (k - 11)
      if c ≤ k - 11 then c else al) := by
  simp only [altStep, cand_eq, bitMask, Nat.and_two_pow_sub_one_eq_mod, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show 2 * i < CL.length by omega), List.getElem?_eq_getElem h, Option.getD_some]

/-! ## The validity and the output -/

/-- Whether the padding is valid, from the scan. -/
abbrev vOf (b0 b1 : Byte) (f : Bool) (sep : Nat) : Bool := decide (b0 = 0 ∧ b1 = 2 ∧ f = true ∧ 10 ≤ sep)

/-- The selected length. -/
abbrev lselOf (v : Bool) (sep al k : Nat) : Nat := if v then k - sep - 1 else al

/-- The validity of `EM`'s padding, as the scan finds it. -/
abbrev vEM (EM : List Byte) (k : Nat) : Bool :=
  vOf (EM.getD 0 1) (EM.getD 1 1) (firstZero EM k).isSome ((firstZero EM k).getD 0)

/-- Byte `i` of the output. -/
def outByte (v ok : Bool) (kl i : Nat) (e a : Byte) : Byte :=
  if kl ≤ i ∧ ok = true then (if v then e else a) else 0

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

theorem outByte_false (v : Bool) (kl i : Nat) (e a : Byte) : outByte v false kl i e a = 0 := by
  simp [outByte]

end VG.Proof.RsaPkcs1Enc
