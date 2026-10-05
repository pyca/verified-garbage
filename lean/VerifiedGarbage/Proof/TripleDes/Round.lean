import VerifiedGarbage.Spec.TripleDes
import VerifiedGarbage.Proof.Framework.Bitslice.Table
import VerifiedGarbage.Proof.Framework.PowLit

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.Permutation`. -/
section

/-! Fixed permutations in the FIPS numbering convention. Untrusted. -/

namespace VG.Proof.TripleDes

open VG.Spec.TripleDes

private theorem prefix_bit {n m : Nat} (positions : Vector Nat m) (x : BitVec n)
    (hn : 0 < n) (k : Nat) (hk : k ≤ m) (j : Nat) (hj : j < m) :
    ((List.range k).foldl (fun (out : BitVec m) i =>
      (out <<< 1) ||| (((x >>> (n - positions.getD i 1)) &&& 1).setWidth m))
      (0 : BitVec m)).getLsbD j =
      if j < k then x.getLsbD (n - positions.getD (k - 1 - j) 1) else false := by
  induction k generalizing j with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, BitVec.getLsbD_or,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_and,
      BitVec.getLsbD_ushiftRight, hj, decide_true, Bool.true_and]
    by_cases hzero : j = 0
    · subst j
      simp [hn]
    · have hj1 : j - 1 < m := by omega
      rw [ih (by omega) (j - 1) hj1]
      have hge : ¬j < 1 := by omega
      have hone : (1 : BitVec n).getLsbD j = false := by
        change (BitVec.ofNat n 1).getLsbD j = false
        rw [BitVec.getLsbD_ofNat]
        have hnat : Nat.testBit 1 j = false := by
          change Nat.testBit (2 ^ 0) j = false
          rw [Nat.testBit_two_pow]
          exact decide_eq_false (Ne.symm hzero)
        rw [hnat, Bool.and_false]
      simp only [hone, Bool.and_false, Bool.or_false, hge,
        decide_false, Bool.not_false, Bool.true_and]
      by_cases hlt : j < k + 1
      · have hlt' : j - 1 < k := by omega
        simp only [hlt, hlt', ite_true]
        have heq : k - 1 - (j - 1) = k + 1 - 1 - j := by omega
        rw [heq]
      · have hlt' : ¬j - 1 < k := by omega
        simp only [hlt, hlt', ite_false]

theorem permute_bit {n m : Nat} (positions : Vector Nat m) (x : BitVec n)
    (hn : 0 < n) (j : Nat) (hj : j < m) :
    (permute positions x).getLsbD j = x.getLsbD (n - positions.getD (m - 1 - j) 1) := by
  have h := prefix_bit positions x hn m (Nat.le_refl m) j hj
  simpa only [permute, hj, ite_true] using h

end VG.Proof.TripleDes

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.Core`. -/
section

namespace VG.Proof.TripleDes

open VG.Spec.TripleDes

theorem ip_bounds : ∀ k < 64, 1 ≤ ip.getD k 1 ∧ ip.getD k 1 ≤ 64 := by decide +kernel
theorem fp_bounds : ∀ k < 64, 1 ≤ fp.getD k 1 ∧ fp.getD k 1 ≤ 64 := by decide +kernel

theorem ip_fp_positions : ∀ j < 64,
    64 - fp.getD (64 - 1 - (64 - ip.getD (64 - 1 - j) 1)) 1 = j := by decide +kernel

theorem fp_ip_positions : ∀ j < 64,
    64 - ip.getD (64 - 1 - (64 - fp.getD (64 - 1 - j) 1)) 1 = j := by decide +kernel

theorem ip_fp (x : BitVec 64) : permute ip (permute fp x) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hj' : 64 - 1 - j < 64 := by omega
  obtain ⟨lo, hi⟩ := ip_bounds _ hj'
  have hk : 64 - ip.getD (64 - 1 - j) 1 < 64 := by omega
  rw [permute_bit ip _ (by decide) j hj,
    permute_bit fp _ (by decide) _ hk, ip_fp_positions j hj]

theorem fp_ip (x : BitVec 64) : permute fp (permute ip x) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hj' : 64 - 1 - j < 64 := by omega
  obtain ⟨lo, hi⟩ := fp_bounds _ hj'
  have hk : 64 - fp.getD (64 - 1 - j) 1 < 64 := by omega
  rw [permute_bit fp _ (by decide) j hj,
    permute_bit ip _ (by decide) _ hk, fp_ip_positions j hj]

def feistelStep (k : BitVec 48) (state : BitVec 32 × BitVec 32) : BitVec 32 × BitVec 32 :=
  (state.2, state.1 ^^^ roundFunction state.2 k)

/-- DES between IP and FP, including its final half swap. -/
def desCore (keys : DesSchedule) (direction : Direction) (input : BitVec 64) : BitVec 64 :=
  let (l, r) := (List.range 16).foldl (fun state j =>
    feistelStep (keys.getD (if direction = .encrypt then j else 15 - j) 0) state)
      ((input >>> 32).setWidth 32, input.setWidth 32)
  r ++ l

theorem des_eq_core (keys : DesSchedule) (direction : Direction) (input : BitVec 64) :
    des keys direction input = permute fp (desCore keys direction (permute ip input)) := rfl

theorem encryptBlock_eq_cores (k : Schedule) (b : Block) :
    encryptBlock k b = encodeBlock (permute fp
      (desCore (componentSchedule k 2) .encrypt
        (desCore (componentSchedule k 1) .decrypt
          (desCore (componentSchedule k 0) .encrypt (permute ip (decodeBlock b)))))) := by
  unfold encryptBlock
  rw [des_eq_core, des_eq_core, des_eq_core, ip_fp, ip_fp]

theorem decryptBlock_eq_cores (k : Schedule) (b : Block) :
    decryptBlock k b = encodeBlock (permute fp
      (desCore (componentSchedule k 0) .decrypt
        (desCore (componentSchedule k 1) .encrypt
          (desCore (componentSchedule k 2) .decrypt (permute ip (decodeBlock b)))))) := by
  unfold decryptBlock
  rw [des_eq_core, des_eq_core, des_eq_core, ip_fp, ip_fp]

def roundKey (keys : DesSchedule) (direction : Direction) (j : Nat) : BitVec 48 :=
  keys.getD (if direction = .encrypt then j else 15 - j) 0

def roundPrefix (keys : DesSchedule) (direction : Direction) (n : Nat)
    (v : BitVec 32 × BitVec 32) : BitVec 32 × BitVec 32 :=
  (List.range n).foldl (fun state j => feistelStep (roundKey keys direction j) state) v

theorem roundPrefix_zero (keys : DesSchedule) (direction : Direction)
    (v : BitVec 32 × BitVec 32) : roundPrefix keys direction 0 v = v := rfl

theorem roundPrefix_succ (keys : DesSchedule) (direction : Direction) (n : Nat)
    (v : BitVec 32 × BitVec 32) :
    roundPrefix keys direction (n + 1) v =
      feistelStep (roundKey keys direction n) (roundPrefix keys direction n v) := by
  unfold roundPrefix
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]

theorem desCore_roundPrefix (keys : DesSchedule) (direction : Direction)
    (v : BitVec 64) :
    desCore keys direction v =
      let halves := roundPrefix keys direction 16 ((v >>> 32).setWidth 32, v.setWidth 32)
      halves.2 ++ halves.1 := rfl

end VG.Proof.TripleDes

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.Round`. -/
section

namespace VG.Proof.TripleDes

open VG.Spec.TripleDes

def substitutionPrefix (x : BitVec 48) (n : Nat) : BitVec 32 :=
  (List.range n).foldl (fun out i =>
    (out <<< 4) ||| (sBox i ((x >>> (6 * (7 - i))).setWidth 6)).zeroExtend 32) 0

theorem substitutionPrefix_bit (x : BitVec 48) (n : Nat) (hn : n ≤ 8)
    (j : Nat) (hj : j < 32) :
    (substitutionPrefix x n).getLsbD j =
      if j < 4 * n then
        (sBox (n - 1 - j / 4)
          ((x >>> (6 * (7 - (n - 1 - j / 4)))).setWidth 6)).getLsbD (j % 4)
      else false := by
  induction n generalizing j with
  | zero => simp [substitutionPrefix]
  | succ n ih =>
    unfold substitutionPrefix
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, BitVec.getLsbD_or,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, hj, decide_true, Bool.true_and]
    by_cases hlow : j < 4
    · have hdiv : j / 4 = 0 := Nat.div_eq_of_lt hlow
      have hmod : j % 4 = j := Nat.mod_eq_of_lt hlow
      have hbound : j < 4 * (n + 1) := by omega
      simp only [hlow, decide_true, Bool.not_true, Bool.false_and, Bool.false_or,
        hbound, ite_true, hdiv, hmod, Nat.sub_zero, Nat.add_sub_cancel]
    · have hj' : j - 4 < 32 := by omega
      have ih' := ih (by omega) (j - 4) hj'
      change ((!decide (j < 4) &&
        (substitutionPrefix x n).getLsbD (j - 4)) ||
        (sBox n ((x >>> (6 * (7 - n))).setWidth 6)).getLsbD j) = _
      rw [BitVec.getLsbD_of_ge (sBox n ((x >>> (6 * (7 - n))).setWidth 6)) j (by omega), ih']
      simp only [hlow, decide_false, Bool.not_false, Bool.true_and, Bool.or_false]
      have hdiv : (j - 4) / 4 = j / 4 - 1 := by omega
      have hmod : (j - 4) % 4 = j % 4 := by omega
      have hidx : n - 1 - (j - 4) / 4 = n + 1 - 1 - j / 4 := by omega
      have hbound : (j - 4 < 4 * n) ↔ (j < 4 * (n + 1)) := by omega
      simp only [hbound, hidx, hmod]

theorem roundFunction_bit (r : BitVec 32) (k : BitVec 48) (j : Nat) (hj : j < 32) :
    (roundFunction r k).getLsbD j =
      let t := 32 - p.getD (31 - j) 1
      (sBox (7 - t / 4)
        (((permute expansion r ^^^ k) >>> (6 * (7 - (7 - t / 4)))).setWidth 6)).getLsbD
        (t % 4) := by
  have bounds : ∀ j < 32, 1 ≤ p.getD j 1 ∧ p.getD j 1 ≤ 32 := by decide +kernel
  obtain ⟨lo, hi⟩ := bounds (31 - j) (by omega)
  have ht : 32 - p.getD (31 - j) 1 < 32 := by omega
  unfold roundFunction
  rw [permute_bit _ _ (by decide) j hj]
  change (substitutionPrefix (permute expansion r ^^^ k) 8).getLsbD
    (32 - p.getD (32 - 1 - j) 1) = _
  rw [substitutionPrefix_bit _ 8 (by decide) _ ht]
  simp only [ht, ite_true]

end VG.Proof.TripleDes

end
