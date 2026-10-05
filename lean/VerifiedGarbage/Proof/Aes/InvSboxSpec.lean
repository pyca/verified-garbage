import VerifiedGarbage.Spec.Aes
import VerifiedGarbage.Proof.Framework.Bitslice.Table
import VerifiedGarbage.Proof.Framework.PowLit

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.SboxSpec`. -/
section

/-!
# The specification's S-box, on all 256 inputs at once

Evaluating `Spec.Aes.sbox` in the kernel takes about 0.1 s per input. Here
the specification's own computation (the inverse as `b²⁵⁴` by square and
multiply with `mul`, then the affine transformation) is transcribed on
*truth tables*: a byte is eight natural numbers, the `j`-th holding bit `j`
of the byte on each of 256 inputs, so that one evaluation computes the
S-box of every byte. `row_sboxT` proves the transcription right, input by
input; the kernel then evaluates it on the 256 bytes at once (in each
target's proof of its S-box, e.g. `Proof/Aes/X86/Sbox.lean`) in a fraction
of a second.
-/

namespace VG.Proof.Aes

open VG.Spec.Aes VG.Bitslice

/-- The table that is true on every one of the 256 inputs. -/
def ONES : Nat := 2 ^ 256 - 1

theorem testBit_ONES (c : Nat) : ONES.testBit c = decide (c < 256) := Nat.testBit_two_pow_sub_one _ _

theorem testBit_ite_ONES (b : Bool) (c : Nat) :
    (if b = true then VG.Proof.Aes.ONES else 0).testBit c = (b && decide (c < 256)) := by
  cases b <;> simp [VG.Proof.Aes.testBit_ONES]

/-- Bytes as eight truth tables. -/
def xorT (A B : List Nat) : List Nat := List.zipWith (· ^^^ ·) A B
def andT (m : Nat) (A : List Nat) : List Nat := A.map (m &&& ·)
/-- `xtimes`: a shift left by one bit, XOR `{1b}` (bits 0, 1, 3, 4) if bit 7 was set. -/
def xtT (A : List Nat) : List Nat :=
  let a7 := A.getD 7 0
  [a7, A.getD 0 0 ^^^ a7, A.getD 1 0, A.getD 2 0 ^^^ a7, A.getD 3 0 ^^^ a7, A.getD 4 0,
    A.getD 5 0, A.getD 6 0]
def zeroT : List Nat := List.replicate 8 0
def oneT : List Nat := VG.Proof.Aes.ONES :: List.replicate 7 0

/-- `mul`, as the specification computes it. -/
def mulT (B C : List Nat) : List Nat :=
  (List.range 8).foldl (fun acc i => VG.Proof.Aes.xorT acc (VG.Proof.Aes.andT (B.getD i 0) (Nat.repeat VG.Proof.Aes.xtT i C))) VG.Proof.Aes.zeroT

/-- `pow`, as the specification computes it. -/
def powT (B : List Nat) (n : Nat) : List Nat :=
  ((List.range 8).foldl (fun (acc, sq) i => (if n.testBit i then VG.Proof.Aes.mulT acc sq else acc, VG.Proof.Aes.mulT sq sq))
    (VG.Proof.Aes.oneT, B)).1

/-- The affine transformation of `sbox`. -/
def affT (A : List Nat) : List Nat := (List.range 8).map fun i =>
  A.getD i 0 ^^^ A.getD ((i + 4) % 8) 0 ^^^ A.getD ((i + 5) % 8) 0 ^^^ A.getD ((i + 6) % 8) 0 ^^^
    A.getD ((i + 7) % 8) 0 ^^^ (if (0x63 : Nat).testBit i then VG.Proof.Aes.ONES else 0)

def sboxT (A : List Nat) : List Nat := VG.Proof.Aes.affT (VG.Proof.Aes.powT A 254)

/-- Row `c` of eight truth tables: the byte whose bit `j` is row `c` of table `j`. -/
def row (T : List Nat) (c : Nat) : Byte := ofBits 8 fun j => (T.getD j 0).testBit c

theorem getLsbD_row (T : List Nat) (c : Nat) {j : Nat} (hj : j < 8) :
    (VG.Proof.Aes.row T c).getLsbD j = (T.getD j 0).testBit c := by
  rw [VG.Proof.Aes.row, getLsbD_ofBits]; simp [hj]

@[simp] theorem getElem_row (T : List Nat) (c : Nat) {j : Nat} (hj : j < 8) :
    (VG.Proof.Aes.row T c)[j] = (T.getD j 0).testBit c := by
  rw [← BitVec.getLsbD_eq_getElem, VG.Proof.Aes.getLsbD_row _ _ hj]

/-! ## Lengths -/

theorem length_xorT {A B : List Nat} (hA : A.length = 8) (hB : B.length = 8) :
    (VG.Proof.Aes.xorT A B).length = 8 := by simp [VG.Proof.Aes.xorT, hA, hB]

theorem length_andT {m : Nat} {A : List Nat} (hA : A.length = 8) : (VG.Proof.Aes.andT m A).length = 8 := by
  simp [VG.Proof.Aes.andT, hA]

theorem length_xtT (A : List Nat) : (VG.Proof.Aes.xtT A).length = 8 := rfl

theorem length_repeat_xtT {A : List Nat} (hA : A.length = 8) (i : Nat) :
    (Nat.repeat VG.Proof.Aes.xtT i A).length = 8 := by
  cases i with
  | zero => exact hA
  | succ i => exact VG.Proof.Aes.length_xtT _

theorem length_mulT_aux (B C : List Nat) (l : List Nat) (acc : List Nat) (hacc : acc.length = 8)
    (hC : C.length = 8) :
    (l.foldl (fun acc i => VG.Proof.Aes.xorT acc (VG.Proof.Aes.andT (B.getD i 0) (Nat.repeat VG.Proof.Aes.xtT i C))) acc).length = 8 := by
  induction l generalizing acc with
  | nil => exact hacc
  | cons i l ih =>
    exact ih _ (VG.Proof.Aes.length_xorT hacc (VG.Proof.Aes.length_andT (VG.Proof.Aes.length_repeat_xtT hC i)))

theorem length_mulT {B C : List Nat} (hC : C.length = 8) : (VG.Proof.Aes.mulT B C).length = 8 :=
  VG.Proof.Aes.length_mulT_aux B C _ VG.Proof.Aes.zeroT rfl hC

/-! ## Rows -/

theorem row_ext {T : List Nat} {c : Nat} {b : Byte}
    (h : ∀ j < 8, (T.getD j 0).testBit c = b.getLsbD j) : VG.Proof.Aes.row T c = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [VG.Proof.Aes.getLsbD_row _ _ hj, h j hj]

theorem row_xorT {A B : List Nat} (hA : A.length = 8) (hB : B.length = 8) (c : Nat) :
    VG.Proof.Aes.row (VG.Proof.Aes.xorT A B) c = VG.Proof.Aes.row A c ^^^ VG.Proof.Aes.row B c := by
  refine VG.Proof.Aes.row_ext fun j hj => ?_
  rw [BitVec.getLsbD_xor, VG.Proof.Aes.getLsbD_row _ _ hj, VG.Proof.Aes.getLsbD_row _ _ hj, ← Nat.testBit_xor]
  congr 1
  simp only [VG.Proof.Aes.xorT, List.getD_eq_getElem?_getD, List.getElem?_zipWith]
  rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)]
  simp

theorem row_andT (m : Nat) (A : List Nat) (c : Nat) :
    VG.Proof.Aes.row (VG.Proof.Aes.andT m A) c = if m.testBit c then VG.Proof.Aes.row A c else 0 := by
  refine VG.Proof.Aes.row_ext fun j hj => ?_
  have : (VG.Proof.Aes.andT m A).getD j 0 = m &&& A.getD j 0 := by
    simp only [VG.Proof.Aes.andT, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases A[j]? <;> simp
  rw [this, Nat.testBit_and]
  split
  · rename_i h; rw [h, VG.Proof.Aes.getLsbD_row _ _ hj]; rfl
  · rename_i h; simp at h; simp [h]

theorem getLsbD_xtimes (b : Byte) {j : Nat} (hj : j < 8) :
    (xtimes b).getLsbD j =
      ((decide (0 < j) && b.getLsbD (j - 1)) ^^ (b.getLsbD 7 && (0x1b : Byte).getLsbD j)) := by
  simp only [xtimes, BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft, BitVec.msb_eq_getLsbD_last]
  have : decide (j < 8) = true := by simp [hj]
  rw [this]
  cases b.getLsbD (8 - 1) <;> simp <;> rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;> first | omega | simp

theorem row_xtT (A : List Nat) (c : Nat) : VG.Proof.Aes.row (VG.Proof.Aes.xtT A) c = xtimes (VG.Proof.Aes.row A c) := by
  refine VG.Proof.Aes.row_ext fun j hj => ?_
  rw [VG.Proof.Aes.getLsbD_xtimes _ hj, VG.Proof.Aes.getLsbD_row _ _ (show 7 < 8 by omega)]
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;> first | omega | simp [VG.Proof.Aes.xtT, Nat.testBit_xor]

theorem row_repeat_xtT (A : List Nat) (c i : Nat) :
    VG.Proof.Aes.row (Nat.repeat VG.Proof.Aes.xtT i A) c = Nat.repeat xtimes i (VG.Proof.Aes.row A c) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [Nat.repeat]
    rw [VG.Proof.Aes.row_xtT, ih]

theorem row_mulT_aux (B C : List Nat) (hC : C.length = 8) (c : Nat) (l : List Nat)
    (hl : ∀ i ∈ l, i < 8) (acc : List Nat) (hacc : acc.length = 8) :
    VG.Proof.Aes.row (l.foldl (fun acc i => VG.Proof.Aes.xorT acc (VG.Proof.Aes.andT (B.getD i 0) (Nat.repeat VG.Proof.Aes.xtT i C))) acc) c =
      l.foldl (fun acc i => if (VG.Proof.Aes.row B c).getLsbD i then acc ^^^ Nat.repeat xtimes i (VG.Proof.Aes.row C c)
        else acc) (VG.Proof.Aes.row acc c) := by
  induction l generalizing acc with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldl_cons]
    rw [ih (fun i hi => hl i (by simp [hi])) _
      (VG.Proof.Aes.length_xorT hacc (VG.Proof.Aes.length_andT (VG.Proof.Aes.length_repeat_xtT hC i)))]
    congr 1
    rw [VG.Proof.Aes.row_xorT hacc (VG.Proof.Aes.length_andT (VG.Proof.Aes.length_repeat_xtT hC i)), VG.Proof.Aes.row_andT, VG.Proof.Aes.row_repeat_xtT,
      VG.Proof.Aes.getLsbD_row _ _ (hl i (by simp))]
    split <;> simp

theorem row_zeroT (c : Nat) : VG.Proof.Aes.row VG.Proof.Aes.zeroT c = 0 := by
  refine VG.Proof.Aes.row_ext fun j hj => ?_
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;> first | omega | simp [VG.Proof.Aes.zeroT]

theorem row_mulT {B C : List Nat} (hC : C.length = 8) (c : Nat) :
    VG.Proof.Aes.row (VG.Proof.Aes.mulT B C) c = mul (VG.Proof.Aes.row B c) (VG.Proof.Aes.row C c) := by
  rw [VG.Proof.Aes.mulT, VG.Proof.Aes.row_mulT_aux B C hC c _ (fun i hi => by simpa using hi) VG.Proof.Aes.zeroT rfl, VG.Proof.Aes.row_zeroT]
  rfl

theorem row_oneT {c : Nat} (hc : c < 256) : VG.Proof.Aes.row VG.Proof.Aes.oneT c = 1 := by
  refine VG.Proof.Aes.row_ext fun j hj => ?_
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;> first | omega |
    simp [VG.Proof.Aes.oneT, List.getD_eq_getElem?_getD, VG.Proof.Aes.testBit_ONES, hc]

theorem row_powT_aux (n c : Nat) (l : List Nat) (acc sq : List Nat) (hacc : acc.length = 8)
    (hsq : sq.length = 8) :
    (VG.Proof.Aes.row (l.foldl (fun (acc, sq) i => (if n.testBit i then VG.Proof.Aes.mulT acc sq else acc, VG.Proof.Aes.mulT sq sq))
        (acc, sq)).1 c,
      VG.Proof.Aes.row (l.foldl (fun (acc, sq) i => (if n.testBit i then VG.Proof.Aes.mulT acc sq else acc, VG.Proof.Aes.mulT sq sq))
        (acc, sq)).2 c) =
    (l.foldl (fun (acc, sq) i => (if n.testBit i then mul acc sq else acc, mul sq sq))
      (VG.Proof.Aes.row acc c, VG.Proof.Aes.row sq c)) ∧
    (l.foldl (fun (acc, sq) i => (if n.testBit i then VG.Proof.Aes.mulT acc sq else acc, VG.Proof.Aes.mulT sq sq))
        (acc, sq)).1.length = 8 ∧
    (l.foldl (fun (acc, sq) i => (if n.testBit i then VG.Proof.Aes.mulT acc sq else acc, VG.Proof.Aes.mulT sq sq))
        (acc, sq)).2.length = 8 := by
  induction l generalizing acc sq with
  | nil => exact ⟨rfl, hacc, hsq⟩
  | cons i l ih =>
    simp only [List.foldl_cons]
    have h1 : (if n.testBit i then VG.Proof.Aes.mulT acc sq else acc).length = 8 := by
      split
      · exact VG.Proof.Aes.length_mulT hsq
      · exact hacc
    obtain ⟨e, l1, l2⟩ := ih _ _ h1 (VG.Proof.Aes.length_mulT hsq)
    refine ⟨?_, l1, l2⟩
    rw [e]
    congr 2
    · split <;> simp [VG.Proof.Aes.row_mulT hsq]
    · exact VG.Proof.Aes.row_mulT hsq c

theorem row_powT {B : List Nat} (hB : B.length = 8) (n : Nat) {c : Nat} (hc : c < 256) :
    VG.Proof.Aes.row (VG.Proof.Aes.powT B n) c = pow (VG.Proof.Aes.row B c) n := by
  have := (VG.Proof.Aes.row_powT_aux n c (List.range 8) VG.Proof.Aes.oneT B rfl hB).1
  simp only [VG.Proof.Aes.powT, pow]
  rw [← VG.Proof.Aes.row_oneT hc]
  exact congrArg Prod.fst this

/-- The affine transformation of `sbox` (its definition after `inv`). -/
def aff (b : Byte) : Byte :=
  let c : Byte := 0x63
  let bit (i : Nat) : Bool :=
    b.getLsbD i ^^ b.getLsbD ((i + 4) % 8) ^^ b.getLsbD ((i + 5) % 8) ^^
      b.getLsbD ((i + 6) % 8) ^^ b.getLsbD ((i + 7) % 8) ^^ c.getLsbD i
  BitVec.ofNat 8 ((List.range 8).foldl (fun acc i => acc + if bit i then 2 ^ i else 0) 0)

theorem sbox_eq (b : Byte) : sbox b = VG.Proof.Aes.aff (inv b) := rfl

/-- A sum of distinct powers of two. -/
theorem testBit_sum_pow (f : Nat → Bool) (n : Nat) :
    (List.range n).foldl (fun acc i => acc + if f i then 2 ^ i else 0) 0 < 2 ^ n ∧
    ∀ j, ((List.range n).foldl (fun acc i => acc + if f i then 2 ^ i else 0) 0).testBit j =
      (decide (j < n) && f j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨hlt, hbit⟩ := ih
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range n).foldl (fun acc i => acc + if f i then 2 ^ i else 0) 0 = S at hlt hbit
    split
    · rename_i hf
      refine ⟨by rw [Nat.pow_succ]; omega, fun j => ?_⟩
      rw [Nat.add_comm]
      by_cases hj : j < n
      · rw [Nat.testBit_two_pow_add_gt hj, hbit]; simp [hj, show j < n + 1 by omega]
      · by_cases hj' : j = n
        · subst hj'; rw [Nat.testBit_two_pow_add_eq, hbit]; simp [hf]
        · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (show 2 ^ n + S < 2 ^ (n + 1) by
            rw [Nat.pow_succ]; omega) (Nat.pow_le_pow_right (by omega) (by omega)))]
          simp; omega
    · rename_i hf
      refine ⟨by rw [Nat.pow_succ]; omega, fun j => ?_⟩
      rw [Nat.add_zero, hbit]
      by_cases hj : j < n
      · simp [hj, show j < n + 1 by omega]
      · by_cases hj' : j = n
        · subst hj'; simp [hf]
        · simp [hj, show ¬ j < n + 1 by omega]

theorem row_affT (A : List Nat) {c : Nat} (hc : c < 256) :
    VG.Proof.Aes.row (VG.Proof.Aes.affT A) c = VG.Proof.Aes.aff (VG.Proof.Aes.row A c) := by
  refine VG.Proof.Aes.row_ext fun j hj => ?_
  simp only [VG.Proof.Aes.aff, BitVec.getLsbD_ofNat, (VG.Proof.Aes.testBit_sum_pow _ 8).2, hj, decide_true, Bool.true_and]
  simp only [VG.Proof.Aes.affT, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some, Nat.testBit_xor]
  simp only [← List.getD_eq_getElem?_getD]
  rw [VG.Proof.Aes.getLsbD_row _ _ hj, VG.Proof.Aes.getLsbD_row _ _ (Nat.mod_lt _ (by omega)),
    VG.Proof.Aes.getLsbD_row _ _ (Nat.mod_lt _ (by omega)), VG.Proof.Aes.getLsbD_row _ _ (Nat.mod_lt _ (by omega)),
    VG.Proof.Aes.getLsbD_row _ _ (Nat.mod_lt _ (by omega))]
  congr 1
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;> first | omega |
    (simp only [VG.Proof.Aes.testBit_ite_ONES, hc, decide_true, Bool.and_true] <;> decide)

theorem row_sboxT {A : List Nat} (hA : A.length = 8) {c : Nat} (hc : c < 256) :
    VG.Proof.Aes.row (VG.Proof.Aes.sboxT A) c = sbox (VG.Proof.Aes.row A c) := by
  rw [VG.Proof.Aes.sboxT, VG.Proof.Aes.row_affT _ hc, VG.Proof.Aes.row_powT hA _ hc, VG.Proof.Aes.sbox_eq]
  rfl

end VG.Proof.Aes

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.InvSboxSpec`. -/
section

/-!
# The specification's inverse S-box, on all 256 inputs at once

As `SboxSpec.lean` does for the S-box: the specification's computation of
the inverse S-box (the inverse of the affine transformation, then the
multiplicative inverse as `b²⁵⁴`) transcribed on truth tables
(`invSboxT`), and proved right input by input (`row_invSboxT`), so that
the kernel evaluates it on the 256 bytes at once.
-/

namespace VG.Proof.Aes

open VG.Spec.Aes VG.Bitslice

/-- The inverse of the affine transformation (`invAffine`). -/
def invAffT (A : List Nat) : List Nat := (List.range 8).map fun i =>
  A.getD ((i + 2) % 8) 0 ^^^ A.getD ((i + 5) % 8) 0 ^^^ A.getD ((i + 7) % 8) 0 ^^^
    (if (0x05 : Nat).testBit i then VG.Proof.Aes.ONES else 0)

def invSboxT (A : List Nat) : List Nat := VG.Proof.Aes.powT (VG.Proof.Aes.invAffT A) 254

theorem length_invAffT (A : List Nat) : (VG.Proof.Aes.invAffT A).length = 8 := by simp [VG.Proof.Aes.invAffT]

theorem row_invAffT (A : List Nat) {c : Nat} (hc : c < 256) :
    VG.Proof.Aes.row (VG.Proof.Aes.invAffT A) c = invAffine (VG.Proof.Aes.row A c) := by
  refine VG.Proof.Aes.row_ext fun j hj => ?_
  simp only [invAffine, BitVec.getLsbD_ofNat, (VG.Proof.Aes.testBit_sum_pow _ 8).2, hj, decide_true,
    Bool.true_and]
  simp only [VG.Proof.Aes.invAffT, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some, Nat.testBit_xor]
  simp only [← List.getD_eq_getElem?_getD]
  rw [VG.Proof.Aes.getLsbD_row _ _ (Nat.mod_lt _ (by omega)), VG.Proof.Aes.getLsbD_row _ _ (Nat.mod_lt _ (by omega)),
    VG.Proof.Aes.getLsbD_row _ _ (Nat.mod_lt _ (by omega))]
  congr 1
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;> first | omega |
    (simp only [VG.Proof.Aes.testBit_ite_ONES, hc, decide_true, Bool.and_true] <;> decide)

theorem row_invSboxT (A : List Nat) {c : Nat} (hc : c < 256) :
    VG.Proof.Aes.row (VG.Proof.Aes.invSboxT A) c = invSbox (VG.Proof.Aes.row A c) := by
  rw [VG.Proof.Aes.invSboxT, VG.Proof.Aes.row_powT (VG.Proof.Aes.length_invAffT A) _ hc, VG.Proof.Aes.row_invAffT _ hc]
  rfl

end VG.Proof.Aes

end
