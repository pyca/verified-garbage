module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Top
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.ExportEncoding
import VerifiedGarbage.Proof.Dsa.X86.ABIResources

/-! # Functional correctness of `vg_rsa_private_crt_precomputed` on x86

What `privateCrtPrecomputedContract` gives at the entry: each factor's
cached `R² mod p` in `pre` (`preR2_of`, from its words, `val32_of_wordsAt`)
and apart from the output (`preOut_of`); `bodyP_ok`: the modulus checked,
then `sizedPre_ok` or the failure; `operationP_ok` and `correctP`, as
`operation_ok` and `correct` are of `vg_rsa_private_crt`.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

open VG VG.X86 VG.X86.Spill VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.Crt (componentValue componentArguments accepted outputValue specResult specResult_eq)
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Impl.Bignum.X86.CrtRt (preArg)

theorem wordsAt_append' (m : Mem) (p : Addr) (a b : Nat) :
    Spec.Rsa.wordsAt m p (a + b) =
      Spec.Rsa.wordsAt m p a ++ Spec.Rsa.wordsAt m (p + BitVec.ofNat 64 (8 * a)) b := by
  rw [Spec.Rsa.wordsAt, Spec.Rsa.wordsAt, Spec.Rsa.wordsAt, List.range_add, List.map_append, List.map_map]
  refine congrArg _ (List.map_congr_left fun i _ => ?_)
  simp only [Function.comp_apply]
  rw [Offset.add_add, Nat.mul_add]

/-- The number of `2 w` words of 32 bits at `p + d` whose `w` words of 64 bits are `toWords V w`. -/
theorem val32_of_wordsAt {m : Mem} {p : Addr} {d w V : Nat}
    (h : Spec.Rsa.wordsAt m (p + BitVec.ofNat 64 d) w = Spec.Rsa.toWords V w) (hV : V < 2 ^ (64 * w)) :
    val32 m p d (2 * w) = V := by
  rw [← VG.Proof.Bignum.read_eq_val32, show 4 * (2 * w) = 8 * w by omega, VG.Proof.Bignum.read_eq_wv,
    ← Nat.mod_eq_of_lt hV]
  refine VG.Proof.Bignum.wv_of_words fun i hi => ?_
  have := congrArg (fun l => l[i]?) h
  simp only [Spec.Rsa.wordsAt, Spec.Rsa.toWords, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.some.injEq] at this
  show (m.readW (off p (d + 8 * i)) 64).toNat = _
  rw [show off p (d + 8 * i) = p + BitVec.ofNat 64 d + BitVec.ofNat 64 (8 * i) by
    rw [Offset.add_add], this, BitVec.toNat_ofNat]

theorem toWords_length' (x w : Nat) : (Spec.Rsa.toWords x w).length = w := by
  simp only [Spec.Rsa.toWords, List.length_map, List.length_range]

theorem wordsAt_length' (m : Mem) (p : Addr) (w : Nat) : (Spec.Rsa.wordsAt m p w).length = w := by
  simp only [Spec.Rsa.wordsAt, List.length_map, List.length_range]

section
variable {s : State}

/-- The first `n` bytes of `pre`. -/
theorem pre_sub (n k : Nat) (h : n ≤ k) (P : Addr) :
    Region.Sub ⟨P, n⟩ ⟨P, k⟩ := by
  have := Offset.sub P (d := 0) (n := n) (e := 0) (k := k) (Nat.zero_le _) (by omega)
  simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this

/-- Factor `i`'s cached value, from the contract's `pre`, for a factor above one. -/
theorem preR2_of (A : CrtABIP s) {i : Nat} (hi : i ≤ 1)
    (hp : 1 < componentValue s.mem (arg s) (6 + 2 * i)) :
    PreR2 s (argumentPointer s 16) ((arg s 17).toNat * 8) (arg s 3).toNat (arg s) i
      (componentValue s.mem (arg s) (6 + 2 * i)) := by
  have lv := A.lengths
  have pl := A.pLength
  have ql := A.qLength
  have pp := A.pPositive
  have qp := A.qPositive
  have plen := A.preLength
  have pb := A.preBound
  unfold Spec.Rsa.lenValid at lv
  have pwq : preOff (arg s) i + 8 * preW (arg s) i ≤ (arg s 19).toNat * 8 := by
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp [preOff, preW] <;> omega
  have below' : Region.Disjoint (below (s.gpr .esp) 96) ⟨argumentPointer s 18, (arg s 19).toNat * 8⟩ := by
    simp only [below]; rw [VG.X86.Taint.sub_setWidth A.stackLow]; exact A.belowPre
  have sub := pre_sub _ _ pwq (argumentPointer s 18)
  refine ⟨⟨VG.Proof.Dsa.X86.stackArgument_of (count := 20) (by have := A.stackBound; omega) (by decide)
      (by rw [A.rd, A.wr]; simp) A.scratchArgs.symm, rfl⟩, hi, ?_, ?_, by omega, by omega,
    ⟨⟨argumentPointer s 18, (arg s 19).toNat * 8⟩, by rw [A.rd]; simp, ?_⟩, by simp only [preArg]; omega,
    A.scratchPre.symm.sub_left sub, ?_,
    by have := A.stackBound; omega, below'.symm.sub_left sub⟩
  · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp only [Nat.reduceMul, Nat.reduceAdd] <;> omega
  · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp only [Nat.reduceMul, Nat.reduceAdd] <;> omega
  · have := Offset.contains_base (argumentPointer s 18) (d := 0) (n := preOff (arg s) i + 8 * preW (arg s) i)
      (k := (arg s 19).toNat * 8) (by omega) (by decide)
    simp only [BitVec.add_zero] at this
    exact this
  · have W := A.preValue
    rw [plen, wordsAt_append'] at W
    obtain ⟨E1, E2⟩ := List.append_inj W (by
      rw [wordsAt_length', Spec.Rsa.primeR2, toWords_length', VG.Proof.Bignum.bytesAt_length])
    simp only [Spec.Rsa.primeR2, VG.Proof.Bignum.bytesAt_length] at E1 E2
    have lt : ∀ j, componentValue s.mem (arg s) j < 2 ^ (64 * Spec.Rsa.primeWords (arg s (j + 1)).toNat) := by
      intro j
      refine Nat.lt_of_lt_of_le (comp_lt s.mem (arg s) j) (Nat.pow_le_pow_right (by decide) ?_)
      simp only [Spec.Rsa.primeWords, Spec.Rsa.modulusWords]; omega
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · have E1' : Spec.Rsa.wordsAt s.mem (argumentPointer s 18 + BitVec.ofNat 64 0)
          (Spec.Rsa.primeWords (arg s 7).toNat) = Spec.Rsa.toWords
            (2 ^ (128 * Spec.Rsa.primeWords (arg s 7).toNat) % componentValue s.mem (arg s) 6)
            (Spec.Rsa.primeWords (arg s 7).toNat) := by
        rw [show argumentPointer s 18 + BitVec.ofNat 64 0 = argumentPointer s 18 from BitVec.add_zero _]
        exact E1
      exact val32_of_wordsAt (p := argumentPointer s 18) (d := 0) E1' (Nat.lt_trans (Nat.mod_lt _ (by omega)) (lt 6))
    · exact val32_of_wordsAt (p := argumentPointer s 18) (d := 8 * Spec.Rsa.primeWords (arg s 7).toNat) E2
        (Nat.lt_trans (Nat.mod_lt _ (by omega)) (lt 8))

/-- Argument 18 and factor `i`'s cached value, apart from the output. -/
theorem preOut_of (A : CrtABIP s) {i : Nat} (hi : i ≤ 1) : PreOut s (arg s) (arg s 3).toNat i := by
  have plen := A.preLength
  have pwq : preOff (arg s) i + 8 * preW (arg s) i ≤ (arg s 19).toNat * 8 := by
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp [preOff, preW] <;> omega
  have pb := A.preBound
  have ol := A.outLength
  have O : VG.Proof.Dsa.X86.StackArgument s (argumentPointer s 0) (arg s 1).toNat preArg :=
    VG.Proof.Dsa.X86.stackArgument_of (count := 20) (by have := A.stackBound; omega) (by decide) (by rw [A.rd, A.wr]; simp)
      A.outArgs.symm
  refine ⟨?_, ?_⟩
  · rw [← ol]; exact O.apart
  · rw [← ol]; exact A.outPre.symm.sub_left (pre_sub _ _ pwq _)

end

end VG.Proof.Bignum.X86.CrtRt
