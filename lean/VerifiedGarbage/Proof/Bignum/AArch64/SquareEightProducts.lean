module

public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Impl.Bignum.AArch64.SquareEight
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Ed25519.Word64
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.TCB.AArch64.Isa

@[expose] public section
namespace VG.Proof.Bignum.AArch64.SquareEight
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.AArch64.SquareEight

theorem multiplyPair_ok (s : State) (lo hi a b : Reg)
    (hd : lo ≠ hi) (ha : a ≠ lo) (hb : b ≠ lo) :
    WP isa (.block [.mul .x lo a b, .umulh hi a b]) s fun t =>
      (t.gpr lo = s.gpr a * s.gpr b ∧
        t.gpr hi = BitVec.ofNat 64 ((s.gpr a).toNat * (s.gpr b).toNat / 2 ^ 64) ∧
        t.mem = s.mem) ∧ Keep [lo, hi] s t := by
  refine WP.keep [lo, hi] ?_ (by simp [writesOnly, Code.allInstrs, dsts, dstOf, Option.toList]) rfl rfl
  brun [hd, ha, hb]

theorem productWord_value {s t : State} {lo hi a b : Reg}
    (hl : t.gpr lo = s.gpr a * s.gpr b)
    (hh : t.gpr hi = BitVec.ofNat 64 ((s.gpr a).toNat * (s.gpr b).toNat / 2 ^ 64)) :
    (t.gpr lo).toNat + 2 ^ 64 * (t.gpr hi).toNat = (s.gpr a).toNat * (s.gpr b).toNat := by
  rw [hl, hh]
  exact mul_toNat _ _

/-- Scheduling uses two disjoint product pairs and never clobbers an input. -/
theorem registers_disjoint : ∀ (j : Fin 2) (i : Fin 8),
    lows[j.val]! ≠ highs[j.val]! ∧ inputs[i.val]! ≠ lows[j.val]! ∧ inputs[i.val]! ≠ highs[j.val]! ∧
      lows[j.val]! ≠ .x19 ∧ lows[j.val]! ≠ .x20 ∧ lows[j.val]! ≠ .x21 ∧
      highs[j.val]! ≠ .x19 ∧ highs[j.val]! ≠ .x20 ∧ highs[j.val]! ≠ .x21 := by decide

theorem pair_bounds : ∀ k < 15, ∀ j < (pairs k).length,
    (pairs k)[j]!.1 < (pairs k)[j]!.2 ∧ (pairs k)[j]!.2 < 8 ∧
      (pairs k)[j]!.1 + (pairs k)[j]!.2 = k := by decide

theorem pairs_length : ∀ k < 15, (pairs k).length ≤ 4 := by decide

def PairReady (s : State) (ps : List (Nat × Nat)) (j : Nat) (t : State) : Prop :=
 t.gpr lows[j % 2]! = s.gpr inputs[ps[j]!.1]! * s.gpr inputs[ps[j]!.2]! ∧
 t.gpr highs[j % 2]! = BitVec.ofNat 64
   ((s.gpr inputs[ps[j]!.1]!).toNat * (s.gpr inputs[ps[j]!.2]!).toNat / 2 ^ 64)

def productRegs (j : Nat) : List Reg := [lows[j % 2]!, highs[j % 2]!]

theorem product_ok {s : State} {ps : List (Nat × Nat)} {j : Nat}
    (hj : j < ps.length) (ha : ps[j]!.1 < 8) (hb : ps[j]!.2 < 8) :
    WP isa (.block (product ps j)) s fun t =>
      (PairReady s ps j t ∧ t.mem = s.mem) ∧ Keep (productRegs j) s t := by
  have hl := registers_disjoint ⟨j % 2, by omega⟩ ⟨ps[j]!.1, ha⟩
  have hr := registers_disjoint ⟨j % 2, by omega⟩ ⟨ps[j]!.2, hb⟩
  unfold product
  rw [ite_eq_left hj]
  exact WP.mono (multiplyPair_ok s _ _ _ _ hl.1 hl.2.1 hr.2.1)
    fun _ ⟨⟨hlo, hhi, hm⟩, hk⟩ => ⟨⟨⟨hlo, hhi⟩, hm⟩, hk⟩

theorem product_optional_ok {s : State} {ps : List (Nat × Nat)} {j : Nat}
    (hps : ∀ i < ps.length, ps[i]!.1 < 8 ∧ ps[i]!.2 < 8) :
    WP isa (.block (product ps j)) s fun t =>
      ((j < ps.length → PairReady s ps j t) ∧ t.mem = s.mem) ∧ Keep (productRegs j) s t := by
  by_cases hj : j < ps.length
  · exact WP.mono (product_ok hj (hps j hj).1 (hps j hj).2)
      fun _ ⟨⟨hr, hm⟩, hk⟩ => ⟨⟨fun _ => hr, hm⟩, hk⟩
  · rw [product, ite_eq_right hj]
    exact WP.block_nil ⟨⟨fun h => False.elim (hj h), rfl⟩, Keep.refl _ _⟩

abbrev workRegs : List Reg := [.x19, .x20, .x21, .x13, .x28, .x14, .x30]

theorem input_not_work : ∀ (i : Fin 8), inputs[i.val]! ∉ workRegs := by decide

theorem products_in_work : ∀ (j : Fin 2), lows[j.val]! ∈ workRegs ∧ highs[j.val]! ∈ workRegs := by decide

theorem productRegs_subset (j : Nat) : ∀ r ∈ productRegs j, r ∈ workRegs := by
  intro r hr
  have h := products_in_work ⟨j % 2, by omega⟩
  simp only [productRegs, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1
  · exact h.2

theorem other_product_preserved : ∀ (j i : Fin 2), j ≠ i →
    lows[j.val]! ∉ [lows[i.val]!, highs[i.val]!] ∧
      highs[j.val]! ∉ [lows[i.val]!, highs[i.val]!] := by decide

theorem inputs_keep {s t : State} (hk : Keep workRegs s t) :
    ∀ i < 8, t.gpr inputs[i]! = s.gpr inputs[i]! := fun i hi =>
  hk.gpr _ (input_not_work ⟨i, hi⟩)

end VG.Proof.Bignum.AArch64.SquareEight
