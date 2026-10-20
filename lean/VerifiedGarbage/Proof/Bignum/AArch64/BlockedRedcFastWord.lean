module

public import VerifiedGarbage.Impl.Bignum.AArch64.BlockedRedcFast
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcWord
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcFastMath
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

@[expose] public section
namespace VG.Proof.Bignum.AArch64.BlockedRedcFast
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.BlockedRedc

/-- A virtual low product models the omitted multiplication even for an
invalid inverse. The actual high halves are still computed from the modulus. -/
def lowProduct (s : State) (n0 : Word) (i : Nat) : Word :=
  if i = 0 then -s.gpr .x19 else BlockedRedc.lowProduct s n0 i

theorem lowChain_ok {s : State} {B : Addr} {Z eN : Nat}
    (hs : Scr s B Z) (h17 : s.gpr .x17 = off B eN) (hN : eN + 8 ≤ Z) :
    WP isa (.block VG.Impl.Bignum.AArch64.BlockedRedcFast.lowChain) s fun t =>
      (t.c = chainCarry (accumulator s) (lowProduct s (word s.mem B eN)) false 8 ∧
       (∀ i, 0 < i → i < 8 → t.gpr VG.Impl.Bignum.AArch64.BlockedRedc.aa[i]! =
         addCarry (accumulator s i) (lowProduct s (word s.mem B eN) i)
           (chainCarry (accumulator s) (lowProduct s (word s.mem B eN)) false i)) ∧
       (∀ i < 4, t.gpr VG.Impl.Bignum.AArch64.BlockedRedc.tt[i]! =
         highProduct s (word s.mem B eN) i) ∧ t.mem = s.mem) ∧
      Keep (VG.Impl.Bignum.AArch64.BlockedRedc.aa ++
        VG.Impl.Bignum.AArch64.BlockedRedc.tt) s t := by
  refine WP.keep (VG.Impl.Bignum.AArch64.BlockedRedc.aa ++
    VG.Impl.Bignum.AArch64.BlockedRedc.tt) ?_ (by decide) (by decide) (by decide +kernel)
  have h4 : List.range 4 = [0, 1, 2, 3] := rfl
  have h7 : List.range 7 = [0, 1, 2, 3, 4, 5, 6] := rfl
  brun [h4, h7, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.cons_append, List.nil_append,
    VG.Impl.Bignum.AArch64.BlockedRedcFast.lowChain,
    VG.Impl.Bignum.AArch64.BlockedRedc.cancelLowChain,
    VG.Impl.Bignum.AArch64.BlockedRedc.product,
    VG.Impl.Bignum.AArch64.BlockedRedc.aa,
    VG.Impl.Bignum.AArch64.BlockedRedc.nn,
    VG.Impl.Bignum.AArch64.BlockedRedc.tt, h17, hs.ld hN]
  refine ⟨?_, ?_, ?_⟩
  · simp only [chainCarry, accumulator, lowProduct, BlockedRedc.lowProduct, operand,
      List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, ↓reduceIte,
      VG.Proof.Ed25519.Word64.carryOut, reduceCtorEq,
      List.getElem!_cons_zero, List.getElem!_cons_succ,
      Nat.reduceAdd, Nat.reduceSub]
    rw [canceled_flag]
  · intro i hi0 hi
    rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [chainCarry, accumulator, lowProduct, BlockedRedc.lowProduct, operand,
      List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, List.getElem!_cons_zero, List.getElem!_cons_succ,
      ↓reduceIte, addCarry,
      VG.Proof.Ed25519.Word64.carryOut, reduceCtorEq,
      List.getElem!_cons_zero, List.getElem!_cons_succ,
      Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod]
    all_goals rw [canceled_flag]
  · intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
    all_goals rfl

/-- The omitted output word is represented only in the proof. -/
def zeroLow (s : State) : State := s.write .x .x19 0

theorem zeroLow_shifted (s : State) : shifted (zeroLow s) = shifted s := by
  funext i
  simp only [shifted, zeroLow, VG.AArch64.RegUpd.gpr_write, reduceCtorEq, ↓reduceIte]

theorem zeroLow_accumulator (s : State) : accumulator (zeroLow s) =
    fun i => if i = 0 then 0 else accumulator s i := by
  funext i
  cases i with
  | zero => rfl
  | succ i =>
    simp only [accumulator, zeroLow, VG.AArch64.RegUpd.gpr_write, reduceCtorEq, ↓reduceIte,
      List.getD_eq_getElem?_getD, List.getElem?_cons_succ]

theorem zeroLow_chain_value {s t : State} {n0 : Word}
    (hc : t.c = chainCarry (accumulator s) (lowProduct s n0) false 8)
    (hv : ∀ i, 0 < i → i < 8 → t.gpr VG.Impl.Bignum.AArch64.BlockedRedc.aa[i]! =
      addCarry (accumulator s i) (lowProduct s n0 i)
        (chainCarry (accumulator s) (lowProduct s n0) false i)) :
    blockValue (accumulator (zeroLow t)) + (2 ^ 64) ^ 8 * t.c.toNat =
      blockValue (accumulator s) + blockValue (lowProduct s n0) := by
  have hz : ∀ i < 8, (zeroLow t).gpr VG.Impl.Bignum.AArch64.BlockedRedc.aa[i]! =
      addCarry (accumulator s i) (lowProduct s n0 i)
        (chainCarry (accumulator s) (lowProduct s n0) false i) := by
    intro i hi
    by_cases hi0 : i = 0
    · subst i
      exact (canceled_sum (s.gpr .x19)).symm
    · have hr : VG.Impl.Bignum.AArch64.BlockedRedc.aa[i]! ≠ .x19 := by
        rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals decide
      simpa only [zeroLow, VG.AArch64.RegUpd.gpr_write, hr, ↓reduceIte] using hv i (by omega) hi
  have h := chain_result_value (t := zeroLow t) hc hz
  exact h.trans (Nat.add_zero _)

end VG.Proof.Bignum.AArch64.BlockedRedcFast
