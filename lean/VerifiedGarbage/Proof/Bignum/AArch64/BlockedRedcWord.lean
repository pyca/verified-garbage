import VerifiedGarbage.Impl.Bignum.AArch64.BlockedRedc
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcMath

namespace VG.Proof.Bignum.AArch64.BlockedRedc
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)

/-- The modulus block has seven words resident in registers and one in memory. -/
def operand (s : State) (n0 : Word) (i : Nat) : Word :=
  ([n0, s.gpr .x2, s.gpr .x3, s.gpr .x4, s.gpr .x5,
    s.gpr .x6, s.gpr .x9, s.gpr .x11]).getD i 0

def accumulator (s : State) (i : Nat) : Word :=
  ([s.gpr .x19, s.gpr .x20, s.gpr .x21, s.gpr .x22,
    s.gpr .x23, s.gpr .x24, s.gpr .x25, s.gpr .x26]).getD i 0

def lowProduct (s : State) (n0 : Word) (i : Nat) : Word :=
  s.gpr .x27 * operand s n0 i

def highProduct (s : State) (n0 : Word) (i : Nat) : Word :=
  BitVec.ofNat 64 ((s.gpr .x27).toNat * (operand s n0 i).toNat / 2 ^ 64)

theorem lowChain_ok {s : State} {B : Addr} {Z eN : Nat}
    (hs : Scr s B Z) (h17 : s.gpr .x17 = off B eN) (hN : eN + 8 ≤ Z) :
    WP isa (.block VG.Impl.Bignum.AArch64.BlockedRedc.lowChain) s fun t =>
      (t.c = chainCarry (accumulator s) (lowProduct s (word s.mem B eN)) false 8 ∧
       (∀ i < 8, t.gpr VG.Impl.Bignum.AArch64.BlockedRedc.aa[i]! = addCarry (accumulator s i)
         (lowProduct s (word s.mem B eN) i)
         (chainCarry (accumulator s) (lowProduct s (word s.mem B eN)) false i)) ∧
       (∀ i < 4, t.gpr VG.Impl.Bignum.AArch64.BlockedRedc.tt[i]! = highProduct s (word s.mem B eN) i) ∧
       t.mem = s.mem) ∧ Keep (VG.Impl.Bignum.AArch64.BlockedRedc.aa ++ VG.Impl.Bignum.AArch64.BlockedRedc.tt) s t := by
  refine WP.keep (VG.Impl.Bignum.AArch64.BlockedRedc.aa ++ VG.Impl.Bignum.AArch64.BlockedRedc.tt) ?_ (by decide) (by decide) (by decide +kernel)
  have h4 : List.range 4 = [0, 1, 2, 3] := rfl
  have h8 : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl
  brun [h4, h8, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append, List.nil_append, VG.Impl.Bignum.AArch64.BlockedRedc.lowChain, VG.Impl.Bignum.AArch64.BlockedRedc.product, VG.Impl.Bignum.AArch64.BlockedRedc.aa, VG.Impl.Bignum.AArch64.BlockedRedc.nn, VG.Impl.Bignum.AArch64.BlockedRedc.tt, h17, hs.ld hN]
  refine ⟨?_, ?_, ?_⟩
  · rfl
  · intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rfl
  · intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
    all_goals rfl


/-- The low chain shifts one word before the high product halves are added. -/
def shifted (s : State) (i : Nat) : Word :=
  ([s.gpr .x20, s.gpr .x21, s.gpr .x22, s.gpr .x23,
    s.gpr .x24, s.gpr .x25, s.gpr .x26, s.gpr .x1]).getD i 0

/-- Four high halves are already scheduled; the other four are computed
while the high carry chain runs. -/
def highTerms (s : State) (i : Nat) : Word :=
  ([s.gpr .x13, s.gpr .x14, s.gpr .x28, s.gpr .x30,
    highProduct s 0 4, highProduct s 0 5,
    highProduct s 0 6, highProduct s 0 7]).getD i 0

theorem highChain_ok (s : State) :
    WP isa (.block VG.Impl.Bignum.AArch64.BlockedRedc.highChain) s fun t =>
      (t.c = chainCarry (shifted s) (highTerms s) false 8 ∧
       (∀ i < 8, t.gpr VG.Impl.Bignum.AArch64.BlockedRedc.aa[i]! =
         addCarry (shifted s i) (highTerms s i)
           (chainCarry (shifted s) (highTerms s) false i)) ∧
       t.mem = s.mem) ∧
      Keep (VG.Impl.Bignum.AArch64.BlockedRedc.aa ++ VG.Impl.Bignum.AArch64.BlockedRedc.tt) s t := by
  refine WP.keep (VG.Impl.Bignum.AArch64.BlockedRedc.aa ++
    VG.Impl.Bignum.AArch64.BlockedRedc.tt) ?_ (by decide) (by decide) (by decide +kernel)
  have h8 : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl
  brun [h8, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append, List.nil_append,
    VG.Impl.Bignum.AArch64.BlockedRedc.highChain, VG.Impl.Bignum.AArch64.BlockedRedc.product,
    VG.Impl.Bignum.AArch64.BlockedRedc.aa, VG.Impl.Bignum.AArch64.BlockedRedc.nn,
    VG.Impl.Bignum.AArch64.BlockedRedc.tt]
  refine ⟨?_, ?_⟩
  · rfl
  · intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [shifted, highTerms, highProduct, operand, chainCarry, addCarry, VG.Proof.Ed25519.Word64.carryOut,
        List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.getD_some, List.getElem!_cons_zero, List.getElem!_cons_succ,
        off, BitVec.ofNat_add, BitVec.add_assoc, reduceCtorEq, ↓reduceIte,
        Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod]


/-- The eight words currently held in accumulator registers. -/
def blockValue (f : Nat → Word) : Nat :=
  VG.Proof.Bignum.Square.value (2 ^ 64) (fun i => (f i).toNat) 8

theorem accumulator_reg (s : State) {i : Nat} (hi : i < 8) :
    accumulator s i = s.gpr VG.Impl.Bignum.AArch64.BlockedRedc.aa[i]! := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

theorem blockValue_congr {a b : Nat → Word} (h : ∀ i < 8, a i = b i) :
    blockValue a = blockValue b :=
  value_congr (fun i hi => congrArg BitVec.toNat (h i hi))

/-- The instruction-level carry-chain result implies full-block conservation. -/
theorem chain_result_value {t : State} {a b : Nat → Word} {c : Bool}
    (hc : t.c = chainCarry a b c 8)
    (hv : ∀ i < 8, t.gpr VG.Impl.Bignum.AArch64.BlockedRedc.aa[i]! =
      addCarry (a i) (b i) (chainCarry a b c i)) :
    blockValue (accumulator t) + 2 ^ 512 * t.c.toNat =
      blockValue a + blockValue b + c.toNat := by
  have ha : blockValue (accumulator t) =
      blockValue (fun i => addCarry (a i) (b i) (chainCarry a b c i)) :=
    blockValue_congr (fun i hi => (accumulator_reg t hi).trans (hv i hi))
  rw [ha, hc]
  have hp : (2 ^ 64) ^ 8 = 2 ^ 512 := by
    simpa only [Nat.reduceMul] using (Nat.pow_mul 2 64 8).symm
  simpa only [blockValue, hp] using (chain_value a b c 8)

/-- The scheduled low and high halves retain the whole scalar/block product. -/
theorem block_product_value (s : State) (n0 : Word) :
    blockValue (lowProduct s n0) + 2 ^ 64 * blockValue (highProduct s n0) =
      (s.gpr .x27).toNat * blockValue (operand s n0) := by
  suffices h : ∀ n,
      VG.Proof.Bignum.Square.value (2 ^ 64) (fun i => (lowProduct s n0 i).toNat) n +
        2 ^ 64 * VG.Proof.Bignum.Square.value (2 ^ 64) (fun i => (highProduct s n0 i).toNat) n =
      (s.gpr .x27).toNat * VG.Proof.Bignum.Square.value (2 ^ 64) (fun i => (operand s n0 i).toNat) n by
    exact h 8
  intro n
  induction n with
  | zero => simp only [VG.Proof.Bignum.Square.value, Nat.mul_zero, Nat.add_zero]
  | succ n ih =>
    have h := mul_toNat (s.gpr .x27) (operand s n0 n)
    change (lowProduct s n0 n).toNat + 2 ^ 64 * (highProduct s n0 n).toNat =
      (s.gpr .x27).toNat * (operand s n0 n).toNat at h
    simp only [VG.Proof.Bignum.Square.value]
    grind

end VG.Proof.Bignum.AArch64.BlockedRedc
