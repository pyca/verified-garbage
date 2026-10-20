module

public import VerifiedGarbage.Impl.Bignum.AArch64.BlockedRedc
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcMath
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

@[expose] public section

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
    blockValue (accumulator t) + (2 ^ 64) ^ 8 * t.c.toNat =
      blockValue a + blockValue b + c.toNat := by
  have ha : blockValue (accumulator t) =
      blockValue (fun i => addCarry (a i) (b i) (chainCarry a b c i)) :=
    blockValue_congr (fun i hi => (accumulator_reg t hi).trans (hv i hi))
  rw [ha, hc]
  exact chain_value a b c 8

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


/-- Shifting the low-chain accumulator exposes its low word and appends the
captured high carry word. -/
theorem shifted_value (s : State) :
    (s.gpr .x19).toNat + 2 ^ 64 * blockValue (shifted s) =
      blockValue (accumulator s) + (2 ^ 64) ^ 8 * (s.gpr .x1).toNat := by
  have ht : VG.Proof.Bignum.Square.value (2 ^ 64) (fun i => (shifted s i).toNat) 7 =
      VG.Proof.Bignum.Square.value (2 ^ 64) (fun i => (accumulator s (i + 1)).toNat) 7 := by
    apply value_congr
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rfl
  have hs := value_shift (2 ^ 64) (fun i => (accumulator s i).toNat) 7
  have hp : 2 ^ 64 * (2 ^ 64) ^ 7 = (2 ^ 64) ^ 8 := by
    rw [Nat.pow_succ (2 ^ 64) 7, Nat.mul_comm]
  unfold blockValue
  rw [VG.Proof.Bignum.Square.value]
  rw [show shifted s 7 = s.gpr .x1 from rfl, ht]
  rw [show accumulator s 0 = s.gpr .x19 from rfl] at hs
  rw [Nat.mul_add, ← Nat.add_assoc]
  rw [show 2 ^ 64 * ((s.gpr .x1).toNat * (2 ^ 64) ^ 7) =
    (2 ^ 64 * (2 ^ 64) ^ 7) * (s.gpr .x1).toNat by ac_rfl]
  simp only [Nat.reduceAdd] at hs
  rewrite [hp, hs]
  rfl


theorem accumulator_congr {s t : State}
    (h : ∀ r ∈ VG.Impl.Bignum.AArch64.BlockedRedc.aa, t.gpr r = s.gpr r) :
    accumulator t = accumulator s := by
  funext i
  simp only [accumulator, h .x19 (by decide), h .x20 (by decide), h .x21 (by decide),
    h .x22 (by decide), h .x23 (by decide), h .x24 (by decide), h .x25 (by decide), h .x26 (by decide)]

theorem highTerms_value {s t : State} (n0 : Word)
    (h13 : t.gpr .x13 = highProduct s n0 0) (h14 : t.gpr .x14 = highProduct s n0 1)
    (h28 : t.gpr .x28 = highProduct s n0 2) (h30 : t.gpr .x30 = highProduct s n0 3)
    (h27 : t.gpr .x27 = s.gpr .x27) (h5 : t.gpr .x5 = s.gpr .x5)
    (h6 : t.gpr .x6 = s.gpr .x6) (h9 : t.gpr .x9 = s.gpr .x9)
    (h11 : t.gpr .x11 = s.gpr .x11) :
    blockValue (highTerms t) = blockValue (highProduct s n0) := by
  apply blockValue_congr
  intro i hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [highTerms, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, h13, h14, h28, h30,
      highProduct, operand, h27, h5, h6, h9, h11]


theorem keep_accumulator {s t : State} {rs : List Reg} (h : Keep rs s t)
    (hd : ∀ r ∈ VG.Impl.Bignum.AArch64.BlockedRedc.aa, r ∉ rs) :
    accumulator t = accumulator s := accumulator_congr (fun r hr => h.gpr r (hd r hr))

theorem keep_operand {s t : State} {rs : List Reg} (h : Keep rs s t)
    (hd : ∀ r ∈ VG.Impl.Bignum.AArch64.BlockedRedc.nn, r ∉ rs) (n0 : Word) :
    operand t n0 = operand s n0 := by
  funext i
  have h2 := h.gpr .x2 (hd .x2 (by decide))
  have h3 := h.gpr .x3 (hd .x3 (by decide))
  have h4 := h.gpr .x4 (hd .x4 (by decide))
  have h5 := h.gpr .x5 (hd .x5 (by decide))
  have h6 := h.gpr .x6 (hd .x6 (by decide))
  have h9 := h.gpr .x9 (hd .x9 (by decide))
  have h11 := h.gpr .x11 (hd .x11 (by decide))
  simp only [operand, h2, h3, h4, h5, h6, h9, h11]

theorem blockValue_lt (f : Nat → Word) : blockValue f < (2 ^ 64) ^ 8 :=
  value_lt _ _ _ (fun i _ => (f i).isLt)

theorem blockValue_mod (f : Nat → Word) : blockValue f % 2 ^ 64 = (f 0).toNat :=
  value_mod _ _ 7 (f 0).isLt

/-- The inverse condition cancels exactly the low word of the register
block. Higher carries are left in the row conservation identity. -/
theorem cancel_low {s : State} {n0 lo : Word} {rest : Nat}
    (hinv : (n0.toNat * (s.gpr .x15).toNat + 1) % 2 ^ 64 = 0)
    (hv : lo.toNat + 2 ^ 64 * rest = blockValue (accumulator s) +
      (s.gpr .x19 * s.gpr .x15).toNat * blockValue (operand s n0)) : lo = 0 := by
  have h := congrArg (· % 2 ^ 64) hv
  have hacc := blockValue_mod (accumulator s)
  have hop := blockValue_mod (operand s n0)
  change blockValue (accumulator s) % 2 ^ 64 = (s.gpr .x19).toNat at hacc
  change blockValue (operand s n0) % 2 ^ 64 = n0.toNat at hop
  have hm := mont_low (s.gpr .x19).toNat (s.gpr .x15).toNat n0.toNat hinv
  have hmul : (s.gpr .x19 * s.gpr .x15).toNat =
      (s.gpr .x19).toNat * (s.gpr .x15).toNat % 2 ^ 64 := BitVec.toNat_mul _ _
  have hrem : lo.toNat = 0 := by
    simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod,
      Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt lo.isLt] at h
    rw [hacc, hop, hmul] at h
    simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod,
      Nat.mod_eq_of_lt (s.gpr .x19).isLt, Nat.mod_eq_of_lt (s.gpr .x15).isLt,
      Nat.mod_eq_of_lt n0.isLt] at h hm
    rw [Nat.add_comm] at hm
    exact h.trans hm
  exact BitVec.eq_of_toNat_eq hrem

theorem value_words (m : Mem) (B : Addr) (e k : Nat) :
    VG.Proof.Bignum.Square.value (2 ^ 64) (fun i => (word m B (e + 8 * i)).toNat) k =
      wv m B e k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change VG.Proof.Bignum.Square.value (2 ^ 64) (fun i => (word m B (e + 8 * i)).toNat) k +
      (word m B (e + 8 * k)).toNat * (2 ^ 64) ^ k =
      wv m B e k + 2 ^ (64 * k) * (word m B (e + 8 * k)).toNat
    exact (congrArg (· + (word m B (e + 8 * k)).toNat * (2 ^ 64) ^ k) ih).trans
      (congrArg (wv m B e k + ·) ((Nat.mul_comm _ _).trans
        (congrArg (· * (word m B (e + 8 * k)).toNat) (Nat.pow_mul 2 64 k).symm)))

theorem blockValue_words (m : Mem) (B : Addr) (e : Nat) :
    blockValue (fun i => word m B (e + 8 * i)) = wv m B e 8 := value_words m B e 8

theorem wv_radix_add (m : Mem) (B : Addr) (e n k : Nat) :
    wv m B e (n + k) = wv m B e n + (2 ^ 64) ^ n * wv m B (e + 8 * n) k :=
  (wv_add m B e n k).trans
    (congrArg (fun r => wv m B e n + r * wv m B (e + 8 * n) k) (Nat.pow_mul 2 64 n))

theorem word_flag (v : Word) (hv : v.toNat ≤ 1) : ∃ p : Bool, v = BitVec.ofNat 64 p.toNat := by
  rcases (by omega : v.toNat = 0 ∨ v.toNat = 1) with h | h
  · exact ⟨false, BitVec.eq_of_toNat_eq h⟩
  · exact ⟨true, BitVec.eq_of_toNat_eq h⟩

end VG.Proof.Bignum.AArch64.BlockedRedc
