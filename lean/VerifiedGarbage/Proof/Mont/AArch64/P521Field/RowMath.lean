module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.ProductMath
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionArithmetic
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionCorrect

/-! The two carry chains of each streamed product row. -/

-- separate module: arithmetic shared by multiplication and point-kernel rows
@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Ed25519.Word64
open VG.Proof.Ed25519.AArch64 (mulHi mul_lo_hi)
open VG.Proof.Mont.AArch64.P521Square
  (value addWords addWords_length addWords_value value_append value_lt)

theorem product_halves (a : Word) (bs : List Word) :
    value (bs.map (a * ·)) + 2^64 * value (bs.map (mulHi a)) = a.toNat * value bs := by
  induction bs with
  | nil => simp only [List.map_nil,value,Nat.mul_zero,Nat.add_zero]
  | cons b bs ih =>
    simp only [List.map_cons,value,Nat.mul_add]
    have h := mul_lo_hi a b
    rw [Nat.mul_left_comm a.toNat (2^64),←ih,Nat.mul_add]
    omega_arith

theorem value_head_tail (xs : List Word) :
    value xs = (xs.headD 0).toNat + 2^64 * value xs.tail := by
  cases xs with
  | nil => simp only [value,List.headD_nil,List.tail_nil,
      show (0 : Word).toNat=0 from rfl,Nat.mul_zero,Nat.add_zero]
  | cons x xs => rfl

/-- The low chain's outgoing carry becomes the top accumulator word;
the high chain starts one word above the low chain. -/
def rowCarry (a : Word) (ts bs : List Word) : List Word × Bool :=
  let low := addWords ts (bs.map (a * ·)) false
  let high := addWords (low.1.tail ++ [BitVec.ofNat 64 low.2.toNat]) (bs.map (mulHi a)) false
  (low.1.headD 0 :: high.1,high.2)

/-- No carries are discarded in the integer identity. -/
theorem rowCarry_value (a : Word) (ts bs : List Word)
    (hl : ts.length=bs.length) (hn : 0<ts.length) :
    value (rowCarry a ts bs).1 + 2^(64*(ts.length+1))*(rowCarry a ts bs).2.toNat =
      value ts + a.toNat*value bs := by
  let low := addWords ts (bs.map (a * ·)) false
  have hlen : low.1.length=ts.length := addWords_length ts _ false (by rw [List.length_map,hl])
  have hlow := addWords_value ts (bs.map (a * ·)) false (by rw [List.length_map,hl])
  change value low.1 + 2^(64*ts.length)*low.2.toNat = _ at hlow
  let hs := low.1.tail ++ [BitVec.ofNat 64 low.2.toNat]
  have hhs : hs.length=bs.length := by
    simp only [hs,List.length_append,List.length_tail,List.length_singleton,hlen]
    omega_arith
  have hhigh := addWords_value hs (bs.map (mulHi a)) false (by rw [List.length_map,hhs])
  have hv := value_head_tail low.1
  have hparts := product_halves a bs
  have htail : low.1.tail.length+1=ts.length := by rw [List.length_tail,hlen]; omega_arith
  have hhsv : value hs = value low.1.tail + 2^(64*low.1.tail.length)*low.2.toNat := by
    rw [value_append]
    simp only [value,Nat.mul_zero,Nat.add_zero,carryWord]
  rw [hhsv,hhs] at hhigh
  have hp : 2^(64*(ts.length+1)) = 2^64*2^(64*ts.length) := by
    rw [Nat.mul_add,Nat.mul_one,Nat.pow_add,Nat.mul_comm]
  have ht : 2^64*2^(64*low.1.tail.length)=2^(64*ts.length) := by
    rw [←Nat.pow_add]
    exact congrArg (2^·) (by omega_arith)
  simp only [Bool.toNat_false,Nat.add_zero] at hlow hhigh
  change (low.1.headD 0).toNat + 2^64*value (addWords hs (bs.map (mulHi a)) false).1 +
    2^(64*(ts.length+1))*(addWords hs (bs.map (mulHi a)) false).2.toNat = _
  rw [←hl] at hhigh
  have hh := congrArg (fun n => 2^64*n) hhigh
  simp only [Nat.mul_add,←Nat.mul_assoc,ht] at hh
  rw [hp]
  omega_using [hh,hv,hlow,hparts]

/-- A one-word multiplier and a same-width accumulator fit in one extra word. -/
theorem row_bound (a : Word) (ts bs : List Word) (hl : ts.length=bs.length) :
    value ts + a.toNat*value bs < 2^(64*(ts.length+1)) := by
  have ht := value_lt ts
  have hb := value_lt bs
  rw [←hl] at hb
  have ha := a.isLt
  have hm := Nat.mul_le_mul (Nat.le_sub_one_of_lt ha) (Nat.le_sub_one_of_lt hb)
  simp only [Nat.sub_mul,Nat.mul_sub,Nat.one_mul,Nat.mul_one] at hm
  rw [Nat.mul_add,Nat.mul_one,Nat.pow_add,
    Nat.mul_comm (2^(64*ts.length)) (2^64)]
  omega_arith

/-- The terminal ADC cannot lose a carry at the top of the streamed row. -/
theorem row_value (a : Word) (ts bs : List Word)
    (hl : ts.length=bs.length) (hn : 0<ts.length) :
    value (rowCarry a ts bs).1 = value ts + a.toNat*value bs := by
  have h := rowCarry_value a ts bs hl hn
  have hb := row_bound a ts bs hl
  have hc : (rowCarry a ts bs).2.toNat=0 := by
    cases he : (rowCarry a ts bs).2 with
    | false => rfl
    | true =>
      rw [he] at h
      simp only [Bool.toNat_true,Nat.mul_one] at h
      omega_arith
  rw [hc,Nat.mul_zero,Nat.add_zero] at h
  exact h

end VG.Proof.Mont.AArch64.P521Field
