module

public import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionWords

/-! Carry arithmetic for the streamed first row of an ordinary product. -/

-- separate module: shares row arithmetic between standalone and point kernels
@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field

open VG.Proof.Ed25519.Word64
open VG.Proof.Ed25519.AArch64 (mulHi mul_lo_hi mul_le)
open VG.Proof.Mont.AArch64.P521Square (value)

/-- A product's high word has room for a final carry. -/
theorem mulHi_carry_lt (a b : Word) (c : Bool) :
    (mulHi a b).toNat + c.toNat < 2^64 := by
  have h := mul_lo_hi a b
  have hp := mul_le a b
  have hc := Bool.toNat_le c
  omega_arith

/-- Each row step adds the next product's low half to the previous high
half; only the one-bit carry survives to the following step. -/
def firstChain (a h : Word) (c : Bool) : List Word → List Word
  | [] => [addCarry h 0 c]
  | b::bs => addCarry h (a*b) c :: firstChain a (mulHi a b) (carryOut h (a*b) c) bs

private theorem carry_product_step {h c lo hi next out prod tail : Nat}
    (ha : out + 2^64*next = h+lo+c) (hm : lo+2^64*hi = prod) :
    out + 2^64*(hi+next+tail) = h+c+prod+2^64*tail := by
  omega_arith

theorem firstChain_value (a : Word) : ∀ (bs : List Word) (h : Word) (c : Bool),
    h.toNat+c.toNat < 2^64 →
    value (firstChain a h c bs) = h.toNat+c.toNat+a.toNat*value bs := by
  intro bs
  induction bs with
  | nil =>
    intro h c hb
    simp only [firstChain,value,Nat.mul_zero,Nat.add_zero,addCarry,
      BitVec.toNat_add,carryWord,show (0 : Word).toNat = 0 from rfl,
      Nat.mod_eq_of_lt h.isLt]
    exact Nat.mod_eq_of_lt hb
  | cons b bs ih =>
    intro h c _
    rw [firstChain,value,ih (mulHi a b) (carryOut h (a*b) c)
      (mulHi_carry_lt a b (carryOut h (a*b) c))]
    have hs := carry_product_step (tail:=a.toNat*value bs)
      (addCarry_value h (a*b) c) (mul_lo_hi a b)
    rw [hs]
    simp only [value,Nat.mul_add,Nat.mul_left_comm a.toNat (2^64),Nat.add_assoc]

/-- The first product row, with no pre-existing accumulator. -/
def firstRow (a : Word) : List Word → List Word
  | [] => [0]
  | b::bs => a*b :: firstChain a (mulHi a b) false bs

theorem firstRow_value (a : Word) (bs : List Word) :
    value (firstRow a bs) = a.toNat*value bs := by
  cases bs with
  | nil => simp only [firstRow,value,show (0 : Word).toNat = 0 from rfl,Nat.mul_zero,Nat.add_zero]
  | cons b bs =>
    rw [firstRow,value,firstChain_value a bs (mulHi a b) false (mulHi_carry_lt a b false)]
    simp only [Bool.toNat_false,Nat.add_zero,Nat.mul_add]
    rw [←Nat.add_assoc,mul_lo_hi]
    simp only [value,Nat.mul_add,Nat.mul_left_comm a.toNat (2^64)]

end VG.Proof.Mont.AArch64.P521Field
