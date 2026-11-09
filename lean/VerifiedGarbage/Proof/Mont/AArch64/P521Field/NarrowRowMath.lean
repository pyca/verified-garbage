module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.RowMath
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionArithmetic
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionCorrect

/-! The last product row exploits the nine-bit top limbs. -/

-- separate module: bounds for the shortened last multiplication row
@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Ed25519.Word64
open VG.Proof.Ed25519.AArch64 (mulHi)
open VG.Proof.Mont.AArch64.P521Square
  (value addWords addWords_length addWords_value value_append)

def narrowRow (a : Word) (ts bs : List Word) (top : Word) : List Word :=
  let low := addWords ts ((bs++[top]).map (a * ·)) false
  let high := addWords low.1.tail (bs.map (mulHi a)) false
  low.1.headD 0 :: high.1

/-- Both omitted carries are zero when the complete row fits in its
accumulator; the omitted high half of the top-limb product is zero too. -/
theorem narrowRow_value (a : Word) (ts bs : List Word) (top : Word)
    (hl : ts.length=bs.length+1) (htop : mulHi a top=0)
    (hb : value ts+a.toNat*value (bs++[top]) < 2^(64*ts.length)) :
    value (narrowRow a ts bs top) = value ts+a.toNat*value (bs++[top]) := by
  let low := addWords ts ((bs++[top]).map (a * ·)) false
  have hlen : low.1.length=ts.length := addWords_length ts _ false (by
    simp only [List.length_map,List.length_append,List.length_singleton,hl])
  have hlow := addWords_value ts ((bs++[top]).map (a * ·)) false (by
    simp only [List.length_map,List.length_append,List.length_singleton,hl])
  change value low.1+2^(64*ts.length)*low.2.toNat = _ at hlow
  have htail : low.1.tail.length=bs.length := by
    rw [List.length_tail,hlen,hl,Nat.add_sub_cancel]
  have hhigh := addWords_value low.1.tail (bs.map (mulHi a)) false (by rw [List.length_map,htail])
  have hv := value_head_tail low.1
  have hp := product_halves a (bs++[top])
  have hhighs : value ((bs++[top]).map (mulHi a)) = value (bs.map (mulHi a)) := by
    rw [List.map_append,value_append]
    simp only [List.map_cons,List.map_nil,htop,value,
      show (0 : Word).toNat=0 from rfl,Nat.mul_zero,Nat.add_zero]
  rw [hhighs] at hp
  simp only [Bool.toNat_false,Nat.add_zero] at hlow hhigh
  have hh := congrArg (fun n => 2^64*n) hhigh
  have he : 2^64*2^(64*low.1.tail.length)=2^(64*ts.length) := by
    rw [htail,hl,Nat.mul_add,Nat.mul_one,Nat.pow_add,Nat.mul_comm]
  simp only [Nat.mul_add,←Nat.mul_assoc,he] at hh
  have hlow0 : low.2.toNat=0 := by
    cases hc : low.2 with
    | false => rfl
    | true =>
      rw [hc] at hlow
      simp only [Bool.toNat_true,Nat.mul_one] at hlow
      omega_using [hlow,hp,hb]
  rw [hlow0,Nat.mul_zero,Nat.add_zero] at hlow
  have hc0 : (addWords low.1.tail (bs.map (mulHi a)) false).2.toNat=0 := by
    cases hc : (addWords low.1.tail (bs.map (mulHi a)) false).2 with
    | false => rfl
    | true =>
      rw [hc] at hh
      simp only [Bool.toNat_true,Nat.mul_one] at hh
      omega_using [hh,hv,hlow,hp,hb]
  rw [hc0,Nat.mul_zero,Nat.add_zero] at hh
  change (low.1.headD 0).toNat + 2^64*value (addWords low.1.tail (bs.map (mulHi a)) false).1 = _
  omega_using [hh,hv,hlow,hp]

end VG.Proof.Mont.AArch64.P521Field
