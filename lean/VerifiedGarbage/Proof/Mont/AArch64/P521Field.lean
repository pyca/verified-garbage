module

public import VerifiedGarbage.Impl.Mont.AArch64.P521Field
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Function
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Product
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Reduction
import VerifiedGarbage.Proof.Framework.Block

/-! Ordinary field squaring reuses the existing symmetric-product proof. -/

-- separate module: isolates ordinary field arithmetic from Montgomery callers
@[expose] public section

namespace VG.Proof.Mont.AArch64.P521Field

open VG VG.AArch64 VG.Impl.Mont.AArch64.P521Square
open VG.Impl.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square
open VG.Proof.Ed25519.AArch64

theorem squareCore_arith (s : State) (hz : s.gpr .x30 = 0)
    (ha : regsVal s aRegs < fieldPrime) :
    WP isa (.block squareCore) s fun t =>
      regsVal t (uRegs.take 9) < fieldPrime ∧
      regsVal t (uRegs.take 9) = regsVal s aRegs * regsVal s aRegs % fieldPrime ∧
      Keeps coreClob s t := by
  rw [squareCore,List.append_assoc,WP.block_append_iff]
  have hp := product_ok s hz
  rw [prime_value] at hp
  refine WP.mono (hp (by simpa only [fieldPrime,prime_value] using ha)) fun u ⟨h,k⟩ => ?_
  have z : u.gpr .x30 = 0 := (k.gpr .x30 (by decide)).trans hz
  have hb : regsVal u uRegs < fieldPrime*fieldPrime := by
    rw [h]
    exact Nat.mul_lt_mul'' ha ha
  refine WP.mono (canonical_reduction_ok u z hb) fun t ⟨ht,et,kt⟩ => ?_
  exact ⟨ht,by rw [et,h],(k.mono (by decide)).trans (kt.mono (by decide))⟩


theorem squareCore_ok (s : State) (hz : s.gpr .x30 = 0)
    (ha : regsVal s aRegs < fieldPrime) :
    WP isa (.block squareCore) s fun t =>
      regsVal t (uRegs.take 9) < fieldPrime ∧
      regsVal t (uRegs.take 9) = regsVal s aRegs * regsVal s aRegs % fieldPrime ∧
      Keeps coreClob s t ∧ t.v = s.v := by
  exact WP.mono (VG.Proof.Weierstrass.AArch64.Mont.WP.block_novec (by
    simp only [squareCore,product,List.mem_append,or_imp,forall_and]
    repeat' constructor
    all_goals decide) (squareCore_arith s hz ha))
    (fun _ ⟨⟨h,e,k⟩,v⟩ => ⟨h,e,k,v⟩)

end VG.Proof.Mont.AArch64.P521Field
