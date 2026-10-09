import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MontProductLoop
import VerifiedGarbage.Proof.MlDsa.Arith.Montgomery

namespace VG.Proof.MlDsa.AArch64.Optimized.MontProduct
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith

theorem result_field (a b : Nat) : result a b = (ofNat a * ofNat b * montgomeryRInv).val := by
  have hm (x : Nat) : mont x % q = x*8265825%q := by
    apply cancel_R
    rw [mont_mod,Nat.mul_assoc,Nat.mul_mod,show 8265825*2^32%q=1 by decide,
      Nat.mul_one,Nat.mod_mod]
  rw [result,hm,val_mul,val_mul]
  rw [val_ofNat,val_ofNat,show montgomeryRInv.val=8265825 by decide]
  simp only [Nat.mul_mod,Nat.mod_mod]

theorem correct (s : State) (hp : contract.pre s) :
    ∃tr t,Exec isa VG.Impl.MlDsa.AArch64.Optimized.MontProduct.code s tr t ∧
      abiPreserved s t ∧ contract.post s t := by
  obtain ⟨tr,t,he,hi⟩ := run_ok s hp
  refine ⟨tr,t,he,VG.Proof.MlKem.AArch64.abi_of rfl (by decide +kernel) he (by decide +kernel),
    polyIs_of_toNat fun i hit => ?_⟩
  have hlt : i<256 := hit
  rw [hi.coeff i hlt,ite_eq_left (by omega),result_field]
  change _ = ((multiplyNTT (polyAt s.mem (s.gpr .x1)) (polyAt s.mem (s.gpr .x2))).map (·*montgomeryRInv))[i]!.val
  rw [map_mul_get _ _ hit,mul_get _ _ hit,
    polyAt_get _ _ hit,polyAt_get _ _ hit]
end VG.Proof.MlDsa.AArch64.Optimized.MontProduct
