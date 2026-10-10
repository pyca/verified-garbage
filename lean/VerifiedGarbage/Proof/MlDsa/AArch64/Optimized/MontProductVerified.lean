import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MontProductLoop
import VerifiedGarbage.Proof.MlDsa.Arith.Montgomery

/-! ## From `MontProductCorrect.lean` -/

section

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

end

/-! ## From `MontProductVerified.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MontProduct
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.MontProduct (code)
open VG.Proof.MlDsa.AArch64.Arith (mulSat)

theorem pub {s t : State} (h : (montProductContract abi).pub s t) : contract.pub s t := by
  sig_pub [montProductContract,montProductSig,abi,argRegs] at h
  refine ⟨?_,h.1⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

theorem ct : ConstantTime isa contract.pre contract.pub code :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0,.x1,.x2])
    (fun _ _ _ _ h => VG.Proof.MlKem.AArch64.agree_of h.2 h.1) (by taint_decide)

theorem verified : Verified target code (montProductContract abi) := by
  refine Verified.of_correct correct ct
    { pre := fun _ h => pre h, post := ?_,pub := fun _ _ _ _ h => pub h,sat := ?_ }
  · intro s t _ h
    sig_post [montProductContract,montProductSig,abi,argRegs]
    exact h
  · refine ⟨mulSat,?_⟩
    sig_pre [montProductContract,montProductSig,abi,argRegs,stackBelow,mulSat]
    refine ⟨Region.disjoint_of_sep (by decide),Region.disjoint_of_sep (by decide),
      by decide,by decide,by decide,?_,?_⟩
    all_goals intro i hi; simp [coeffAt,Mem.readW,Mem.read,VG.Spec.MlDsa.q]
end VG.Proof.MlDsa.AArch64.Optimized.MontProduct

end
