import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.MontgomeryCore

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.X86_64 (Keep XOnly YOnly ylanes yld_ok yconst_ok WP.keep writesOnly gprPreserved_of ifp ifn
  ptr_step GOnly wp_rcxLoopY add_ofNat_zero lane_setReg lane_setFlags sx32 State.setMem_ymm xmm_setXmm)
open VG.Impl.MlKem.X86_64 (xb xmov toY yconst rcxLoop)
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced)

abbrev montMulK : Contract isa := mulK (fun _ f g => Spec.MlDsa.montgomeryMultiplyNTT f g) fun _ _ => True
abbrev montMulAddK : Contract isa := mulK Spec.MlDsa.montgomeryMultiplyAddNTT Reduced

theorem montMul_get (f g : Poly) {i : Nat} (hi : i < n) :
    (Spec.MlDsa.montgomeryMultiplyNTT f g)[i]! = f[i]! * g[i]! * Spec.MlDsa.montgomeryRInv := by
  rw [Spec.MlDsa.montgomeryMultiplyNTT, map_mul_get _ _ hi, mul_get _ _ hi]

theorem montMulY_correct (s : State) (hs : montMulK.pre s) :
    ∃ t s', Exec isa montMulAvx2 s t s' ∧ abiPreserved s s' ∧ montMulK.post s s' := by
  obtain ⟨t, s', he, hk, hf, hq⟩ := YMul.fn_ok hs (core := montMulCore) (Fv := fun x y _ => montMulV x y)
    (fun s hc _ => montMulCore_ok hc) lane_montMulCore
    (fun i hi x y z hx hy _ e he => by
      rw [montMul_get _ _ (by rw [n_eq]; omega)]
      exact montMul_lane hx hy he)
    (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_ctl (by decide +kernel) he (gprPreserved_of hk (by decide) hf
    (by simpa using hs.2.2.2.2.1)), hq⟩

theorem montMulAddY_correct (s : State) (hs : montMulAddK.pre s) :
    ∃ t s', Exec isa montMulAddAvx2 s t s' ∧ abiPreserved s s' ∧ montMulAddK.post s s' := by
  obtain ⟨t, s', he, hk, hf, hq⟩ := YMul.fn_ok hs (core := montMulAddCore) (Fv := montMulAddV)
    (fun s hc _ => montMulAddCore_ok hc) lane_montMulAddCore
    (fun i hi x y z hx hy hz e he => by
      rw [Spec.MlDsa.montgomeryMultiplyAddNTT, add_get _ _ (by rw [n_eq]; omega), montMul_get _ _ (by rw [n_eq]; omega)]
      exact montMulAdd_lane hx hy (c := fun e => (polyAt s.mem (s.gpr .rdi))[4 * i + e]!)
        (fun e he => by rw [hz e he, polyAt_val hs.2.2.2.2.2.2.2.1 (by rw [n_eq]; omega)]) he)
    (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_ctl (by decide +kernel) he (gprPreserved_of hk (by decide) hf
    (by simpa using hs.2.2.2.2.1)), hq⟩

theorem montMulY_ct : ConstantTime isa montMulK.pre montMulK.pub montMulAvx2 :=
  VG.Taint.constantTime (A := taint) mulτ mul_agree (by taint_decide)

theorem montMulAddY_ct : ConstantTime isa montMulAddK.pre montMulAddK.pub montMulAddAvx2 :=
  VG.Taint.constantTime (A := taint) mulτ mul_agree (by taint_decide)

theorem montMulY_verified : Verified X86_64.target montMulAvx2 (Spec.MlDsa.montgomeryMulContract X86_64.abi) :=
  Verified.of_correct montMulY_correct montMulY_ct (by
    mldsa_implies [Spec.MlDsa.montgomeryMulContract, Spec.MlDsa.mulSig, mulK, X86_64.abi, X86_64.argRegs]
      [mulSat] using mulSat)

theorem montMulAddY_verified : Verified X86_64.target montMulAddAvx2 (Spec.MlDsa.montgomeryMulAddContract X86_64.abi) :=
  Verified.of_correct montMulAddY_correct montMulAddY_ct (by
    mldsa_implies [Spec.MlDsa.montgomeryMulAddContract, Spec.MlDsa.mulSig, mulK, X86_64.abi, X86_64.argRegs]
      [mulSat] using mulSat)

end VG.Proof.MlDsa.X86_64.Arith
