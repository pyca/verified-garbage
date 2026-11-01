module

public import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.CombContract
public import VerifiedGarbage.Proof.Secp256k1.Arm.CombSat
public import VerifiedGarbage.Proof.Ecdsa.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-! The public signing contract with ROM is satisfiable. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Arm.Secp256k1
open VG VG.Arm VG.Impl.Weierstrass.Arm VG.Proof.Secp256k1.Arm

theorem combSign_sat : combSignSpec.pre combSatState := by
  have arg := combSat_stackArg
  have held := combSat_held
  generalize eqs : combSatState=s
  sig_pre [combSignSpec,Spec.Ecdsa.Secp256k1.inst,Proof.Ecdsa.Instance.signContract,
    Proof.Ecdsa.Instance.signSig,Spec.Secp256k1.curve,Spec.Ecdsa.scratchWords,abi,argRegs,reduceClassify,
    Loc.val,State.addr,stackArgAddr,BitVec.add_zero,secp256k1CombConsts,Abi.withConsts,
    Abi.constRegions,Abi.constsHeld,stackBelow]
  subst s
  rw [arg,comb_words_length]
  rw [comb_words_length] at held
  refine ⟨by decide,by decide,held,by decide,?_,by decide,by decide,?_⟩
  · intro r hr
    change r∈[⟨0x10000,64⟩,⟨0,8192⟩] at hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide

end VG.Proof.Ecdsa.Arm.Secp256k1
