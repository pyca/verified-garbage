module

public import VerifiedGarbage.Proof.Ffdh.AArch64.VettedValidation.Contract
import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import Batteries.Logic
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ffdh.Contract
meta import VerifiedGarbage.TCB.AArch64.Target

/-! A permitted domain buffer and disjoint public table witness contract satisfiability. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.VettedValidation
open VG VG.AArch64
open VG.Impl.Ffdh.AArch64.Cached

private def satState (W : List (BitVec 64)) : State where
  gpr r := match r with
    | .x0=>0x1000 | .x1=>128 | .x2=>64 | .x3=>0x9000 | .x4=>1056 | _=>0
  sp:=0x8000
  mem:=constMem 0x200000 W
  rd:=[⟨0x1000,128⟩,⟨0x200000,17744⟩]
  wr:=[⟨0x9000,8448⟩]
  syms:=fun _=>0x200000

private theorem shared_sat_aux (W : List (BitVec 64)) (length : W.length=2218) :
    ∃s,(Spec.Ffdh.checkDomainContract (abi.withConsts [(Policy.tableSym,W)])).pre s := by
  refine ⟨satState W,pre_consts.mpr ⟨?_,?_⟩⟩
  · sig_pre [Spec.Ffdh.checkDomainContract,Spec.Ffdh.checkDomainSig,Spec.Ffdh.pLenValid,
      Spec.Ffdh.domainLenValid,Spec.Rsa.scratchWords,abi,argRegs]
    repeat' apply And.intro
    all_goals first
      | rfl
      | decide +kernel
      | (apply Region.disjoint_of_sep;decide +kernel)
  · refine ⟨?_,?_,?_,?_⟩
    · simp only [satState,constRegs,Abi.constRegions,List.map_cons,List.map_nil,length]
      rfl
    · intro c hc i hi
      simp only [List.mem_singleton] at hc
      subst c
      exact constMem_held 0x200000 W (by rw [length];decide) i hi
    · intro r hr
      simp only [constRegs,Abi.constRegions,List.mem_map,List.mem_singleton] at hr
      obtain ⟨c,rfl,rfl⟩:=hr
      rw [length]
      dsimp only [satState]
      refine ⟨by decide,?_,?_⟩
      · intro q hq
        change q∈([⟨0x9000,8448⟩] : List Region) at hq
        simp only [List.mem_singleton] at hq
        subst q
        apply Region.disjoint_of_sep
        decide
      · intro q hq
        simp only [abi,stackBelow,List.not_mem_nil] at hq
    · intro r hr
      simp only [constRegs,Abi.constRegions,List.mem_map,List.mem_singleton] at hr
      obtain ⟨c,rfl,rfl⟩:=hr
      dsimp only [satState]
      decide

theorem shared_sat : ∃s,(Spec.Ffdh.checkDomainContract (abi.withConsts Policy.tableConsts)).pre s :=
  shared_sat_aux Policy.tableWords Cached.Policy.tableWords_length

end VG.Proof.Ffdh.AArch64.VettedValidation
