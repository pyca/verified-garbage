module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafSubtract
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Selecting a signed width-five digit from the public scalar's low word. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.X25519.X86_64

theorem nafParity (x : BitVec 64) : x &&& 1=0 ↔ x.toNat%2=0 := by
  rw [←BitVec.toNat_inj]
  change x.toNat &&& 1=0 ↔ x.toNat%2=0
  rw [Nat.and_one_is_mod]

theorem nafParity_ok (s : State) :
    WP isa (.block [.mov .rcx (.reg .r8),.alu .and .rcx (.imm 1),.alu .test .rcx (.reg .rcx)]) s
      fun t => t.gpr .rcx=s.gpr .r8 &&& 1 ∧ t.zf=some (decide (s.gpr .r8 &&& 1=0)) ∧ Keeps [.rcx] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,
    Option.map_some,Option.bind_some,RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,
    RegUpd.zf_arithFlags,BitVec.and_self,ite_true,Option.some.injEq,exists_eq_left']
  refine ⟨rfl,?_,fun r hr => ?_,rfl,rfl,rfl⟩
  · rfl
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_arithFlags,RegUpd.gpr_setReg,hr,ite_false]

end VG.Proof.Weierstrass.X86_64
