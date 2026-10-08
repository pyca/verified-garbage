import VerifiedGarbage.Impl.Weierstrass.X86.NafPrep
import VerifiedGarbage.Proof.Weierstrass.Naf5
import VerifiedGarbage.Proof.Weierstrass.X86.TCombDigit

/-! Selecting a signed width-five digit from the public scalar's low word. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Weierstrass.X86
open VG.Proof.Mont.X86

def nafOdd (x : BitVec 32) : BitVec 32 :=
  if (x &&& 31).toNat<16 then x &&& 31 else (x &&& 31)-32

def nafRaw (x : BitVec 32) : BitVec 32 := if x &&& 1=0 then 0 else nafOdd x

theorem nafMask (x : BitVec 32) : x &&& 31=BitVec.ofNat 32 (x.toNat%32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and,BitVec.toNat_ofNat]
  change x.toNat &&& (2^5-1) = (x.toNat%32)%2^32
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem nafParity (x : BitVec 32) : x &&& 1=0 ↔ x.toNat%2=0 := by
  rw [←BitVec.toNat_inj]
  change x.toNat &&& 1=0 ↔ x.toNat%2=0
  rw [Nat.and_one_is_mod]

theorem nafRaw_eq {x : BitVec 32} {k j : Nat}
    (hx : x.toNat%32=Naf5.residual k j%32) : nafRaw x=BitVec.ofInt 32 (Naf5.digit k j) := by
  have H : ∀ r : Fin 32,
      (if r.val%2=0 then (0 : BitVec 32) else if r.val<16 then BitVec.ofNat 32 r.val else
        BitVec.ofNat 32 r.val-32) =
      BitVec.ofInt 32 (if r.val%2=0 then 0 else if r.val<16 then (r.val:Int) else (r.val:Int)-32) := by decide
  simp only [nafRaw,nafOdd,nafParity,nafMask,BitVec.toNat_ofNat,hx,Naf5.digit_mod32]
  have hp : x.toNat%2=Naf5.residual k j%32%2 := by omega
  rw [hp,Nat.mod_eq_of_lt (show Naf5.residual k j%32<2^32 from by omega)]
  exact H ⟨Naf5.residual k j%32,Nat.mod_lt _ (by decide)⟩

theorem nafOdd_ok (s : State) :
    WP isa Naf.oddDigit s fun t => t.gpr .ecx=nafOdd (s.gpr .eax) ∧ CKeeps [.ecx] s t := by
  rw [Naf.oddDigit]
  refine WP.seq ?_
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,
    Option.map_some,Option.bind_some,RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,
    ite_true,Option.some.injEq,exists_eq_left']
  refine WP.ite (decide ((s.gpr .eax &&& 31).toNat<16)) ?_ (fun h => ?_) (fun h => ?_)
  · rfl
  · apply WP.block_nil
    refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl⟩
    · simp only [RegUpd.gpr_arithFlags,RegUpd.gpr_setReg,ite_true,nafOdd,
        of_decide_eq_true h,ite_true]
    · simp only [List.mem_singleton] at hr
      simp only [RegUpd.gpr_arithFlags,RegUpd.gpr_setReg,hr,ite_false]
  · apply WP.of_runBlock
    simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,
      Option.bind_some,RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,
      ite_true,Option.some.injEq,exists_eq_left']
    refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl⟩
    · simp only [nafOdd,of_decide_eq_false h,ite_false]
    · simp only [List.mem_singleton] at hr
      simp only [RegUpd.gpr_arithFlags,RegUpd.gpr_setReg,hr,ite_false]

theorem nafParity_ok (s : State) :
    WP isa (.block [.mov .ecx (.reg .eax),.alu .and .ecx (.imm 1),.alu .test .ecx (.reg .ecx)]) s
      fun t => t.gpr .ecx=s.gpr .eax &&& 1 ∧ t.zf=some (decide (s.gpr .eax &&& 1=0)) ∧ CKeeps [.ecx] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,
    Option.map_some,Option.bind_some,RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,
    RegUpd.zf_arithFlags,BitVec.and_self,ite_true,Option.some.injEq,exists_eq_left']
  refine ⟨trivial,?_,fun r hr => ?_,rfl,rfl,rfl⟩
  · rfl
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_arithFlags,RegUpd.gpr_setReg,hr,ite_false]

end VG.Proof.Weierstrass.X86
