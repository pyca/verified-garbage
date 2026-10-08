import VerifiedGarbage.Impl.Weierstrass.X86.Naf
import VerifiedGarbage.Proof.Weierstrass.X86.NafPrep

/-! Read public signed digits and test their sign and zero case. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
  VG.Proof.Mont.X86 VG.Proof.Mont

def nafMagnitude (b : BitVec 8) : Nat := if b.toNat<128 then b.toNat else 256-b.toNat

def nafNegative (b : BitVec 8) : Bool := decide (128≤b.toNat)

private theorem nafRead_zero : ∀ b : BitVec 8, (b.setWidth 32==0)=decide (b=0) := by decide

theorem nafRead_ok {K : WinCfg} {s : State} {base : Addr} {size j : Nat} {b : BitVec 8}
    (hs : Scr s base size) (hj : K.bits+j<size)
    (hc : s.gpr .esi=BitVec.ofNat 32 j) (hm : s.mem (off base (K.bits+j))=b) :
    WP isa (.block (Naf.digitRead K)) s fun t =>
      t.gpr .ebx=b.setWidth 32 ∧ t.zf=some (decide (b=0)) ∧ CKeeps [.ecx,.ebx] s t := by
  unfold Naf.digitRead
  refine wp_movS rfl fun a ua _ => ?_
  refine wp_addS rfl fun c uc _ => ?_
  have kc := ua.keeps.trans uc.keeps
  have sc := hs.of_keeps kc (by decide)
  have ea : c.gpr .ecx=c.gpr .edi+BitVec.ofNat 32 j := by
    rw [uc.gpr,ua.gpr,ua.other _ (by decide),hc,kc.1 .edi (by decide)]
  refine wp_load8 (ea_winByte sc ea hj) (sc.read (by omega)) fun d ud => ?_
  refine wp_test fun t ut zt => WP.block_nil ?_
  have vd : d.gpr .ebx=b.setWidth 32 := by rw [ud.gpr,uc.mem,ua.mem,hm]
  refine ⟨(congrFun ut.gpr .ebx).trans vd,?_,?_,?_,?_,?_⟩
  · rw [zt,vd,BitVec.and_self,nafRead_zero]
  · intro r hr
    have hx : r≠.ecx := fun h => hr (h ▸ (by simp))
    have hb : r≠.ebx := fun h => hr (h ▸ (by simp))
    rw [ut.gpr,ud.other _ hb,uc.other _ hx,ua.other _ hx]
  · rw [ut.mem,ud.mem,uc.mem,ua.mem]
  · rw [ut.rd,ud.rd,uc.rd,ua.rd]
  · rw [ut.wr,ud.wr,uc.wr,ua.wr]

theorem nafDigitSign_ok (s : State) {b : BitVec 8} (hb : s.gpr .ebx=b.setWidth 32) :
    WP isa (.block [.alu .cmp .ebx (.imm 128)]) s fun t =>
      t.cf=some (decide (b.toNat<128)) ∧ CKeeps [] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,
    Option.bind_some,RegUpd.cf_arithFlags,hb,Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun _ _ => rfl,rfl,rfl,rfl⟩
  simp only [BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (show b.toNat<2^32 from by have:=b.isLt; omega)]
  rfl

theorem nafAbs_ok (s : State) {b : BitVec 8} (hb : s.gpr .ebx=b.setWidth 32) :
    WP isa (.block [.mov .eax (.imm 256),.alu .sub .eax (.reg .ebx),.mov .ebx (.reg .eax)]) s
      fun t => t.gpr .ebx=BitVec.ofNat 32 (256-b.toNat) ∧ CKeeps [.eax,.ebx] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,
    Option.map_some,Option.bind_some,RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,hb,
    ite_true,ite_false,reduceCtorEq,Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl⟩
  · have h : ∀ b : BitVec 8, (256 : BitVec 32)-b.setWidth 32=BitVec.ofNat 32 (256-b.toNat) := by decide
    exact h b
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,hr.1,hr.2,ite_false]

end VG.Proof.Weierstrass.X86
