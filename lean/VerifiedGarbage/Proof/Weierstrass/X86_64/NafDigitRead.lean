import VerifiedGarbage.Impl.Weierstrass.X86_64.Naf
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafPrep

/-! Reading a signed public digit and testing its sign and zero case. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.X25519.X86_64

def nafMagnitude (b : BitVec 8) : Nat := if b.toNat<128 then b.toNat else 256-b.toNat

def nafNegative (b : BitVec 8) : Bool := decide (128≤b.toNat)

private theorem nafRead_zero : ∀ b : BitVec 8, (b.setWidth 64==0)=decide (b=0) := by decide

theorem nafRead_ok {K : WinCfg} {s : State} {base : Addr} {size j : Nat} {b : BitVec 8}
    (hs : Scr s base size) (hj : K.bits+j<size)
    (hc : s.gpr .rbx=BitVec.ofNat 64 j) (hm : s.mem (off base (K.bits+j))=b) :
    WP isa (.block (Naf.digitRead K)) s fun t =>
      t.gpr .r8=b.setWidth 64 ∧ t.zf=some (decide (b=0)) ∧ Keeps [.r8] s t := by
  have hr : InRegions (s.rd++s.wr) (off base (K.bits+j)) 1 :=
    ⟨_,List.mem_append_right _ hs.wr,hs.contains (by omega) (by decide)⟩
  apply WP.of_runBlock
  simp only [Naf.digitRead,runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,
    Option.map_some,Option.bind_some,State.load8,ea_tbl hs.rdi hc,hr,hm,
    RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,RegUpd.zf_arithFlags,BitVec.and_self,
    ite_true,Option.some.injEq,exists_eq_left']
  refine ⟨trivial,?_,fun r hr => ?_,rfl,rfl,rfl⟩
  · exact nafRead_zero b
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,hr,ite_false]

theorem nafSign_ok (s : State) {b : BitVec 8} (hb : s.gpr .r8=b.setWidth 64) :
    WP isa (.block [.alu .cmp .r8 (.imm 128)]) s fun t =>
      t.cf=some (decide (b.toNat<128)) ∧ Keeps [] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,
    Option.bind_some,RegUpd.cf_arithFlags,hb,Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun _ _ => rfl,rfl,rfl,rfl⟩
  congr 1

theorem nafAbs_ok (s : State) {b : BitVec 8} (hb : s.gpr .r8=b.setWidth 64) :
    WP isa (.block [.mov32 .rax (.imm 256),.alu .sub .rax (.reg .r8),.mov .r8 (.reg .rax)]) s
      fun t => t.gpr .r8=BitVec.ofNat 64 (256-b.toNat) ∧ Keeps [.rax,.r8] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,readSrc32,State.setReg32,
    Option.map_some,Option.bind_some,RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,hb,
    ite_true,ite_false,reduceCtorEq,Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl⟩
  · have h : ∀ b : BitVec 8, (256 : BitVec 64)-b.setWidth 64=BitVec.ofNat 64 (256-b.toNat) := by decide
    exact h b
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,hr.1,hr.2,ite_false]

end VG.Proof.Weierstrass.X86_64
