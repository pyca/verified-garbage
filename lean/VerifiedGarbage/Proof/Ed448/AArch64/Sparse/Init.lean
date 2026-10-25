module

public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Loop
import VerifiedGarbage.Proof.X448.AArch64.Iter
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ed448.WnafWide.Recoding

/-! The in-place recoder's initialized carry and zero lookahead padding. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.Ed448.WnafWide
open VG.Impl.X448.AArch64 (BITS)
open VG.Proof.X448.AArch64 (Scr Keeps off ofs Outside writeW_outside write8_eq)

private theorem half_word (wide:Bool) :
    (BitVec.ofNat 16 (half wide)).setWidth 64=BitVec.ofNat 64 (half wide) := by cases wide <;> rfl

theorem recodeInit_ok (wide:Bool) {s:State} {base:Addr} (hs:Scr s base) :
    WP isa (.block (recodeInit wide)) s fun u =>
      u.gpr .x19=0 ∧ u.gpr .x6=BitVec.ofNat 64 (half wide) ∧
      Keeps [.x4,.x19,.x6] s u ∧
      u.mem=s.mem.writeW (off base (BITS+456)) (0 : BitVec 64) := by
  have hw:=hs.write (d:=BITS+456) (n:=8) (by decide)
  have enc:(BITS+456)%8=0 ∧ BITS+456<32768 := by decide
  apply WP.of_runBlock
  simp only [recodeInit,runBlock_cons,runStep_some,runBlock_nil,exec,Size.bits,
    Nat.reduceMul,Nat.reduceLT,ite_true,BitVec.shiftLeft_zero,addr,Size.bytes,enc,and_self,
    RegUpd.gpr_write,RegUpd.wr_write,RegUpd.mem_write,RegUpd.rd_write,State.read,BitVec.setWidth_eq,hs.x3,State.store,hw,Option.bind_some,
    write8_eq,half_word,ite_false,reduceCtorEq,Option.some.injEq,exists_eq_left']
  refine ⟨by trivial,by trivial,⟨fun r hr => ?_,rfl,rfl⟩,by trivial⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
  simp only [RegUpd.gpr_write,hr.1,hr.2.1,hr.2.2,ite_false]

private theorem zero_padding (m:Mem) (base:Addr) {j:Nat} (hj:456≤j) (hj':j<464) :
    (m.writeW (off base (BITS+456)) (0 : BitVec 64)) (off base (BITS+j))=0 := by
  have ha:off base (BITS+j)=off base (BITS+456)+BitVec.ofNat 64 (j-456) := by
    symm
    rw [off,off,Offset.add_add]
    exact congrArg (fun n => base+BitVec.ofNat 64 n) (by omega)
  simp only [Mem.writeW,Mem.write,Nat.reduceDiv,BitVec.setWidth_eq]
  rw [ha,Mem.sub_ofNat_toNat _ (by omega)]
  rw [ite_eq_left (by omega)]
  exact BitVec.extractLsb'_zero (w:=64) (start:=8*(j-456)) (len:=8)

theorem init_ok (wide:Bool) {s:State} {base:Addr} (hs:Scr s base) {k:Nat} (hk:k<VG.Impl.Ed448.WnafWide.scalarLimit)
    (hb:∀ j<456,s.mem (off base (BITS+j))=BitVec.ofNat 8 (WnafWide.bit k j)) :
    WP isa (.block (recodeInit wide)) s (RecInv base wide k s 0) := by
  refine WP.mono (recodeInit_ok wide hs) fun u ⟨u19,u6,uk,um⟩ => ?_
  have ku:Keeps recClob s u := uk.mono (by decide)
  have fo:Outside base (BITS+456) 8 s.mem u.mem := by
    rw [um]
    exact writeW_outside _ _ _ (by decide)
  refine ⟨hs.of_keeps ku (by decide),u19,?_,ku,fo.mono (by omega) (by omega),?_,?_⟩
  · refine ⟨half wide,by cases wide <;> decide,u6,?_⟩
    simp only [residual,Nat.pow_zero,Nat.div_one]
  · intro j hj
    omega
  · intro j _ hj
    by_cases h456:j<456
    · rw [fo _ (Or.inl (by
        rw [VG.Proof.X448.AArch64.ofs_off' base (by simp only [BITS];omega)]
        omega))]
      exact hb j h456
    · have hdiv:k/2^j=0 := WnafWide.tail_quotient hk (by omega)
      rw [um,zero_padding _ _ (by omega) hj]
      simp only [WnafWide.bit,hdiv,Nat.zero_mod]
      rfl

end VG.Proof.Ed448.AArch64.Sparse
