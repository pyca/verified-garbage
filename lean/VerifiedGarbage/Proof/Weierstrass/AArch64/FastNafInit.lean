import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafState
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvWords

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 VG.Proof.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

theorem fastInit_ok (K : WinCfg) {w : Nat} (hw : FastNaf.Width w) {s : State} {base : Addr} {size src : Nat}
    (hs : Scr s base size) (hsrc : src+32≤size) (hsrc8 : src%8=0) (hbits : K.bits<4096) :
    WP isa (.block (Impl.Weierstrass.AArch64.FastNaf.init K src w)) s fun t =>
      FastPrepCore base size K.bits w (wordsVal s.mem base src 4) 0 t ∧
      KeepRegs nafPrepClob s t ∧ t.mem=s.mem := by
  have he : Impl.Weierstrass.AArch64.FastNaf.init K src w = VG.Impl.Mont.AArch64.loads [.x5,.x6,.x7,.x8] src ++
      [.movz .x .x9 0 0,.movz .x .x10 (BitVec.ofNat 16 (2^w-1)) 0,.movz .x .x11 (BitVec.ofNat 16 (2^(w-1))) 0,.movz .x .x12 0 0,
       .movz .x .x13 1 0,.movz .x .x19 257 0,.addImm .x .x20 .x0 K.bits] := by
    simp only [Impl.Weierstrass.AArch64.FastNaf.init,VG.Impl.Mont.AArch64.loads,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd]
  rw [he,WP.block_append_iff]
  refine WP.mono (nafLoads_ok hs hsrc hsrc8) fun a ⟨va,ka⟩ => ?_
  have sa := hs.of_keeps ka (by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,RegUpd.gpr_write,
    BitVec.setWidth_eq,show 16*0<Size.x.bits from by decide,hbits,ite_true,ite_false,reduceCtorEq,
    Option.some.injEq,exists_eq_left']
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_⟩,?_,ka.mem⟩
  · exact ⟨sa.x0,sa.wr,sa.nowrap,sa.enc⟩
  · simp only [FastNaf.residual_zero,nafVal5,RegUpd.gpr_write,ite_true,ite_false,reduceCtorEq,BitVec.setWidth_eq] at *
    simp only [regsVal] at va
    change _+2^256*0=_
    omega
  · rcases hw with rfl | rfl <;> rfl
  · rcases hw with rfl | rfl <;> rfl
  · rfl
  · rfl
  · simpa only [Nat.add_zero,RegUpd.gpr_write,ite_true,BitVec.setWidth_eq] using congrArg (fun x => x+BitVec.ofNat 64 K.bits) sa.x0
  · refine ⟨?_,ka.rd,ka.wr,ka.sp⟩
    intro r hr
    have hh : r≠.x9 ∧ r≠.x10 ∧ r≠.x11 ∧ r≠.x12 ∧ r≠.x13 ∧ r≠.x19 ∧ r≠.x20 := by
      simp only [nafPrepClob,List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
      exact ⟨hr.2.2.2.2.2.2.2.1,hr.2.2.2.2.2.2.2.2.1,hr.2.2.2.2.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.2.2.2.2.1,hr.2.2.2.2.2.2.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.2.2.2.2.2.2.1,hr.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
    simp only [RegUpd.gpr_write,hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2.1,hh.2.2.2.2.2.1,hh.2.2.2.2.2.2,ite_false]
    exact ka.gpr r (by
      intro hm
      exact hr ((by decide : ∀ q∈[Reg.x5,.x6,.x7,.x8],q∈nafPrepClob) r hm))

theorem fastClear_ok (K : WinCfg) {s : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) (hz : s.gpr .x12=0) (ha : K.bits%8=0) (hb : K.bits+264≤size) :
    WP isa (.block (Impl.Weierstrass.AArch64.FastNaf.clear K)) s fun t =>
      (∀ i<264,t.mem (off base (K.bits+i))=0) ∧ KeepRegs [] s t ∧ Outside base K.bits 264 s.mem t.mem := by
  refine WP.mono (zerosW_ok hs hz ha 33 hb) fun t ⟨ht,kt,ot⟩ => ⟨?_,kt,ot⟩
  intro i hi
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  rw [testBit_byte t.mem base (n:=33) (by omega) hb,ht]
  simp only [BitVec.ofNat_eq_ofNat,Nat.zero_testBit,BitVec.getLsbD_zero]

end VG.Proof.Weierstrass.AArch64
