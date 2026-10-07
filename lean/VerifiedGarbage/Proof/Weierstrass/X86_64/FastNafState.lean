import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafChoose
import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafShift
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafPrep

/-! Digit stores, public index updates and the prezeroed sparse recoder state. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Mont.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.X25519.X86_64

structure FastPrepState (base : Addr) (size bits w k j : Nat) (s : State) : Prop where
  scr : Scr s base size
  value : nafVal5 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) (s.gpr .r12)=FastNaf.residual w k j
  count : s.gpr .rbx=BitVec.ofNat 64 j
  digits : ∀ i<257,s.mem (off base (bits+i))=if i<j then FastNaf.byte w k i else 0

theorem fastByte_word (w k j : Nat) :
    (BitVec.ofInt 64 (FastNaf.digit w k j)).setWidth 8=FastNaf.byte w k j := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth,fastWord_toNat,FastNaf.byte_toNat]
  have hb := fastMagnitude_bound w k j
  cases hn : FastNaf.negative w k j
  · simp only [Bool.false_eq_true,ite_false]; omega
  · have hp := FastNaf.negative_magnitude_pos w k j hn
    simp only [ite_true]; omega

theorem fastStore_ok {s : State} {base : Addr} {size bits w k j : Nat}
    (hs : Scr s base size) (hb : bits+264≤size) (hj : j<257)
    (hc : s.gpr .rbx=BitVec.ofNat 64 j)
    (hd : s.gpr .rcx=BitVec.ofInt 64 (FastNaf.digit w k j)) :
    WP isa (.block [.store8 (tbl bits) .rcx]) s fun t =>
      t.mem=s.mem.writeW (off base (bits+j)) (FastNaf.byte w k j) ∧ KeepRegs [] s t := by
  have hw : InRegions s.wr (off base (bits+j)) 1 :=
    ⟨_,hs.wr,hs.contains (by omega) (by decide)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,State.store8,
    ea_tbl hs.rdi hc,hw,hd,fastByte_word,ite_true,Option.some.injEq,exists_eq_left']
  exact ⟨trivial,fun _ _ => rfl,rfl,rfl⟩

theorem fastAdvance_ok (s : State) {j d : Nat} (hd : d=1 ∨ d=5 ∨ d=7)
    (hc : s.gpr .rbx=BitVec.ofNat 64 j) :
    WP isa (.block (Impl.Weierstrass.X86_64.FastNaf.advance d)) s fun t =>
      t.gpr .rbx=BitVec.ofNat 64 (j+d) ∧ Keeps [.rbx] s t := by
  have he : (BitVec.ofNat 32 d).signExtend 64=BitVec.ofNat 64 d := by
    rcases hd with rfl|rfl|rfl <;> rfl
  apply WP.of_runBlock
  simp only [Impl.Weierstrass.X86_64.FastNaf.advance,runBlock_cons,runStep_some,runBlock_nil,
    exec,execAlu,readSrc,Option.bind_some,Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl⟩
  · simp only [RegUpd.gpr_arithFlags,RegUpd.gpr_setReg,ite_true,hc,he,BitVec.ofNat_add]
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_arithFlags,RegUpd.gpr_setReg,hr,ite_false]

theorem fastCompare_ok (s : State) {j : Nat} (hj : j≤263)
    (hc : s.gpr .rbx=BitVec.ofNat 64 j) :
    WP isa (.block [.alu .cmp .rbx (.imm 257)]) s fun t =>
      t.cf=some (decide (j<257)) ∧ Keeps [] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,
    Option.bind_some,RegUpd.cf_arithFlags,Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun _ _ => rfl,rfl,rfl,rfl⟩
  simp only [hc,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show j<2^64 from by omega)]
  rfl

private theorem clearWords_ok {s : State} {base : Addr} {size bits n : Nat}
    (hs : Scr s base size) (hb : bits+8*n≤size) :
    WP isa (.block (setConst n bits 0)) s fun t =>
      wordsVal t.mem base bits n=0 ∧ KeepRegs [.rax] s t ∧ Outside base bits (8*n) s.mem t.mem :=
  setConst_ok hs hb (Nat.two_pow_pos _)

theorem fastClear_ok {s : State} {base : Addr} {size bits : Nat}
    (hs : Scr s base size) (hb : bits+264≤size) :
    WP isa (.block (setConst 33 bits 0)) s fun t =>
      (∀ i<264,t.mem (off base (bits+i))=0) ∧ KeepRegs [.rax] s t ∧ Outside base bits 264 s.mem t.mem := by
  refine WP.mono (clearWords_ok (n:=33) hs hb) fun t ⟨ht,kt,ot⟩ => ⟨?_,kt,ot⟩
  intro i hi
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  rw [testBit_byte t.mem base (n:=33) (by omega) hb,ht]
  simp only [BitVec.ofNat_eq_ofNat,Nat.zero_testBit,BitVec.getLsbD_zero]

theorem fastPrepInit_ok {s : State} {base : Addr} {size src bits w : Nat}
    (hs : Scr s base size) (hsrc : src+32≤size) (hb : bits+264≤size) :
    WP isa (.block (Naf.init src++setConst 33 bits 0)) s fun t =>
      FastPrepState base size bits w (wordsVal s.mem base src 4) 0 t ∧
      KeepRegs nafPrepClob s t ∧ Outside base bits 264 s.mem t.mem := by
  rw [WP.block_append_iff]
  refine WP.mono (nafPrepInit_ok (bits:=bits) hs hsrc) fun a ⟨ia,ka,ma⟩ => ?_
  refine WP.mono (fastClear_ok ia.scr hb) fun t ⟨zt,kt,ot⟩ => ?_
  refine ⟨⟨ia.scr.of_keepRegs kt (by decide),?_,?_,?_⟩,ka.trans (kt.mono (by decide)),?_⟩
  · rw [kt.gpr .r8 (by decide),kt.gpr .r9 (by decide),kt.gpr .r10 (by decide),
      kt.gpr .r11 (by decide),kt.gpr .r12 (by decide),ia.value,FastNaf.residual_zero]
    rfl
  · exact (kt.gpr .rbx (by decide)).trans ia.count
  · intro i hi
    simpa only [Nat.not_lt_zero,ite_false] using zt i (by omega)
  · rw [ma] at ot
    exact ot

end VG.Proof.Weierstrass.X86_64
