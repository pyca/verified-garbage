module

import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafState
import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafSubtract
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Impl.Weierstrass.X86_64.FastNaf
public import VerifiedGarbage.Proof.Mont.X86_64.Csub
public import VerifiedGarbage.Proof.Weierstrass.FastNaf
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafSubtract

/-! The width-nine recoder's state: its digits as sixteen-bit words, and their stores. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Mont.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.X25519.X86_64

/-- `FastPrepState` for width nine: the digits so far as sixteen-bit words, little-endian, the rest
of the `2 (64 n + 1)` bytes zero. -/
structure FastPrepState16 (n : Nat) (base : Addr) (size bits k j : Nat) (s : State) : Prop where
  scr : Scr s base size
  value : nafValN n s=FastNaf.residual 9 k j
  count : s.gpr .rbx=BitVec.ofNat 64 j
  digits : ∀ i<2*(64*n+1),s.mem (off base (bits+i))=if i/2<j then FastNaf.wbyte k i else 0

theorem fastWord16 (k j : Nat) :
    (BitVec.ofInt 64 (FastNaf.digit 9 k j)).setWidth 16=FastNaf.word k j := by
  apply BitVec.eq_of_toNat_eq
  have hw := FastNaf9.word_toNat k j
  have hb := FastNaf9.magnitude_le k j
  have hm : FastNaf.magnitude 9 k j=FastNaf9.magnitude k j := by
    simp only [FastNaf.magnitude,FastNaf.ne_9_7,ite_true,ite_false]
  have hn : FastNaf.negative 9 k j=FastNaf9.negative k j := by
    simp only [FastNaf.negative,FastNaf.ne_9_7,ite_true,ite_false]
  rw [BitVec.toNat_setWidth,fastWord_toNat,FastNaf.word,hw,hm,hn]
  cases hn' : FastNaf9.negative k j
  · simp only [Bool.false_eq_true,ite_false]; omega
  · have hp := FastNaf9.negative_magnitude_pos k j hn'
    simp only [ite_true]; omega

theorem ea_tbl16 {s : State} {base : Addr} (hb : s.gpr .rdi=base) {t : Nat}
    (ht : s.gpr .rbx=BitVec.ofNat 64 t) (d : Nat) :
    s.ea (FastNaf.tbl16 d)=off base (d+2*t) := by
  simp only [State.ea,FastNaf.tbl16,hb,ht,BitVec.ofInt_natCast]
  rw [BitVec.ofNat_mul_ofNat,Offset.add_add,Nat.add_comm,Nat.mul_comm]

theorem writeW16_apply (m : Mem) (a x : Addr) (v : BitVec 16) :
    (m.writeW a v) x=if (x-a).toNat<2 then v.extractLsb' (8*(x-a).toNat) 8 else m x := by
  simp only [Mem.writeW,Mem.write,Nat.reduceDiv,Nat.reduceMul,BitVec.setWidth_eq]

theorem writeW16_at (m : Mem) (base : Addr) {d e : Nat} (v : BitVec 16) (he : e<2) : (m.writeW (off base d) v) (off base (d+e))=v.extractLsb' (8*e) 8 := by
  have hs : (off base (d+e)-off base d).toNat=e := by
    simp only [off]
    rw [Offset.add_sub_add_left,Offset.ofNat_sub_ofNat (by omega),Nat.add_sub_cancel_left,
      BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  rw [writeW16_apply,hs,ite_eq_left he]

theorem writeW16_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 16) (hd : d+2≤2^64)
    {x : Addr} (hx : ofs base x<d ∨ d+2≤ofs base x) : (m.writeW (off base d) v) x=m x := by
  have he : x-off base d=BitVec.ofNat 64 (ofs base x)-BitVec.ofNat 64 d := by
    simp only [off,ofs,BitVec.ofNat_toNat,BitVec.setWidth_eq]
    rw [Offset.sub_add_eq]
  rw [writeW16_apply,ite_eq_right]
  rw [he]
  exact Offset.not_lt_sub_ofNat hx (BitVec.isLt _) (by decide) hd

theorem fastStore16_ok {s : State} {base : Addr} {size bits k j : Nat}
    (hs : Scr s base size) (hb : bits+2*j+2≤size)
    (hc : s.gpr .rbx=BitVec.ofNat 64 j)
    (hd : s.gpr .rcx=BitVec.ofInt 64 (FastNaf.digit 9 k j)) :
    WP isa (.block [.store16 (FastNaf.tbl16 bits) .rcx]) s fun t =>
      t.mem=s.mem.writeW (off base (bits+2*j)) (FastNaf.word k j) ∧ KeepRegs [] s t := by
  have hw : InRegions s.wr (off base (bits+2*j)) 2 :=
    ⟨_,hs.wr,hs.contains (by omega) (by decide)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,State.store16,
    ea_tbl16 hs.rdi hc,hw,hd,fastWord16,ite_true,Option.some.injEq,exists_eq_left']
  exact ⟨trivial,fun _ _ => rfl,rfl,rfl⟩

theorem FastPrepState16.of_keeps {s t : State} {base : Addr} {size n bits k j : Nat}
    (h : FastPrepState16 n base size bits k j s) {rs : List Reg} (hk : Keeps rs s t)
    (hr : ∀ r∈[Reg.rdi,.rbx,.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15,.rbp,.rsi],r∉rs) :
    FastPrepState16 n base size bits k j t := by
  refine ⟨h.scr.of_keeps hk (hr _ (by simp)),?_,?_,?_⟩
  · rw [nafValN_keep hk.1 (fun r hr' => hr r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr')))]
    exact h.value
  · exact (hk.1 .rbx (hr _ (by simp))).trans h.count
  · rw [hk.2.1]
    exact h.digits

/-- Two bytes, little-endian, are the word they were cut from. -/
theorem readW16_bytes (m : Mem) (a : Addr) {d : BitVec 16} (h0 : m a=d.extractLsb' 0 8)
    (h1 : m (a+1)=d.extractLsb' 8 8) : m.readW a 16=d := by
  simp only [Mem.readW,Nat.reduceDiv,Mem.read,h0,h1]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth,BitVec.getLsbD_append,BitVec.getLsbD_extractLsb']
  by_cases h8 : i<8
  · simp [h8,hi]
  · have h16 : i-8<8 := by omega
    simp only [h8,ite_false]
    simp only [h16,hi,decide_true,Bool.true_and]
    rw [show 8+(i-8)=i by omega]
    simp only [ite_true]

/-- `r8` = the sixteen-bit digit `rbx` at `bits`, and its test. -/
theorem nafRead16_ok {s : State} {base : Addr} {size bits j : Nat} {d : BitVec 16}
    (hs : Scr s base size) (hj : bits+2*j+2≤size) (hc : s.gpr .rbx=BitVec.ofNat 64 j)
    (h0 : s.mem (off base (bits+2*j))=d.extractLsb' 0 8)
    (h1 : s.mem (off base (bits+2*j+1))=d.extractLsb' 8 8) :
    WP isa (.block [.movzx16 .r8 (FastNaf.tbl16 bits),.alu .test .r8 (.reg .r8)]) s fun t =>
      t.gpr .r8=d.setWidth 64 ∧ t.zf=some (decide (d=0)) ∧ Keeps [.r8] s t := by
  have hr : InRegions (s.rd++s.wr) (off base (bits+2*j)) 2 :=
    ⟨_,List.mem_append_right _ hs.wr,hs.contains (by omega) (by decide)⟩
  have h1' : s.mem (off base (bits+2*j)+1)=d.extractLsb' 8 8 := by
    rw [← h1]; simp only [off]
    rw [BitVec.add_assoc,show BitVec.ofNat 64 (bits+2*j)+1=BitVec.ofNat 64 (bits+2*j+1) from by
      simp only [BitVec.ofNat_add]; rfl]
  have hw := readW16_bytes s.mem _ h0 h1'
  have hz : ((d.setWidth 64 &&& d.setWidth 64)==0)=decide (d=0) := by
    rw [BitVec.and_self]
    by_cases h : d=0
    · subst h; rfl
    · have : d.setWidth 64≠0 := by
        intro he; apply h; apply BitVec.eq_of_toNat_eq
        have := congrArg BitVec.toNat he
        simp only [BitVec.toNat_setWidth] at this ⊢
        rwa [Nat.mod_eq_of_lt (by have := d.isLt; omega)] at this
      rw [beq_false_of_ne this,decide_eq_false h]
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,
    Option.map_some,Option.bind_some,State.load16,ea_tbl16 hs.rdi hc,hr,hw,
    RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,RegUpd.zf_arithFlags,
    ite_true,Option.some.injEq,exists_eq_left']
  refine ⟨trivial,?_,fun r hr => ?_,rfl,rfl,rfl⟩
  · exact hz
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,hr,ite_false]

end VG.Proof.Weierstrass.X86_64
