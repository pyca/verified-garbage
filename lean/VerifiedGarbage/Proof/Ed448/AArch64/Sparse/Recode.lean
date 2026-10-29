module

public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Step

import VerifiedGarbage.Proof.X448.AArch64.Iter
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.X448.AArch64.BitWrite
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ed448.WnafWide.Recoding
/-! Complete full-width signed recoding, framed to its 464-byte digit buffer. -/

-- Formerly `VerifiedGarbage/Proof/Ed448/AArch64/Sparse/Loop.lean`, which only this module imported.
section

/-! The in-place public recoder preserves future input bits and completed digits. -/

section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.Ed448.WnafWide
open VG.Impl.X448.AArch64 (BITS)
open VG.Proof.X448.AArch64 (Scr Keeps off ofs Outside writeW8_apply writeW8_outside off_eq_iff)

structure RecInv (base : Addr) (wide : Bool) (k : Nat) (s₀ : State) (i : Nat) (s : State) : Prop where
  scr : Scr s base
  x19 : s.gpr .x19=BitVec.ofNat 64 i
  carry : ∃ c≤radix wide, s.gpr .x6=BitVec.ofNat 64 c ∧ residual wide k i+half wide=k/2^i+c
  keep : Keeps recClob s₀ s
  mem : Outside base BITS 464 s₀.mem s.mem
  digits : ∀ j<i, s.mem (off base (BITS+j))=Enc wide k j
  bits : ∀ j, i≤j → j<464 → s.mem (off base (BITS+j))=BitVec.ofNat 8 (WnafWide.bit k j)

theorem RecInv.advance {base : Addr} {wide : Bool} {k i : Nat} {s₀ s u : State}
    (h:RecInv base wide k s₀ i s) (hi:i<464) (g:StepOut base wide k i s u) :
    RecInv base wide k s₀ (i+1) u := by
  refine ⟨g.scr,g.x19,g.carry,h.keep.trans g.keep,?_,?_,?_⟩
  · intro p hp
    rw [g.mem,writeW8_outside _ base _ (by simp only [BITS];omega) (by omega)]
    exact h.mem p hp
  · intro j hj
    rw [g.mem,writeW8_apply]
    simp only [off_eq_iff base (d:=BITS+j) (e:=BITS+i) (by simp only [BITS];omega) (by simp only [BITS];omega)]
    by_cases he:j=i
    · subst j
      simp only [ite_true]
    · rw [ite_eq_right (by omega)]
      exact h.digits j (by omega)
  · intro j hj hj'
    rw [g.mem,writeW8_outside _ base _ (by simp only [BITS];omega) (by
      rw [VG.Proof.X448.AArch64.ofs_off' base (by simp only [BITS];omega)]
      omega)]
    exact h.bits j (by omega) hj'

theorem recodeLoop_ok (wide : Bool) {base : Addr} {k i : Nat} {s₀ s : State}
    (hi:i<456) (h:RecInv base wide k s₀ i s) :
    WP isa (.loop (.block (recodeBody wide)) (.nonzero .x .x9)) s
      (RecInv base wide k s₀ 456) := by
  refine WP.loop (M:=isa) (body:=.block (recodeBody wide)) (c:=.nonzero .x .x9)
    (Q:=RecInv base wide k s₀ 456)
    (fun m s => ∃ i, m=456-i ∧ i<456 ∧ RecInv base wide k s₀ i s) ?_ (456-i) s ⟨i,rfl,hi,h⟩
  rintro m s ⟨i,rfl,hi,h⟩
  obtain ⟨c,hc,h6,hrel⟩:=h.carry
  refine WP.mono (recodeBody_ok wide h.scr hi hc h.x19 h6 hrel
    (fun j hj => by simpa only [Nat.add_assoc] using h.bits (i+j) (by omega) (by omega))) fun u ⟨g,gz⟩ => ?_
  have hu:=h.advance (by omega) g
  simp only [eval,State.read,BitVec.setWidth_eq,bne,gz]
  by_cases hn:i+1<456
  · refine .inr ⟨?_,456-(i+1),by omega,i+1,rfl,hn,hu⟩
    simp only [decide_eq_false (by omega : ¬i+1=456),Bool.not_false]
  · have he:i+1=456 := by omega
    rw [he] at hu
    exact .inl ⟨by simp only [he,decide_true,Bool.not_true],hu⟩

theorem recodeTail_ok (wide : Bool) {base : Addr} {k i n : Nat} {s₀ s : State}
    (hk:k<VG.Impl.Ed448.WnafWide.scalarLimit) (hi:456≤i) (hend:i+n≤464) (h:RecInv base wide k s₀ i s) :
    WP isa (recodeTail wide n) s (RecInv base wide k s₀ (i+n)) := by
  induction n generalizing i s with
  | zero =>
    simpa only [recodeTail,Nat.add_zero] using (WP.block_nil h)
  | succ n ih =>
    rw [recodeTail]
    obtain ⟨c,hc,h6,hrel⟩:=h.carry
    refine WP.seq (WP.mono (zeroStep_ok wide h.scr hk (by omega) hi hc h.x19 h6 hrel)
      fun u g => ?_)
    have hu:=h.advance (by omega) g
    have hr:=ih (i:=i+1) (by omega) (by omega) hu
    have he:i+1+n=i+(n+1) := by omega
    rw [he] at hr
    exact hr

end VG.Proof.Ed448.AArch64.Sparse
end

end

-- Formerly `VerifiedGarbage/Proof/Ed448/AArch64/Sparse/Init.lean`, which only this module imported.
section

/-! The in-place recoder's initialized carry and zero lookahead padding. -/

section

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
end

end

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.X448.AArch64 (BITS)
open VG.Proof.X448.AArch64 (Scr Keeps Outside off)

structure Digits (base : Addr) (wide : Bool) (k : Nat) (s₀ s : State) : Prop where
  scr : Scr s base
  keep : Keeps recClob s₀ s
  mem : Outside base BITS 464 s₀.mem s.mem
  digits : ∀ j<464,s.mem (off base (BITS+j))=Enc wide k j

theorem recodeBits_ok (wide : Bool) {s : State} {base : Addr} (hs : Scr s base)
    {k : Nat} (hk:k<VG.Impl.Ed448.WnafWide.scalarLimit)
    (hb:∀ j<456,s.mem (off base (BITS+j))=BitVec.ofNat 8 (WnafWide.bit k j)) :
    WP isa (recodeBits wide) s (Digits base wide k s) := by
  unfold recodeBits
  refine WP.seq (WP.mono (init_ok wide hs hk hb) fun u hu => ?_)
  refine WP.seq (WP.mono (recodeLoop_ok wide (by decide) hu) fun v hv => ?_)
  refine WP.mono (recodeTail_ok wide hk (by decide) (by decide) hv) fun t ht => ?_
  exact ⟨ht.scr,ht.keep,ht.mem,ht.digits⟩

end VG.Proof.Ed448.AArch64.Sparse
