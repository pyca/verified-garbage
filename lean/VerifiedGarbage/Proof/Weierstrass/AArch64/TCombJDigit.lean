import VerifiedGarbage.Impl.Weierstrass.AArch64.TCombJ
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombDigit
import VerifiedGarbage.Proof.Weierstrass.AArch64.Zero
import VerifiedGarbage.Proof.Weierstrass.Booth

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

private theorem sbcMask3_ok (s : State) (hz : s.gpr .x7=0) :
    WP isa (.block [.sbc .x .x3 .x7 .x7]) s fun t =>
      t.gpr .x3=mask ((!s.c)=true) ∧ Keeps [.x3] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,RegUpd.gpr_write_self,
    BitVec.setWidth_eq,hz,Option.some.injEq,exists_eq_left']
  refine ⟨by cases s.c <;> decide,fun r hr => ?_,rfl,rfl,rfl,rfl⟩
  exact RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr)

private theorem isNonzero_ok (s : State) (hz : s.gpr .x7=0) :
    WP isa (.block [.subs .x .x16 .x7 .x1,.sbc .x .x3 .x7 .x7]) s fun t =>
      t.gpr .x3=mask (s.gpr .x1≠0) ∧ Keeps [.x3,.x16] s t := by
  rw [←List.singleton_append,WP.block_append_iff]
  refine WP.mono (subc_ok s .x16 .x7 .x1 true (c:=true) rfl) fun a ⟨_,ac,ka⟩ => ?_
  refine WP.mono (sbcMask3_ok a (by rw [ka.gpr _ (by decide),hz])) fun t ⟨ht,kt⟩ =>
    ⟨?_,(ka.mono (by sub_regs)).trans (kt.mono (by sub_regs))⟩
  rw [ht,ac,not_carryOut,hz]
  simp only [Bool.not_true,Bool.toNat_false,Nat.add_zero,decide_eq_true_eq,mask]
  congr 1
  apply propext
  change 0<(s.gpr .x1).toNat ↔ s.gpr .x1≠0
  rw [Nat.pos_iff_ne_zero]
  exact not_congr ⟨fun h => BitVec.eq_of_toNat_eq h,fun h => by rw [h]; rfl⟩

/-- The full-word nonzero mask, without a branch or secret address. -/
theorem nzMask_full_ok {s : State} {base : Addr} {size n z : Nat} (hs : Scr s base size)
    (hn : 0<n) (hz : z+8*n≤size) (hz8 : z%8=0) :
    WP isa (.block (nzMask n z)) s fun t =>
      t.gpr .x3=mask (wordsVal s.mem base z n≠0) ∧ Keeps [.x1,.x2,.x3,.x7,.x16] s t ∧ t.gpr .x7=0 := by
  rw [nzMask,List.append_assoc,WP.block_append_iff,←List.singleton_append,WP.block_append_iff]
  refine WP.mono (zero7_ok s) fun a ⟨a7,ka⟩ => ?_
  refine WP.mono (ld_ok (hs.of_keeps ka (by decide)) (d:=z) (by omega) hz8 .x1) fun b ⟨b1,kb,_⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ors_ok ((hs.of_keeps ka (by decide)).of_keeps kb (by decide)) hz8 (n-1) (by omega))
    fun c ⟨ce,kc⟩ => ?_
  rw [b1,kb.mem,ka.mem] at ce
  have eqz : c.gpr .x1=0 ↔ wordsVal s.mem base z n=0 := by
    rw [ce,wordsVal_eq_zero_iff]
    constructor
    · intro ⟨h0,h⟩ j hj
      cases j with
      | zero => simpa using h0
      | succ j => exact h j (by omega)
    · intro h
      exact ⟨by simpa using h 0 hn,fun j hj => h (j+1) (by omega)⟩
  refine WP.mono (isNonzero_ok c (by rw [kc.gpr _ (by decide),kb.gpr _ (by decide),a7]))
    fun t ⟨ht,kt⟩ => ⟨?_,?_,?_⟩
  · simpa only [mask,ne_eq,eqz] using ht
  · exact (((ka.mono (by sub_regs)).trans (kb.mono (by sub_regs))).trans
      (kc.mono (by sub_regs))).trans (kt.mono (by sub_regs))
  · rw [kt.gpr _ (by decide),kc.gpr _ (by decide),kb.gpr _ (by decide),a7]

theorem nzMask_ok {s : State} {base : Addr} {size n z : Nat} (hs : Scr s base size)
    (hn : 0<n) (hz : z+8*n≤size) (hz8 : z%8=0) :
    WP isa (.block (nzMask n z)) s fun t =>
      t.gpr .x3=mask (wordsVal s.mem base z n≠0) ∧ Keeps [.x1,.x2,.x3,.x7,.x16] s t :=
  WP.mono (nzMask_full_ok hs hn hz hz8) fun _ h => ⟨h.1,h.2.1⟩

theorem bcar_testBit {w k j : Nat} (hj : 1≤j) : bcar w k j=(k.testBit (w*j-1)).toNat := by
  simp only [bcar,show j≠0 by omega,↓reduceIte,Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (k/2^(w*j-1)) with h | h <;> simp [h]

theorem bcar_succ_testBit {w : Nat} (hw : 1≤w) (k j : Nat) :
    bcar w k (j+1)=(k.testBit (w*j+(w-1))).toNat := by
  rw [bcar_testBit (by omega),show w*(j+1)-1=w*j+(w-1) by rw [Nat.mul_succ]; omega]

theorem byte_testBit (b : Bool) : (if b then (1 : BitVec 8) else 0)=BitVec.ofNat 8 b.toNat := by
  cases b <;> rfl


private theorem bmag_fact : ∀ w<9,∀ m<2^w+1,∀ s<2,
    (BitVec.ofNat 64 m ^^^ ((0 : BitVec 64)-BitVec.ofNat 64 s))-((0 : BitVec 64)-BitVec.ofNat 64 s)+
      (((0 : BitVec 64)-BitVec.ofNat 64 s) &&& BitVec.ofNat 64 (2^w))=
    BitVec.ofNat 64 (if s=1 then 2^w-m else m) := by decide +kernel

/-- The magnitude arithmetic following the bit-window load. -/
theorem bmagTail_ok (K : TCombCfg) {s : State} {m sb : Nat} (hw : K.w<9)
    (hm2 : m<2^K.w+1) (hs2 : sb<2) (hd : K.bits+K.w-1<4096)
    (hx : s.gpr .x2=BitVec.ofNat 64 m)
    (hr : InRegions (s.rd++s.wr) (s.gpr .x16+BitVec.ofNat 64 (K.bits+K.w-1)) 1)
    (hm : s.mem (s.gpr .x16+BitVec.ofNat 64 (K.bits+K.w-1))=BitVec.ofNat 8 sb) :
    WP isa (.block (([zero7,.ldrb .x4 .x16 (K.bits+K.w-1),.sub .x .x3 .x7 .x4,
      .logic .eor .x .x2 .x2 .x3,.sub .x .x2 .x2 .x3] : List Instr) ++
      const64 .x9 (BitVec.ofNat 64 (2^K.w)) ++
      ([.logic .and .x .x3 .x3 .x9,.add .x .x2 .x2 .x3] : List Instr))) s fun t =>
      t.gpr .x2=BitVec.ofNat 64 (if sb=1 then 2^K.w-m else m) ∧
      Keeps [.x2,.x3,.x4,.x7,.x9] s t := by
  have es : (BitVec.ofNat 8 sb).setWidth 64=BitVec.ofNat 64 sb := by
    rcases (by omega : sb=0 ∨ sb=1) with rfl | rfl <;> rfl
  have pre : WP isa (.block [zero7,.ldrb .x4 .x16 (K.bits+K.w-1),.sub .x .x3 .x7 .x4,
      .logic .eor .x .x2 .x2 .x3,.sub .x .x2 .x2 .x3]) s fun a =>
      a.gpr .x2=(BitVec.ofNat 64 m ^^^ ((0 : BitVec 64)-BitVec.ofNat 64 sb))-
        ((0 : BitVec 64)-BitVec.ofNat 64 sb) ∧
      a.gpr .x3=(0 : BitVec 64)-BitVec.ofNat 64 sb ∧ Keeps [.x2,.x3,.x4,.x7] s a := by
    apply WP.of_runBlock
    simp only [zero7,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,State.load,addr,
      Size.bits,Nat.mod_one,show K.bits+K.w-1<4096*1 by omega,and_self,
      show 16*0<64 by decide,ite_true,RegUpd.gpr_write,RegUpd.rd_write,RegUpd.wr_write,
      RegUpd.mem_write,BitVec.setWidth_eq,reduceCtorEq,ite_false,hr,read1_zext,hm,
      Option.map_some,Option.bind_some,Option.some.injEq,exists_eq_left',es,hx]
    refine ⟨rfl,rfl,fun r hr' => ?_,rfl,rfl,rfl,rfl⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr'
    simp only [RegUpd.gpr_write,hr'.1,hr'.2.1,hr'.2.2.1,hr'.2.2.2,ite_false]
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono pre fun a ⟨a2,a3,ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Mont.AArch64.const64_ok a .x9 (BitVec.ofNat 64 (2^K.w))) fun b ⟨b9,kb⟩ => ?_
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,RegUpd.gpr_write,
    BitVec.setWidth_eq,reduceCtorEq,ite_false,b9,kb.gpr .x2 (by decide),kb.gpr .x3 (by decide),a2,a3,
    Option.some.injEq,exists_eq_left']
  refine ⟨bmag_fact K.w hw m hm2 sb hs2,fun r hr' => ?_,kb.mem.trans ka.mem,
    kb.rd.trans ka.rd,kb.wr.trans ka.wr,kb.sp.trans ka.sp⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr'
  simp only [RegUpd.gpr_write,hr'.1,hr'.2.1,ite_false]
  rw [kb.gpr r (by simp [hr'.2.2.2.2]),ka.gpr r (by simp [hr'.1,hr'.2.1,hr'.2.2.1,hr'.2.2.2.1])]


theorem bsignMask_ok (K : TCombCfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {k j N : Nat} (hw1 : 1≤K.w) (hw : K.w<65536) (hj : K.w*j+K.w≤N)
    (hN : K.bits+N≤size) (hbw : K.bits+K.w-1<4096) (hx : s.gpr .x19=BitVec.ofNat 64 j)
    (hbits : ∀ t<N,s.mem (off base (K.bits+t))=if k.testBit t then 1 else 0) :
    WP isa (.block K.bsignMask) s fun t =>
      t.gpr .x3=bmask (decide (bcar K.w k (j+1)=1)) ∧ Keeps [.x3,.x4,.x7,.x16] s t := by
  rw [TCombCfg.bsignMask,WP.block_append_iff]
  refine WP.mono (winIndex_ok s hs hw hx) fun a ⟨a16,ka⟩ => ?_
  have hr : InRegions (a.rd++a.wr) (off base (K.bits+(K.w*j+(K.w-1)))) 1 :=
    ⟨_,List.mem_append_right _ (ka.wr ▸ hs.wr),hs.contains (by omega) (by decide)⟩
  have he : a.gpr .x16+BitVec.ofNat 64 (K.bits+K.w-1)=off base (K.bits+(K.w*j+(K.w-1))) := by
    rw [a16,off,off,BitVec.add_assoc,BitVec.ofNat_add_ofNat]
    exact congrArg (base+·) (congrArg _ (by omega))
  have hv : a.mem (off base (K.bits+(K.w*j+(K.w-1))))=BitVec.ofNat 8 (bcar K.w k (j+1)) := by
    rw [ka.mem,hbits _ (by omega),bcar_succ_testBit hw1,byte_testBit]
  have hb := bcar_le K.w k (j+1)
  apply WP.of_runBlock
  simp only [zero7,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,State.load,addr,
    Size.bits,RegUpd.gpr_write,RegUpd.mem_write,RegUpd.rd_write,RegUpd.wr_write,
    BitVec.setWidth_eq,Nat.mod_one,show K.bits+K.w-1<4096*1 by omega,
    show 16*0<64 by decide,and_self,he,hr,read1_zext,hv,ite_true,reduceCtorEq,ite_false,
    Option.map_some,Option.bind_some,Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun r hr' => ?_,ka.mem,ka.rd,ka.wr,ka.sp⟩
  · rcases (by omega : bcar K.w k (j+1)=0 ∨ bcar K.w k (j+1)=1) with h | h <;> rw [h] <;> decide
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr'
    simp only [RegUpd.gpr_write,hr'.1,hr'.2.1,hr'.2.2.1,ite_false]
    exact ka.gpr r (by simp [hr'.2.2.2])

theorem booth_inc_ok (s : State) {j J : Nat} (hJ : J<4096)
    (h19 : s.gpr .x19=BitVec.ofNat 64 j) :
    WP isa (.block [.addImm .x .x19 .x19 1,.subImm .x .x4 .x19 J]) s fun t =>
      t.gpr .x19=BitVec.ofNat 64 (j+1) ∧ t.gpr .x4=BitVec.ofNat 64 (j+1)-BitVec.ofNat 64 J ∧
      Keeps [.x4,.x19] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,Size.bits,
    show 1<4096 by decide,hJ,ite_true,RegUpd.gpr_write,BitVec.setWidth_eq,
    reduceCtorEq,ite_false,h19,BitVec.ofNat_add_ofNat,Option.some.injEq,exists_eq_left']
  refine ⟨trivial,trivial,fun r hr => ?_,rfl,rfl,rfl,rfl⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
  simp only [RegUpd.gpr_write,hr.1,hr.2,ite_false]

theorem booth_eqMask_ok (s : State) :
    WP isa (.block [zero7,.movz .x .x5 1 0,.subs .x .x16 .x2 .x5,.sbc .x .x3 .x7 .x7]) s fun t =>
      t.gpr .x3=mask (s.gpr .x2=0) ∧ Keeps [.x3,.x5,.x7,.x16] s t := by
  rw [←List.singleton_append,WP.block_append_iff]
  refine WP.mono (zero7_ok s) fun a ⟨a7,ka⟩ => ?_
  rw [←List.singleton_append,WP.block_append_iff]
  refine WP.mono (movz_ok a .x5 1) fun b ⟨b5,kb⟩ => ?_
  rw [←List.singleton_append,WP.block_append_iff]
  refine WP.mono (subc_ok b .x16 .x2 .x5 true (c:=true) rfl) fun c ⟨_,cc,kc⟩ => ?_
  refine WP.mono (sbcMask3_ok c (by rw [kc.gpr _ (by decide),kb.gpr _ (by decide),a7]))
    fun t ⟨ht,kt⟩ => ⟨?_,(((ka.mono (by sub_regs)).trans (kb.mono (by sub_regs))).trans
      (kc.mono (by sub_regs))).trans (kt.mono (by sub_regs))⟩
  rw [ht,cc,not_carryOut,b5,kb.gpr .x2 (by decide),ka.gpr .x2 (by decide)]
  simp only [show ((1 : BitVec 16).setWidth 64).toNat=1 from rfl,Bool.not_true,
    Bool.toNat_false,Nat.add_zero,Nat.lt_one_iff,decide_eq_true_eq,mask]
  congr 1
  exact propext ⟨fun h => BitVec.eq_of_toNat_eq h,fun h => by rw [h]; rfl⟩


private theorem booth_addByte_ok {s : State} {d m b : Nat} (hd : d<4096) (hb : b<2)
    (hx : s.gpr .x2=BitVec.ofNat 64 m)
    (hr : InRegions (s.rd++s.wr) (s.gpr .x16+BitVec.ofNat 64 d) 1)
    (hm : s.mem (s.gpr .x16+BitVec.ofNat 64 d)=BitVec.ofNat 8 b) :
    WP isa (.block [.ldrb .x4 .x16 d,.add .x .x2 .x2 .x4]) s fun t =>
      t.gpr .x2=BitVec.ofNat 64 (m+b) ∧ Keeps [.x2,.x4] s t := by
  have eb : (BitVec.ofNat 8 b).setWidth 64=BitVec.ofNat 64 b := by
    rcases (by omega : b=0 ∨ b=1) with rfl | rfl <;> rfl
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,State.load,addr,Size.bits,
    Nat.mod_one,show d<4096*1 by omega,and_self,ite_true,hr,read1_zext,hm,
    Option.map_some,Option.bind_some,RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,ite_false,
    hx,Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun r hr' => ?_,rfl,rfl,rfl,rfl⟩
  · rw [eb,BitVec.ofNat_add_ofNat]
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr'
    simp only [RegUpd.gpr_write,hr'.1,hr'.2,ite_false]

/-- Read a Booth digit using only addresses determined by the public window index. -/
theorem bdigit_ok (K : TCombCfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {k j N : Nat} (hw1 : 1≤K.w) (hw : K.w<9) (hj : K.w*j+K.w≤N) (hN : K.bits+N≤size)
    (hb1 : 1≤K.bits) (hbw : K.bits+K.w≤4096) (hx : s.gpr .x19=BitVec.ofNat 64 j)
    (hbits : ∀ t<N,s.mem (off base (K.bits+t))=if k.testBit t then 1 else 0) {carry : Bool}
    (hc : (carry=true ∧ 1≤j) ∨ (carry=false ∧ j=0)) :
    WP isa (.block (K.bdigit carry)) s fun t =>
      t.gpr .x2=BitVec.ofNat 64 (bmag K.w k j) ∧ Keeps [.x2,.x3,.x4,.x7,.x9,.x16] s t := by
  rw [TCombCfg.bdigit,List.append_assoc,List.append_assoc,List.append_assoc,List.append_assoc,
    WP.block_append_iff]
  refine WP.mono (winIndex_ok s hs (by omega) hx) fun a ⟨a16,ka⟩ => ?_
  rw [WP.block_append_iff]
  have hv : ∀ i,(fun t => (k.testBit (K.w*j+(t-K.bits))).toNat) i≤1 := fun _ => Bool.toNat_le _
  refine WP.mono (hornerBits_ok hv K.w K.bits (s:=a) (by omega) hbw fun i hi => ?_)
    fun b ⟨b2,kb⟩ => ?_
  · have he : a.gpr .x16+BitVec.ofNat 64 (K.bits+i)=off base (K.bits+(K.w*j+i)) := by
      rw [a16,off,off,BitVec.add_assoc,BitVec.ofNat_add_ofNat]
      exact congrArg (base+·) (congrArg _ (by omega))
    refine ⟨by rw [he]; exact ⟨_,List.mem_append_right _ (ka.wr ▸ hs.wr),hs.contains (by omega) (by decide)⟩,?_⟩
    rw [he,ka.mem,hbits _ (by omega),show K.bits+i-K.bits=i by omega]
    cases k.testBit (K.w*j+i) <;> rfl
  have heq : hornerVal (fun t => (k.testBit (K.w*j+(t-K.bits))).toNat) K.bits K.w=combWin K.w k j := by
    have he := hornerVal_eq k K.w j K.w (Nat.le_refl _)
    rw [Nat.sub_self,Nat.add_zero] at he
    rw [combWin,←he]
    exact hornerVal_congr fun i _ => by simp only [show K.bits+i-K.bits=i by omega]
  rw [heq] at b2
  have b16 : b.gpr .x16=off base (K.w*j) := (kb.gpr _ (by decide)).trans a16
  have reg : ∀ t<N,InRegions (b.rd++b.wr) (off base (K.bits+t)) 1 := fun t ht =>
    ⟨_,List.mem_append_right _ (kb.wr ▸ ka.wr ▸ hs.wr),hs.contains (by omega) (by decide)⟩
  have mid : WP isa (.block (if carry then [.ldrb .x4 .x16 (K.bits-1),.add .x .x2 .x2 .x4] else [])) b
      fun t => t.gpr .x2=BitVec.ofNat 64 (combWin K.w k j+bcar K.w k j) ∧ Keeps [.x2,.x4] b t := by
    rcases hc with ⟨rfl,hj1⟩ | ⟨rfl,rfl⟩
    · have hwj : 1≤K.w*j := Nat.mul_le_mul hw1 hj1
      have he : b.gpr .x16+BitVec.ofNat 64 (K.bits-1)=off base (K.bits+(K.w*j-1)) := by
        rw [b16,off,off,BitVec.add_assoc,BitVec.ofNat_add_ofNat]
        exact congrArg (base+·) (congrArg _ (by omega))
      apply booth_addByte_ok (by omega) (Nat.lt_succ_of_le (bcar_le _ _ _)) b2
      · rw [he]; exact reg _ (by omega)
      · rw [he,kb.mem,ka.mem,hbits _ (by omega),bcar_testBit hj1,byte_testBit]
    · change WP isa (.block []) b _
      exact WP.block_nil ⟨by simpa only [bcar,ite_true,Nat.add_zero] using b2,fun _ _ => rfl,rfl,rfl,rfl,rfl⟩
  rw [WP.block_append_iff]
  refine WP.mono mid fun d ⟨d2,kd⟩ => ?_
  have d16 : d.gpr .x16=off base (K.w*j) := (kd.gpr _ (by decide)).trans b16
  have he : d.gpr .x16+BitVec.ofNat 64 (K.bits+K.w-1)=off base (K.bits+(K.w*j+(K.w-1))) := by
    rw [d16,off,off,BitVec.add_assoc,BitVec.ofNat_add_ofNat]
    exact congrArg (base+·) (congrArg _ (by omega))
  have dm : d.mem (d.gpr .x16+BitVec.ofNat 64 (K.bits+K.w-1))=BitVec.ofNat 8 (bcar K.w k (j+1)) := by
    rw [he,kd.mem,kb.mem,ka.mem,hbits _ (by omega),bcar_succ_testBit hw1,byte_testBit]
  have dr : InRegions (d.rd++d.wr) (d.gpr .x16+BitVec.ofNat 64 (K.bits+K.w-1)) 1 := by
    rw [he,kd.rd,kd.wr]; exact reg _ (by omega)
  have ml : combWin K.w k j+bcar K.w k j<2^K.w+1 := by
    have := combWin_lt K.w k j
    have := bcar_le K.w k j
    omega
  rw [←List.append_assoc]
  refine WP.mono (bmagTail_ok K hw ml (Nat.lt_succ_of_le (bcar_le _ _ _)) (by omega) d2 dr dm)
    fun t ⟨t2,kt⟩ => ?_
  rw [←bmag_eq hw1] at t2
  exact ⟨t2,(((ka.mono (by sub_regs)).trans (kb.mono (by sub_regs))).trans
    (kd.mono (by sub_regs))).trans (kt.mono (by sub_regs))⟩

end VG.Proof.Weierstrass.AArch64
