import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafChoose
import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafShift
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafPrep

/-! Digit stores, public index updates and the prezeroed sparse recoder state. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Mont.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.X25519.X86_64

/-- The recoder of a scalar `k` of `n` words after `j` digits: the residual in
the scalar's registers, the index in `rbx`, and the digits so far (the rest of
the `64 n + 1` bytes zero). -/
structure FastPrepState (n : Nat) (base : Addr) (size bits w k j : Nat) (s : State) : Prop where
  scr : Scr s base size
  value : nafValN n s=FastNaf.residual w k j
  count : s.gpr .rbx=BitVec.ofNat 64 j
  digits : ∀ i<64*n+1,s.mem (off base (bits+i))=if i<j then FastNaf.byte w k i else 0

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
    (hs : Scr s base size) (hb : bits+j<size)
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

private theorem cmp_sext {v : Nat} (hv : v<2^31) :
    (BitVec.ofNat 32 v).signExtend 64=BitVec.ofNat 64 v := by
  rw [BitVec.signExtend_eq_setWidth_of_msb_false (BitVec.msb_eq_false_iff_two_mul_lt.mpr (by
      rw [BitVec.toNat_ofNat]; omega))]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : v<2^32),Nat.mod_eq_of_lt (by omega : v<2^64)]

theorem fastCompare_ok (s : State) {n j : Nat} (hn : 64*n+1<2^31) (hj : j<2^64)
    (hc : s.gpr .rbx=BitVec.ofNat 64 j) :
    WP isa (.block [.alu .cmp .rbx (.imm (BitVec.ofNat 32 (64*n+1)))]) s fun t =>
      t.cf=some (decide (j<64*n+1)) ∧ Keeps [] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,
    Option.bind_some,RegUpd.cf_arithFlags,Option.some.injEq,exists_eq_left',cmp_sext hn]
  refine ⟨?_,fun _ _ => rfl,rfl,rfl,rfl⟩
  simp only [hc,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hj,Nat.mod_eq_of_lt (show 64*n+1<2^64 by omega)]

private theorem clearWords_ok {s : State} {base : Addr} {size bits n : Nat}
    (hs : Scr s base size) (hb : bits+8*n≤size) :
    WP isa (.block (setConst n bits 0)) s fun t =>
      wordsVal t.mem base bits n=0 ∧ KeepRegs [.rax] s t ∧ Outside base bits (8*n) s.mem t.mem :=
  setConst_ok hs hb (Nat.two_pow_pos _)

theorem fastClear_ok {s : State} {base : Addr} {size n bits : Nat}
    (hs : Scr s base size) (hb : bits+64*n+8≤size) :
    WP isa (.block (setConst (8*n+1) bits 0)) s fun t =>
      (∀ i<64*n+8,t.mem (off base (bits+i))=0) ∧ KeepRegs [.rax] s t ∧
        Outside base bits (64*n+8) s.mem t.mem := by
  refine WP.mono (clearWords_ok (n:=8*n+1) hs (by omega)) fun t ⟨ht,kt,ot⟩ => ⟨?_,kt,?_⟩
  · intro i hi
    apply BitVec.eq_of_getLsbD_eq
    intro b hb
    rw [testBit_byte t.mem base (n:=8*n+1) (by omega) hb,ht]
    simp only [BitVec.ofNat_eq_ofNat,Nat.zero_testBit,BitVec.getLsbD_zero]
  · rwa [show 8*(8*n+1)=64*n+8 by omega] at ot

/-- `loads_ok` for any distinct registers but `rdi`: nine words load into `rbp`
too, which `Fresh` excludes. -/
theorem loadsScalar_ok {size : Nat} : ∀ (ts : List Reg) {s : State} {base : Addr} {a : Nat},
    Scr s base size → a+8*ts.length≤size → ts.Nodup → Reg.rdi∉ts →
    WP isa (.block (loads ts a)) s fun s' =>
      regsVal s' ts=wordsVal s.mem base a ts.length ∧ Keeps ts s s'
  | [],s,_,_,_,_,_,_ => WP.block_nil ⟨rfl,fun _ _ => rfl,rfl,rfl,rfl⟩
  | t::ts,s,base,a,hs,ha,hn,hd => by
    simp only [List.length_cons] at ha
    have ht : t∉ts := (List.nodup_cons.mp hn).1
    have htd : t≠.rdi := fun h => hd (h ▸ List.mem_cons_self ..)
    rw [loads,←List.singleton_append,WP.block_append_iff]
    refine WP.mono (show WP isa (.block [.mov t (.mem (sc a))]) s
        (fun s₁ => s₁.gpr t=word s.mem base a ∧ Keeps [t] s s₁) by
      apply WP.of_runBlock
      simp only [runBlock_cons,runStep_some,runBlock_nil,exec,readSrc_sc hs (d:=a) (by omega),
        Option.map_some,RegUpd.gpr_setReg,ite_true,Option.some.injEq,exists_eq_left']
      refine ⟨trivial,fun r hr => ?_,rfl,rfl,rfl⟩
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      simp only [RegUpd.gpr_setReg,hr,ite_false]) fun s₁ ⟨e₁,k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by
      simp only [List.mem_cons,List.not_mem_nil,or_false]; exact fun h => htd h.symm)
    refine WP.mono (loadsScalar_ok ts hs₁ (a:=a+8) (by omega) (List.nodup_cons.mp hn).2
      (fun h => hd (List.mem_cons_of_mem _ h))) fun s₂ ⟨e₂,k₂⟩ => ?_
    have ht' : s₂.gpr t=s₁.gpr t := k₂.1 t ht
    refine ⟨?_,(k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
    rw [List.length_cons,regsVal,wordsVal,ht',e₁,e₂,k₁.2.1]

theorem initN_four (src : Nat) : Naf.initN 4 src=Naf.init src := rfl

theorem initN_six (src : Nat) : Naf.initN 6 src=
    loads [.r8,.r9,.r10,.r11,.r12,.r13] src++
      ([.mov32 .r14 (.imm 0),.mov32 .rbx (.imm 0)] : List Instr) := rfl

theorem initN_nine (src : Nat) : Naf.initN 9 src=
    loads [.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15,.rbp] src++
      ([.mov32 .rsi (.imm 0),.mov32 .rbx (.imm 0)] : List Instr) := rfl

/-- Load a scalar of `n` words, a zero top word and a zero index. -/
theorem nafPrepInitN_ok {s : State} {base : Addr} {size n src : Nat} (hn : n=4 ∨ n=6 ∨ n=9)
    (hs : Scr s base size) (hsrc : src+8*n≤size) :
    WP isa (.block (Naf.initN n src)) s fun t =>
      nafValN n t=wordsVal s.mem base src n ∧ t.gpr .rbx=BitVec.ofNat 64 0 ∧
      KeepRegs (nafPrepClobN n) s t ∧ t.mem=s.mem ∧ Scr t base size := by
  rcases hn with rfl|rfl|rfl
  · rw [initN_four,Naf.init,WP.block_append_iff]
    refine WP.mono (loads_ok [.r8,.r9,.r10,.r11] hs hsrc (by simp [Fresh])) fun a ⟨va,ka⟩ => ?_
    have sa := hs.of_keeps ka (by decide)
    apply WP.of_runBlock
    simp only [runBlock_cons,runStep_some,runBlock_nil,exec,readSrc32,State.setReg32,
      Option.map_some,Option.some.injEq,exists_eq_left']
    refine ⟨?_,rfl,?_,ka.2.1,⟨sa.rdi,sa.wr,sa.nowrap⟩⟩
    · simp only [nafValN_four,nafVal5,RegUpd.gpr_setReg,ite_true,ite_false,reduceCtorEq]
      change _+2^256*0=wordsVal s.mem base src 4
      simp only [regsVal,List.length_cons,List.length_nil,Nat.reduceAdd] at va
      omega
    · refine ⟨fun r hr => ?_,ka.2.2.1,ka.2.2.2⟩
      have h12 : r≠.r12 := fun h => hr (h ▸ (by decide))
      have hbx : r≠.rbx := fun h => hr (h ▸ (by decide))
      simp only [RegUpd.gpr_setReg,h12,hbx,ite_false]
      exact ka.1 r (fun h => hr ((by decide : ∀ q∈[Reg.r8,.r9,.r10,.r11],q∈nafPrepClobN 4) r h))
  · rw [initN_six,WP.block_append_iff]
    refine WP.mono (loads_ok [.r8,.r9,.r10,.r11,.r12,.r13] hs hsrc (by simp [Fresh]))
      fun a ⟨va,ka⟩ => ?_
    have sa := hs.of_keeps ka (by decide)
    apply WP.of_runBlock
    simp only [runBlock_cons,runStep_some,runBlock_nil,exec,readSrc32,State.setReg32,
      Option.map_some,Option.some.injEq,exists_eq_left']
    refine ⟨?_,rfl,?_,ka.2.1,⟨sa.rdi,sa.wr,sa.nowrap⟩⟩
    · simp only [nafValN_six,nafVal7,RegUpd.gpr_setReg,ite_true,ite_false,reduceCtorEq]
      change _+2^64*(_+2^64*(_+2^64*(_+2^64*(_+2^64*(_+2^64*0)))))=wordsVal s.mem base src 6
      simp only [regsVal,List.length_cons,List.length_nil,Nat.reduceAdd] at va
      omega
    · refine ⟨fun r hr => ?_,ka.2.2.1,ka.2.2.2⟩
      have h14 : r≠.r14 := fun h => hr (h ▸ (by decide))
      have hbx : r≠.rbx := fun h => hr (h ▸ (by decide))
      simp only [RegUpd.gpr_setReg,h14,hbx,ite_false]
      exact ka.1 r (fun h => hr ((by decide : ∀ q∈[Reg.r8,.r9,.r10,.r11,.r12,.r13],
        q∈nafPrepClobN 6) r h))
  · rw [initN_nine,WP.block_append_iff]
    refine WP.mono (loadsScalar_ok [.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15,.rbp] hs hsrc (by decide)
      (by decide))
      fun a ⟨va,ka⟩ => ?_
    have sa := hs.of_keeps ka (by decide)
    apply WP.of_runBlock
    simp only [runBlock_cons,runStep_some,runBlock_nil,exec,readSrc32,State.setReg32,
      Option.map_some,Option.some.injEq,exists_eq_left']
    refine ⟨?_,rfl,?_,ka.2.1,⟨sa.rdi,sa.wr,sa.nowrap⟩⟩
    · simp only [nafValN_nine,nafVal10,RegUpd.gpr_setReg,ite_true,ite_false,reduceCtorEq]
      change _+2^64*(_+2^64*(_+2^64*(_+2^64*(_+2^64*(_+2^64*(_+2^64*(_+2^64*(_+2^64*0))))))))=
        wordsVal s.mem base src 9
      simp only [regsVal,List.length_cons,List.length_nil,Nat.reduceAdd] at va
      omega
    · refine ⟨fun r hr => ?_,ka.2.2.1,ka.2.2.2⟩
      have hsi : r≠.rsi := fun h => hr (h ▸ (by decide))
      have hbx : r≠.rbx := fun h => hr (h ▸ (by decide))
      simp only [RegUpd.gpr_setReg,hsi,hbx,ite_false]
      exact ka.1 r (fun h => hr ((by decide : ∀ q∈[Reg.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15,.rbp],
        q∈nafPrepClobN 9) r h))

theorem fastPrepInit_ok {s : State} {base : Addr} {size n src bits w : Nat} (hn : n=4 ∨ n=6 ∨ n=9)
    (hs : Scr s base size) (hsrc : src+8*n≤size) (hb : bits+64*n+8≤size) :
    WP isa (.block (Naf.initN n src++setConst (8*n+1) bits 0)) s fun t =>
      FastPrepState n base size bits w (wordsVal s.mem base src n) 0 t ∧
      KeepRegs (nafPrepClobN n) s t ∧ Outside base bits (64*n+8) s.mem t.mem := by
  rw [WP.block_append_iff]
  refine WP.mono (nafPrepInitN_ok hn hs hsrc) fun a ⟨va,ca,ka,ma,sa⟩ => ?_
  refine WP.mono (fastClear_ok sa hb) fun t ⟨zt,kt,ot⟩ => ?_
  have hv : nafValN n t=nafValN n a :=
    VG.Proof.Mont.X86_64.regsVal_congr fun r hr => kt.gpr r (by
      rcases hn with rfl|rfl|rfl <;> revert r <;> decide)
  refine ⟨⟨sa.of_keepRegs kt (by decide),?_,?_,?_⟩,ka.trans (kt.mono (by
    rcases hn with rfl|rfl|rfl <;> decide)),?_⟩
  · rw [hv,va,FastNaf.residual_zero]
  · exact (kt.gpr .rbx (by decide)).trans ca
  · intro i hi
    simpa only [Nat.not_lt_zero,ite_false] using zt i (by omega)
  · rw [ma] at ot
    exact ot

end VG.Proof.Weierstrass.X86_64
