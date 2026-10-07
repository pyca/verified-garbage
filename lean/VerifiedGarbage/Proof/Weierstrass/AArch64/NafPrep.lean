import VerifiedGarbage.Proof.Weierstrass.AArch64.NafSubtract
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 VG.Proof.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

/-- Registers written by the public scalar recoder. -/
def nafPrepClob : List Reg := [.x1,.x2,.x3,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x19,.x20]

structure NafPrepState (base : Addr) (size bits k j : Nat) (s : State) : Prop where
  scr : Scr s base size
  value : nafVal5 (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) (s.gpr .x8) (s.gpr .x9)=Naf5.residual k j
  mask : s.gpr .x10=31
  sign : s.gpr .x11=16
  zero : s.gpr .x12=0
  one : s.gpr .x13=1
  count : s.gpr .x19=BitVec.ofNat 64 (257-j)
  ptr : s.gpr .x20=off base (bits+j)
  digits : ∀ i<j,s.mem (off base (bits+i))=Naf5.byte k i

theorem nafByte_word (k j : Nat) :
    BitVec.ofNat 8 (BitVec.ofInt 64 (Naf5.digit k j)).toNat=Naf5.byte k j := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat,nafWord_toNat,Naf5.byte_toNat]
  have hb := Naf5.magnitude_le k j
  cases hn : Naf5.negative k j
  · simp only [Bool.false_eq_true,ite_false]; omega
  · have hp := Naf5.negative_magnitude_pos k j hn
    simp only [ite_true]; omega

theorem nafStore_ok {s : State} {base : Addr} {size bits k j : Nat}
    (hs : Scr s base size) (hb : bits+257≤size) (hj : j<257)
    (hp : s.gpr .x20=off base (bits+j))
    (hd : s.gpr .x2=BitVec.ofInt 64 (Naf5.digit k j)) :
    WP isa (.block ([.strb .x2 .x20 0,.addImm .x .x20 .x20 1] : List Instr)) s fun t =>
      t.gpr .x20=off base (bits+(j+1)) ∧
      t.mem=s.mem.writeW (off base (bits+j)) (Naf5.byte k j) ∧ KeepRegs [.x20] s t := by
  rw [show ([.strb .x2 .x20 0,.addImm .x .x20 .x20 1] : List Instr)=
    [.strb .x2 .x20 0]++[.addImm .x .x20 .x20 1] from rfl,WP.block_append_iff]
  have hw : InRegions s.wr (s.gpr .x20+BitVec.ofNat 64 0) 1 := by
    rw [hp]; simp only [BitVec.add_zero]
    exact ⟨_,hs.wr,hs.contains (by omega) (by decide)⟩
  refine WP.mono (strb_ok s (by decide) hw) fun a ha => ?_
  subst a
  refine WP.mono (addImm_ok _ (d:=.x20) (n:=.x20) (imm:=1) (by decide)) fun t ⟨ht,kt⟩ => ?_
  refine ⟨?_,?_,⟨kt.gpr,kt.rd,kt.wr,kt.sp⟩⟩
  · rw [ht]; change s.gpr .x20+BitVec.ofNat 64 1=_
    rw [hp]; unfold off; rw [Offset.add_add]; congr 1
  · rw [kt.mem]; simp only [hp,BitVec.add_zero,hd,nafByte_word]

theorem nafPrepStep_ok {s : State} {base : Addr} {size bits k j : Nat}
    (hI : NafPrepState base size bits k j s) (hb : bits+257≤size) (hj : j<257)
    (hv : Naf5.residual k j≤2^256) :
    WP isa Naf.prepStep s fun t => NafPrepState base size bits k (j+1) t ∧
      KeepRegs nafPrepClob s t ∧ Outside base bits 257 s.mem t.mem := by
  rw [Naf.prepStep]
  refine WP.seq (WP.mono (nafChoose_ok s hI.mask hI.sign hI.one) fun a ⟨ha,ka⟩ => ?_)
  have va : nafVal5 (a.gpr .x5) (a.gpr .x6) (a.gpr .x7) (a.gpr .x8) (a.gpr .x9)=Naf5.residual k j := by
    simp only [ka.gpr .x5 (by decide),ka.gpr .x6 (by decide),ka.gpr .x7 (by decide),
      ka.gpr .x8 (by decide),ka.gpr .x9 (by decide),hI.value]
  have da : a.gpr .x2=BitVec.ofInt 64 (Naf5.digit k j) := by
    rw [ha]; apply nafRaw_eq
    have hh := hI.value
    dsimp only [nafVal5] at hh
    omega
  have pa : a.gpr .x20=off base (bits+j) := (ka.gpr _ (by decide)).trans hI.ptr
  have sa := hI.scr.of_keeps ka (by decide)
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (nafStore_ok sa hb hj pa da) fun b ⟨pb,mb,kb⟩ => ?_
  have sb := sa.of_keepRegs kb (by decide)
  have vb : nafVal5 (b.gpr .x5) (b.gpr .x6) (b.gpr .x7) (b.gpr .x8) (b.gpr .x9)=Naf5.residual k j := by
    simp only [kb.gpr .x5 (by decide),kb.gpr .x6 (by decide),kb.gpr .x7 (by decide),
      kb.gpr .x8 (by decide),kb.gpr .x9 (by decide),va]
  rw [WP.block_append_iff]
  refine WP.mono (nafSubtract_ok b k j
    (by rw [kb.gpr .x12 (by decide),ka.gpr .x12 (by decide),hI.zero])
    (by rw [kb.gpr .x2 (by decide)]; exact da) vb hv) fun c ⟨vc,kc⟩ => ?_
  have pc : c.gpr .x20=off base (bits+(j+1)) := (kc.gpr _ (by decide)).trans pb
  have sc := sb.of_keeps kc (by decide)
  have cc : c.gpr .x19=BitVec.ofNat 64 (257-j) := by
    rw [kc.gpr _ (by decide),kb.gpr _ (by decide),ka.gpr _ (by decide),hI.count]
  refine WP.mono (decCounter_ok c (by omega) (by omega) cc) fun t ⟨ct,kt⟩ => ?_
  have st := sc.of_keeps kt (by decide)
  have mt : t.mem=s.mem.writeW (off base (bits+j)) (Naf5.byte k j) := by rw [kt.mem,kc.mem,mb,ka.mem]
  have O := writeW8_outside s.mem base (Naf5.byte k j) (d:=bits+j) (by have:=hI.scr.nowrap; omega)
  refine ⟨⟨st,?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,?_⟩
  · simp only [kt.gpr .x5 (by decide),kt.gpr .x6 (by decide),kt.gpr .x7 (by decide),
      kt.gpr .x8 (by decide),kt.gpr .x9 (by decide),vc]
  · rw [kt.gpr _ (by decide),kc.gpr _ (by decide),kb.gpr _ (by decide),ka.gpr _ (by decide),hI.mask]
  · rw [kt.gpr _ (by decide),kc.gpr _ (by decide),kb.gpr _ (by decide),ka.gpr _ (by decide),hI.sign]
  · rw [kt.gpr _ (by decide),kc.gpr _ (by decide),kb.gpr _ (by decide),ka.gpr _ (by decide),hI.zero]
  · rw [kt.gpr _ (by decide),kc.gpr _ (by decide),kb.gpr _ (by decide),ka.gpr _ (by decide),hI.one]
  · rw [ct]; congr 1
  · rw [kt.gpr _ (by decide),pc]
  · intro i hi
    rw [mt]
    by_cases hij : i=j
    · subst i; exact writeW8_self ..
    · rw [O _ (by
        have hoff : ofs base (off base (bits+i))=bits+i := by
          simpa only [BitVec.add_zero,Nat.add_zero] using (ofs_off base (d:=bits+i) (i:=0) (by have:=hI.scr.nowrap; omega))
        rw [hoff]; omega)]
      exact hI.digits i (by omega)
  · refine ⟨?_,kt.rd.trans (kc.rd.trans (kb.rd.trans ka.rd)),
      kt.wr.trans (kc.wr.trans (kb.wr.trans ka.wr)),kt.sp.trans (kc.sp.trans (kb.sp.trans ka.sp))⟩
    intro r hr
    have aR : r∉[Reg.x1,.x2,.x3] := by
      intro hh
      exact hr ((by decide : ∀ q∈[Reg.x1,.x2,.x3],q∈nafPrepClob) r hh)
    have bR : r∉[Reg.x20] := by
      intro hh
      exact hr ((by decide : ∀ q∈[Reg.x20],q∈nafPrepClob) r hh)
    have cR : r∉[Reg.x3,.x5,.x6,.x7,.x8,.x9] := by
      intro hh
      exact hr ((by decide : ∀ q∈[Reg.x3,.x5,.x6,.x7,.x8,.x9],q∈nafPrepClob) r hh)
    have tR : r∉[Reg.x19] := by
      intro hh
      exact hr ((by decide : ∀ q∈[Reg.x19],q∈nafPrepClob) r hh)
    rw [kt.gpr r tR,kc.gpr r cR,kb.gpr r bR,ka.gpr r aR]
  · rw [mt]; exact O.mono (by omega) (by omega)

theorem nafLoads_ok {s : State} {base : Addr} {size src : Nat}
    (hs : Scr s base size) (hsrc : src+32≤size) (hsrc8 : src%8=0) :
    WP isa (.block (VG.Impl.Mont.AArch64.loads [.x5,.x6,.x7,.x8] src)) s fun t =>
      regsVal t [.x5,.x6,.x7,.x8]=wordsVal s.mem base src 4 ∧ Keeps [.x5,.x6,.x7,.x8] s t := by
  rw [VG.Impl.Mont.AArch64.loads,←List.singleton_append,WP.block_append_iff]
  refine WP.mono (ld_ok hs (d:=src) (by omega) hsrc8 .x5) fun a ⟨va,ka,_⟩ => ?_
  have sa := hs.of_keeps ka (by decide)
  rw [VG.Impl.Mont.AArch64.loads,←List.singleton_append,WP.block_append_iff]
  refine WP.mono (ld_ok sa (d:=src+8) (by omega) (by omega) .x6) fun b ⟨vb,kb,_⟩ => ?_
  have sb := sa.of_keeps kb (by decide)
  rw [VG.Impl.Mont.AArch64.loads,←List.singleton_append,WP.block_append_iff]
  refine WP.mono (ld_ok sb (d:=src+8+8) (by omega) (by omega) .x7) fun c ⟨vc,kc,_⟩ => ?_
  have sc := sb.of_keeps kc (by decide)
  rw [VG.Impl.Mont.AArch64.loads,←List.singleton_append,WP.block_append_iff]
  refine WP.mono (ld_ok sc (d:=src+8+8+8) (by omega) (by omega) .x8) fun t ⟨vt,kt,_⟩ => ?_
  apply WP.block_nil
  refine ⟨?_,?_,kt.mem.trans (kc.mem.trans (kb.mem.trans ka.mem)),kt.rd.trans (kc.rd.trans (kb.rd.trans ka.rd)),
    kt.wr.trans (kc.wr.trans (kb.wr.trans ka.wr)),kt.sp.trans (kc.sp.trans (kb.sp.trans ka.sp))⟩
  · simp only [regsVal,wordsVal,kt.gpr .x5 (by decide),kt.gpr .x6 (by decide),kt.gpr .x7 (by decide),
      kc.gpr .x5 (by decide),kc.gpr .x6 (by decide),kb.gpr .x5 (by decide),va,vb,vc,vt,
      kc.mem,kb.mem,ka.mem]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    rw [kt.gpr r (by simpa using hr.2.2.2),kc.gpr r (by simpa using hr.2.2.1),
      kb.gpr r (by simpa using hr.2.1),ka.gpr r (by simpa using hr.1)]

theorem nafPrepInit_ok (K : WinCfg) {s : State} {base : Addr} {size src : Nat}
    (hs : Scr s base size) (hsrc : src+32≤size) (hsrc8 : src%8=0) (hbits : K.bits<4096) :
    WP isa (.block (Naf.prepInit K src)) s fun t =>
      NafPrepState base size K.bits (wordsVal s.mem base src 4) 0 t ∧
      KeepRegs nafPrepClob s t ∧ t.mem=s.mem := by
  have he : Naf.prepInit K src = VG.Impl.Mont.AArch64.loads [.x5,.x6,.x7,.x8] src ++
      [.movz .x .x9 0 0,.movz .x .x10 31 0,.movz .x .x11 16 0,.movz .x .x12 0 0,
       .movz .x .x13 1 0,.movz .x .x19 257 0,.addImm .x .x20 .x0 K.bits] := by
    simp only [Naf.prepInit,VG.Impl.Mont.AArch64.loads,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd]
  rw [he,WP.block_append_iff]
  refine WP.mono (nafLoads_ok hs hsrc hsrc8) fun a ⟨va,ka⟩ => ?_
  have sa := hs.of_keeps ka (by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,RegUpd.gpr_write,
    BitVec.setWidth_eq,show 16*0<Size.x.bits from by decide,hbits,ite_true,ite_false,reduceCtorEq,
    Option.some.injEq,exists_eq_left']
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,ka.mem⟩
  · exact ⟨sa.x0,sa.wr,sa.nowrap,sa.enc⟩
  · simp only [Naf5.residual,nafVal5,RegUpd.gpr_write,ite_true,ite_false,reduceCtorEq,BitVec.setWidth_eq] at *
    simp only [regsVal] at va
    change _+2^256*0=_
    omega
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · simpa only [Nat.add_zero,RegUpd.gpr_write,ite_true,BitVec.setWidth_eq] using congrArg (fun x => x+BitVec.ofNat 64 K.bits) sa.x0
  · intro i hi; omega
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

theorem nafPrep_ok (K : WinCfg) {s : State} {base : Addr} {size src : Nat}
    (hs : Scr s base size) (hsrc : src+32≤size) (hsrc8 : src%8=0)
    (hbits : K.bits<4096) (hb : K.bits+257≤size) :
    WP isa (Naf.prep K src) s fun t =>
      NafPrepState base size K.bits (wordsVal s.mem base src 4) 257 t ∧
      KeepRegs nafPrepClob s t ∧ Outside base K.bits 257 s.mem t.mem := by
  let k := wordsVal s.mem base src 4
  have hk : k<2^256 := wordsVal_lt ..
  let I (m : Nat) (t : State) := NafPrepState base size K.bits k (257-m) t ∧
    KeepRegs nafPrepClob s t ∧ Outside base K.bits 257 s.mem t.mem
  rw [Naf.prep]
  refine WP.seq (WP.mono (nafPrepInit_ok K hs hsrc hsrc8 hbits) fun a ⟨ia,ka,ma⟩ => ?_)
  refine countLoop_ok (Inv:=I) (n:=257) (by decide) ?_ ?_ (by decide) ?_
  · intro m t hm hm257 hI
    have hp := Naf5.residual_bound (Nat.le_of_lt hk) (j:=257-m) (by omega)
    have hp' : Naf5.residual k (257-m)≤2^256 := Nat.le_trans hp
      (Nat.pow_le_pow_right (by decide) (by omega))
    refine WP.mono (nafPrepStep_ok hI.1 hb (by omega) hp') fun u ⟨iu,ku,ou⟩ => ?_
    have he : 257-(m-1)=257-m+1 := by omega
    refine ⟨⟨?_,hI.2.1.trans ku,hI.2.2.trans ou⟩,?_⟩
    · rw [he]; exact iu
    · rw [iu.count]; congr 1; omega
  · intro t hI
    exact hI
  · refine ⟨ia,ka,?_⟩
    rw [ma]; intro _ _; rfl

end VG.Proof.Weierstrass.AArch64
