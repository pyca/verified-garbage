module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.LinearPair
public import VerifiedGarbage.Proof.Mont.AArch64.Csub
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.LinearPairs
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.LinearSum
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionBits
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Reduce

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64

def linearSubPair (rn r0 r1 : Reg) (b : Nat) (first : Bool) : List Instr :=
  twoLoads rn .x4 .x3 b++([if first then .subs .x r0 r0 .x4 else .sbcs .x r0 r0 .x4,.sbcs .x r1 r1 .x3] : List Instr)

theorem linear_sub_pair_words {s : State} {rn r0 r1 : Reg} {p : Addr} {size b : Nat} (first : Bool)
    (hp : Ptr s rn p size) (hb : b+16≤size) (hb8 : b%8=0)
    (hr : rn≠.x4) (h01 : r0≠r1) (h0 : r0∉[Reg.x3,.x4]) (h1 : r1∉[Reg.x3,.x4]) :
    WP isa (.block (linearSubPair rn r0 r1 b first)) s fun t =>
      t.gpr r0=addCarry (s.gpr r0) (~~~word s.mem p b) (if first then true else s.c) ∧
      t.gpr r1=addCarry (s.gpr r1) (~~~word s.mem p (b+8))
        (carryOut (s.gpr r0) (~~~word s.mem p b) (if first then true else s.c)) ∧
      t.c=carryOut (s.gpr r1) (~~~word s.mem p (b+8))
        (carryOut (s.gpr r0) (~~~word s.mem p b) (if first then true else s.c)) ∧ Keeps [.x3,.x4,r0,r1] s t := by
  rw [linearSubPair,WP.block_append_iff]
  refine WP.mono (two_loads_ok hp hb hb8 hr (by decide)) fun u ⟨b0,b1,cu,ku⟩ => ?_
  rw [←List.singleton_append,WP.block_append_iff]
  refine WP.mono (subc_ok u r0 r0 .x4 first rfl) fun v ⟨a0,c0,k0⟩ => ?_
  refine WP.mono (subc_ok v r1 r1 .x3 false rfl) fun t ⟨a1,c1,k1⟩ => ?_
  have u0 : u.gpr r0=s.gpr r0 := ku.gpr r0 (by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,not_or,and_comm] using h0)
  have u1 : u.gpr r1=s.gpr r1 := ku.gpr r1 (by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,not_or,and_comm] using h1)
  have v1 : v.gpr r1=u.gpr r1 := k0.gpr r1 (by simpa only [List.mem_singleton,ne_comm] using h01)
  have v3 : v.gpr .x3=u.gpr .x3 := k0.gpr .x3 (by
    simp only [List.mem_singleton]
    intro h
    exact h0 (by simp [←h]))
  simp only [Bool.false_eq_true,ite_false] at a0 c0 a1 c1
  rw [b0,u0,cu] at a0 c0
  rw [v1,v3,u1,b1,c0] at a1 c1
  exact ⟨by simpa only [k1.gpr r0 (by simpa only [List.mem_singleton] using h01)] using a0,a1,c1,
    (ku.mono (by simp)).trans ((k0.mono (by simp)).trans (k1.mono (by simp)))⟩

theorem linear_sub_pair_value {s : State} {rn r0 r1 : Reg} {p : Addr} {size b : Nat} (first : Bool)
    (hp : Ptr s rn p size) (hb : b+16≤size) (hb8 : b%8=0)
    (hr : rn≠.x4) (h01 : r0≠r1) (h0 : r0∉[Reg.x3,.x4]) (h1 : r1∉[Reg.x3,.x4]) :
    WP isa (.block (linearSubPair rn r0 r1 b first)) s fun t =>
      regsVal t [r0,r1]+wordsVal s.mem p b 2+(!(if first then true else s.c)).toNat=
        regsVal s [r0,r1]+2^128*(!t.c).toNat ∧
      Keeps [.x3,.x4,r0,r1] s t := by
  refine WP.mono (linear_sub_pair_words first hp hb hb8 hr h01 h0 h1) fun t ⟨a0,a1,c,k⟩ => ?_
  refine ⟨?_,k⟩
  simp only [regsVal,wordsVal,Nat.add_zero,Nat.mul_zero,a0,a1,c]
  have e0 := sub_borrow (s.gpr r0) (word s.mem p b) (if first then true else s.c)
  have e1 := sub_borrow (s.gpr r1) (word s.mem p (b+8))
    (carryOut (s.gpr r0) (~~~word s.mem p b) (if first then true else s.c))
  omega_using [e0,e1]

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64

def linearSubPairs (rn : Reg) : List (Reg × Reg) → Nat → List Instr
  | [], _ => []
  | (a,b)::ps, o => linearSubPair rn a b o false++linearSubPairs rn ps (o+16)

theorem linear_sub_pairs_ok {size : Nat} {rn : Reg} :
    ∀ (ps : List (Reg × Reg)) {s : State} {p : Addr} {b : Nat},
    Ptr s rn p size → b+8*(pairRegs ps).length≤size → b%8=0 →
    (pairRegs ps).Nodup → rn≠.x3 → rn≠.x4 →
    (∀ r∈pairRegs ps, r∉[Reg.x3,.x4,rn]) →
    WP isa (.block (linearSubPairs rn ps b)) s fun t =>
      regsVal t (pairRegs ps)+wordsVal s.mem p b (pairRegs ps).length+(!s.c).toNat=
        regsVal s (pairRegs ps)+2^(64*(pairRegs ps).length)*(!t.c).toNat ∧
      Keeps (.x3::.x4::pairRegs ps) s t
  | [], s, _, _, _, _, _, _, _, _, _ => WP.block_nil ⟨by simp [pairRegs,regsVal,wordsVal],
      fun _ _ => rfl,rfl,rfl,rfl,rfl⟩
  | (a,d)::ps, s, p, b, hp, hb, hb8, hn, hr3, hr4, hf => by
    have ha := hf a (by simp [pairRegs])
    have hd := hf d (by simp [pairRegs])
    have hn' := List.nodup_cons.mp hn
    have hn'' := List.nodup_cons.mp hn'.2
    have had : a≠d := fun e => hn'.1 (by simp [←e])
    have ha34 : a∉[Reg.x3,.x4] := fun e => ha (by simp_all)
    have hd34 : d∉[Reg.x3,.x4] := fun e => hd (by simp_all)
    rw [linearSubPairs,WP.block_append_iff]
    refine WP.mono (linear_sub_pair_value false hp (by simp only [pairRegs,List.length_cons] at hb; omega_arith)
      hb8 hr4 had ha34 hd34) fun u ⟨e0,k0⟩ => ?_
    have hpu := hp.of_keeps k0 (by
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
      exact ⟨hr3,hr4,fun e => ha (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton.mpr e.symm))),fun e => hd (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton.mpr e.symm)))⟩)
    refine WP.mono (linear_sub_pairs_ok ps hpu
      (by simp only [pairRegs,List.length_cons] at hb; omega_arith)
      (by omega_arith) hn''.2 hr3 hr4 (fun r h => hf r (by simp [pairRegs,h])))
      fun t ⟨e1,k1⟩ => ?_
    have hta : t.gpr a=u.gpr a := k1.gpr a (by
      simp only [List.mem_cons,not_or]; exact ⟨(by simpa using ha34 : a≠.x3 ∧ a≠.x4).1,(by simpa using ha34 : a≠.x3 ∧ a≠.x4).2,fun h => hn'.1 (by simp [h])⟩)
    have htd : t.gpr d=u.gpr d := k1.gpr d (by
      simp only [List.mem_cons,not_or]; exact ⟨(by simpa using hd34 : d≠.x3 ∧ d≠.x4).1,(by simpa using hd34 : d≠.x3 ∧ d≠.x4).2,hn''.1⟩)
    have htail : regsVal u (pairRegs ps)=regsVal s (pairRegs ps) := regsVal_congr fun r h =>
      k0.gpr r (by
        simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
        have hfr := hf r (List.mem_cons_of_mem a (List.mem_cons_of_mem d h))
        exact ⟨by intro e; exact hfr (by simp [e]),by intro e; exact hfr (by simp [e]),
          fun e => hn'.1 (List.mem_cons_of_mem d (e ▸ h)),fun e => hn''.1 (e ▸ h)⟩)
    rw [htail,k0.mem] at e1
    refine ⟨?_,(k0.mono (by
      intro r h
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl | rfl | rfl | rfl <;> simp [pairRegs])).trans (k1.mono (by
      intro r h
      simp only [List.mem_cons] at h
      rcases h with rfl | rfl | h
      · simp [pairRegs]
      · simp [pairRegs]
      · change r ∈ .x3::.x4::a::d::pairRegs ps
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)))))⟩
    simp only [Bool.false_eq_true,ite_false] at e0
    have hpw : 2^(64*(pairRegs ((a,d)::ps)).length)=2^128*2^(64*(pairRegs ps).length) := by
      simp only [pairRegs,List.length_cons,pow64_succ]
      omega_arith
    rw [hpw]
    simp only [pairRegs,regsVal,wordsVal,List.length_cons,hta,htd,Nat.add_assoc,
      Nat.add_zero,Nat.mul_zero,Nat.mul_add,Nat.mul_assoc,Nat.reduceAdd] at e0 ⊢
    omega_using [e0,e1]

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64

def linearSubTailPairs : List (Reg × Reg) := [(.x7,.x8),(.x9,.x10),(.x11,.x12)]
def linearSubEight (rn : Reg) (b : Nat) : List Instr :=
  linearSubPair rn .x5 .x6 b true++linearSubPairs rn linearSubTailPairs (b+16)

theorem linear_sub_eight_ok {s : State} {rn : Reg} {p : Addr} {size b : Nat}
    (hp : Ptr s rn p size) (hb : b+64≤size) (hb8 : b%8=0)
    (hr : rn∉[Reg.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12]) :
    WP isa (.block (linearSubEight rn b)) s fun t =>
      regsVal t linearRegs8+wordsVal s.mem p b 8=regsVal s linearRegs8+2^512*(!t.c).toNat ∧
      Keeps (.x3::.x4::linearRegs8) s t := by
  rw [linearSubEight,WP.block_append_iff]
  refine WP.mono (linear_sub_pair_value true hp (by omega_arith) hb8
    (fun h => hr (by simp [h])) (by decide) (by decide) (by decide)) fun u ⟨eu,ku⟩ => ?_
  have hpu := hp.of_keeps ku (fun h => hr ((by decide : ∀r∈[Reg.x3,.x4,.x5,.x6],r∈[Reg.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12]) _ h))
  refine WP.mono (linear_sub_pairs_ok linearSubTailPairs hpu
    (by change b+16+8*6≤size; omega_arith) (by omega_arith) (by decide)
    (fun h => hr (by simp [h])) (fun h => hr (by simp [h])) (by
      intro r h
      have h34 := (by decide : ∀r∈pairRegs linearSubTailPairs,r∉[Reg.x3,.x4]) r h
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at h34 ⊢
      exact ⟨h34.1,h34.2,fun e => hr ((by decide : ∀r∈pairRegs linearSubTailPairs,r∈[Reg.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12]) _ (e ▸ h))⟩))
    fun t ⟨et,kt⟩ => ?_
  have t5 : t.gpr .x5=u.gpr .x5 := kt.gpr .x5 (by decide)
  have t6 : t.gpr .x6=u.gpr .x6 := kt.gpr .x6 (by decide)
  have tailEq : regsVal u (pairRegs linearSubTailPairs)=regsVal s (pairRegs linearSubTailPairs) := regsVal_congr fun r h =>
    ku.gpr r ((by decide : ∀r∈pairRegs linearSubTailPairs,r∉[Reg.x3,.x4,.x5,.x6]) r h)
  rw [tailEq,ku.mem] at et
  simp only [ite_true,Bool.not_true,Bool.toNat_false,Nat.add_zero] at eu
  simp only [show (pairRegs linearSubTailPairs).length=6 from by decide,Nat.reduceMul] at et
  have splitRegs (v : State) : regsVal v linearRegs8=regsVal v [.x5,.x6]+2^128*regsVal v (pairRegs linearSubTailPairs) := by
    have h : linearRegs8=[Reg.x5,.x6]++pairRegs linearSubTailPairs := rfl
    rw [h,regsVal_append]
    simp only [List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceMul]
  have firstEq : regsVal t [.x5,.x6]=regsVal u [.x5,.x6] := by simp only [regsVal,t5,t6]
  have splitWords := wordsVal_split s.mem p b 2 6
  simp only [Nat.reduceAdd,Nat.reduceMul] at splitWords
  refine ⟨?_,(ku.mono (by decide)).trans (kt.mono (by decide))⟩
  rw [splitRegs,splitRegs,firstEq,splitWords]
  have scaled := congrArg (fun n : Nat => 2^128*n) et
  simp only [Nat.mul_add,←Nat.mul_assoc] at scaled
  have pw : 2^128*2^384=2^512 := by lit_decide
  rw [pw] at scaled
  omega_using [eu,scaled]

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64

def linearSubLast (rn : Reg) (b : Nat) : List Instr := [.ldr .x .x4 rn b,.sbcs .x .x13 .x13 .x4]

theorem linear_sub_last_ok {s : State} {rn : Reg} {p : Addr} {size b : Nat}
    (hp : Ptr s rn p size) (hb : b+8≤size) (hb8 : b%8=0) :
    WP isa (.block (linearSubLast rn b)) s fun t =>
      (t.gpr .x13).toNat+(word s.mem p b).toNat+(!s.c).toNat=
        (s.gpr .x13).toNat+2^64*(!t.c).toNat ∧ Keeps [.x4,.x13] s t := by
  rw [linearSubLast,←List.singleton_append,WP.block_append_iff]
  refine WP.mono (ldR_ok hp hb hb8 .x4) fun u ⟨bu,ku,cu⟩ => ?_
  refine WP.mono (subc_ok u .x13 .x13 .x4 false rfl) fun t ⟨a,ct,kt⟩ => ?_
  simp only [Bool.false_eq_true,ite_false] at a ct
  have ev := sub_borrow (u.gpr .x13) (u.gpr .x4) u.c
  rw [←a,←ct,bu,cu,ku.gpr .x13 (by decide)] at ev
  exact ⟨ev,(ku.mono (by simp)).trans (kt.mono (by simp))⟩

def linearDifference (rn : Reg) (b : Nat) : List Instr := linearSubEight rn b++linearSubLast rn (b+64)

theorem linear_difference_ok {s : State} {rn : Reg} {p : Addr} {size b : Nat}
    (hp : Ptr s rn p size) (hb : b+72≤size) (hb8 : b%8=0)
    (hr : rn∉[Reg.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13]) :
    WP isa (.block (linearDifference rn b)) s fun t =>
      regsVal t linearRegs9+wordsVal s.mem p b 9=regsVal s linearRegs9+2^576*(!t.c).toNat ∧
      Keeps (.x3::.x4::linearRegs9) s t := by
  rw [linearDifference,WP.block_append_iff]
  refine WP.mono (linear_sub_eight_ok hp (by omega_arith) hb8 (fun h => hr
    ((by decide : ∀r∈[Reg.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12],r∈[Reg.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13]) _ h))) fun u ⟨eu,ku⟩ => ?_
  have hpu := hp.of_keeps ku (fun h => hr ((by decide : ∀r∈.x3::.x4::linearRegs8,r∈[Reg.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13]) _ h))
  refine WP.mono (linear_sub_last_ok hpu (b:=b+64) (by omega_arith) (by omega_arith)) fun t ⟨et,kt⟩ => ?_
  have u13 : u.gpr .x13=s.gpr .x13 := ku.gpr .x13 (by decide)
  have t8 : regsVal t linearRegs8=regsVal u linearRegs8 := regsVal_congr fun r h =>
    kt.gpr r ((by decide : ∀r∈linearRegs8,r∉[Reg.x4,.x13]) r h)
  rw [u13,ku.mem] at et
  have eReg (v : State) : regsVal v linearRegs9=regsVal v linearRegs8+2^512*(v.gpr .x13).toNat := by
    rw [linearRegs9,regsVal_append]
    simp only [show linearRegs8.length=8 from by decide,Nat.reduceMul,regsVal,Nat.mul_zero,Nat.add_zero]
  have hone : wordsVal s.mem p (b+64) 1=(word s.mem p (b+64)).toNat := by
    simp only [wordsVal,Nat.mul_zero,Nat.add_zero]
  have splitWords := wordsVal_split s.mem p b 8 1
  simp only [Nat.reduceAdd,Nat.reduceMul,hone] at splitWords
  refine ⟨?_,(ku.mono (by decide)).trans (kt.mono (by decide))⟩
  rw [eReg,eReg,t8,splitWords]
  have scaled := congrArg (fun n : Nat => 2^512*n) et
  simp only [Nat.mul_add,←Nat.mul_assoc] at scaled
  have pw : 2^512*2^64=2^576 := by lit_decide
  rw [pw] at scaled
  omega_using [eu,scaled]

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64

theorem linear_regs_split (s : State) :
    regsVal s linearRegs9=regsVal s linearRegs8+2^512*(s.gpr .x13).toNat := by
  rw [linearRegs9,regsVal_append]
  simp only [show linearRegs8.length=8 from by decide,Nat.reduceMul,regsVal,Nat.mul_zero,Nat.add_zero]

theorem linear_mask_math {lo hi : Nat} (hl : lo<2^512) :
    lo+2^512*(hi%512)=(lo+2^512*hi)%(2^521) := by omega_arith

def linearMaskTop : List Instr := [.logic .and .x .x13 .x13 .x0]

theorem linear_mask_top_words (s : State) (hz : s.gpr .x0=511) :
    WP isa (.block linearMaskTop) s fun t =>
      t.gpr .x13=(s.gpr .x13 &&& 511) ∧ t.c=s.c ∧ Keeps [.x13] s t := by
  apply WP.of_runBlock
  simp only [linearMaskTop,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,
    RegUpd.gpr_write,RegUpd.c_write,BitVec.setWidth_eq,hz,Option.some.injEq,exists_eq_left']
  exact ⟨rfl,True.intro,⟨by intro r h; simp only [List.mem_singleton] at h; simp only [RegUpd.gpr_write,h,ite_false],
    by simp only [RegUpd.mem_write],by simp only [RegUpd.rd_write],
    by simp only [RegUpd.wr_write],by simp only [RegUpd.sp_write]⟩⟩

theorem linear_mask_top_ok (s : State) (hz : s.gpr .x0=511) :
    WP isa (.block linearMaskTop) s fun t =>
      regsVal t linearRegs9=regsVal s linearRegs9%(2^521) ∧ t.gpr .x0=511 ∧ Keeps [.x13] s t := by
  refine WP.mono (linear_mask_top_words s hz) fun t ⟨h,_,k⟩ => ?_
  have ht : regsVal t linearRegs8=regsVal s linearRegs8 := regsVal_congr fun r hr =>
    k.gpr r ((by decide : ∀r∈linearRegs8,r∉[Reg.x13]) r hr)
  refine ⟨?_,(k.gpr .x0 (by decide)).trans hz,k⟩
  rw [linear_regs_split,linear_regs_split,ht,h]
  have hm : (s.gpr .x13 &&& (511 : BitVec 64)).toNat=(s.gpr .x13).toNat%512 := P521Square.mask9_value (s.gpr .x13)
  rw [hm]
  have hl : regsVal s linearRegs8<2^512 := by
    simpa only [show linearRegs8.length=8 from by decide,Nat.reduceMul] using regsVal_lt s linearRegs8
  exact linear_mask_math (lo:=regsVal s linearRegs8) (hi:=(s.gpr .x13).toNat) hl

end VG.Proof.Mont.AArch64.P521Field
