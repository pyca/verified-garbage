import VerifiedGarbage.Impl.Weierstrass.X86.NafPrep
import VerifiedGarbage.Proof.Weierstrass.Naf5
import VerifiedGarbage.Proof.Weierstrass.X86.TCombDigit
import VerifiedGarbage.Impl.Weierstrass.X86.Naf
import VerifiedGarbage.Proof.Weierstrass.X86.TCombScan
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Weierstrass.X86.JacState
import VerifiedGarbage.Proof.Weierstrass.X86.Ladder
import VerifiedGarbage.Proof.Weierstrass.X86.NafSubChain

/-! ## `NafChoose` -/

section

/-! Selecting a signed width-five digit from the public scalar's low word. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Weierstrass.X86
open VG.Proof.Mont.X86

def nafOdd (x : BitVec 32) : BitVec 32 :=
  if (x &&& 31).toNat<16 then x &&& 31 else (x &&& 31)-32

def nafRaw (x : BitVec 32) : BitVec 32 := if x &&& 1=0 then 0 else nafOdd x

theorem nafMask (x : BitVec 32) : x &&& 31=BitVec.ofNat 32 (x.toNat%32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and,BitVec.toNat_ofNat]
  change x.toNat &&& (2^5-1) = (x.toNat%32)%2^32
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem nafParity (x : BitVec 32) : x &&& 1=0 ↔ x.toNat%2=0 := by
  rw [←BitVec.toNat_inj]
  change x.toNat &&& 1=0 ↔ x.toNat%2=0
  rw [Nat.and_one_is_mod]

theorem nafRaw_eq {x : BitVec 32} {k j : Nat}
    (hx : x.toNat%32=Naf5.residual k j%32) : nafRaw x=BitVec.ofInt 32 (Naf5.digit k j) := by
  have H : ∀ r : Fin 32,
      (if r.val%2=0 then (0 : BitVec 32) else if r.val<16 then BitVec.ofNat 32 r.val else
        BitVec.ofNat 32 r.val-32) =
      BitVec.ofInt 32 (if r.val%2=0 then 0 else if r.val<16 then (r.val:Int) else (r.val:Int)-32) := by decide
  simp only [nafRaw,nafOdd,nafParity,nafMask,BitVec.toNat_ofNat,hx,Naf5.digit_mod32]
  have hp : x.toNat%2=Naf5.residual k j%32%2 := by omega
  rw [hp,Nat.mod_eq_of_lt (show Naf5.residual k j%32<2^32 from by omega)]
  exact H ⟨Naf5.residual k j%32,Nat.mod_lt _ (by decide)⟩

theorem nafOdd_ok (s : State) :
    WP isa Naf.oddDigit s fun t => t.gpr .ecx=nafOdd (s.gpr .eax) ∧ CKeeps [.ecx] s t := by
  rw [Naf.oddDigit]
  refine WP.seq ?_
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,
    Option.map_some,Option.bind_some,RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,
    ite_true,Option.some.injEq,exists_eq_left']
  refine WP.ite (decide ((s.gpr .eax &&& 31).toNat<16)) ?_ (fun h => ?_) (fun h => ?_)
  · rfl
  · apply WP.block_nil
    refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl⟩
    · simp only [RegUpd.gpr_arithFlags,RegUpd.gpr_setReg,ite_true,nafOdd,
        of_decide_eq_true h,ite_true]
    · simp only [List.mem_singleton] at hr
      simp only [RegUpd.gpr_arithFlags,RegUpd.gpr_setReg,hr,ite_false]
  · apply WP.of_runBlock
    simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,
      Option.bind_some,RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,
      ite_true,Option.some.injEq,exists_eq_left']
    refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl⟩
    · simp only [nafOdd,of_decide_eq_false h,ite_false]
    · simp only [List.mem_singleton] at hr
      simp only [RegUpd.gpr_arithFlags,RegUpd.gpr_setReg,hr,ite_false]

theorem nafParity_ok (s : State) :
    WP isa (.block [.mov .ecx (.reg .eax),.alu .and .ecx (.imm 1),.alu .test .ecx (.reg .ecx)]) s
      fun t => t.gpr .ecx=s.gpr .eax &&& 1 ∧ t.zf=some (decide (s.gpr .eax &&& 1=0)) ∧ CKeeps [.ecx] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,
    Option.map_some,Option.bind_some,RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,
    RegUpd.zf_arithFlags,BitVec.and_self,ite_true,Option.some.injEq,exists_eq_left']
  refine ⟨trivial,?_,fun r hr => ?_,rfl,rfl,rfl⟩
  · rfl
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_arithFlags,RegUpd.gpr_setReg,hr,ite_false]

end VG.Proof.Weierstrass.X86

end

/-! ## `NafCopy` -/

section

/-! Direct copies of public Jacobian table entries. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Weierstrass.X86
open VG.Proof.Mont.X86 VG.Proof.Mont

private theorem ea_congr {s t : State} (h : t.gpr=s.gpr) (m : MemOp) : t.ea m=s.ea m := by
  simp only [State.ea,h]

theorem nafCopyPiece_ok {s : State} {base : Addr} {size a o : Nat} {src dst : MemOp}
    (hs : Scr s base size) (ha : a+16≤size) (ho : o+16≤size)
    (ea : s.ea src=off base a) (eo : s.ea dst=off base o) (r : XReg) :
    WP isa (.block [.movdquLoad r src,.movdquStore dst r]) s fun t =>
      t.mem.readW (off base o) 128=s.mem.readW (off base a) 128 ∧
      Outside base o 16 s.mem t.mem ∧ t.gpr=s.gpr ∧ t.rd=s.rd ∧ t.wr=s.wr := by
  have hr : InRegions (s.rd++s.wr) (off base a) 16 :=
    hs.read ha
  have hw : InRegions s.wr (off base o) 16 := hs.write ho
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,State.load128,State.store128,
    ea,hr,ite_true,Option.map_some,RegUpd.wr_setXmm,ea_congr (RegUpd.gpr_setXmm ..),eo,hw,
    RegUpd.xmm_setXmm_self,RegUpd.mem_setXmm,Option.some.injEq,exists_eq_left']
  exact ⟨Mem.readW_writeW_self (n:=16) _ _ _ (by decide),
    writeW128_out s.mem base (s.mem.readW (off base a) 128) (by have:=hs.nowrap; omega),rfl,rfl,trivial⟩

theorem nafCopyPieces_ok {base : Addr} {size a o : Nat} {src dst : Nat → MemOp} :
    ∀ n (s : State), Scr s base size → a+16*n≤size → o+16*n≤size →
      (o+16*n≤a ∨ a+16*n≤o) →
      (∀ i<n,s.ea (src i)=off base (a+16*i)) →
      (∀ i<n,s.ea (dst i)=off base (o+16*i)) →
    WP isa (.block (Naf.copyPieces n src dst)) s fun t =>
      (∀ i<n,t.mem.readW (off base (o+16*i)) 128=s.mem.readW (off base (a+16*i)) 128) ∧
      Outside base o (16*n) s.mem t.mem ∧ t.gpr=s.gpr ∧ t.rd=s.rd ∧ t.wr=s.wr
  | 0,s,_,_,_,_,_,_ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _),
      Outside.refl _ _ _ _,rfl,rfl,rfl⟩
  | n+1,s,hs,ha,ho,hd,ea,eo => by
    rw [Naf.copyPieces,List.range_succ,List.flatMap_append,List.flatMap_singleton,WP.block_append_iff]
    refine WP.mono (nafCopyPieces_ok n s hs (by omega) (by omega) (by omega)
      (fun i hi => ea i (by omega)) (fun i hi => eo i (by omega))) fun u ⟨eu,ou,gu,ru,wu⟩ => ?_
    have su : Scr u base size := hs.of_eq (congrFun gu .edi) (congrFun gu .esp) wu
    refine WP.mono (nafCopyPiece_ok su (a:=a+16*n) (o:=o+16*n) (by omega) (by omega)
      (by rw [ea_congr gu]; exact ea n (by omega))
      (by rw [ea_congr gu]; exact eo n (by omega)) (selAcc n)) fun t ⟨et,ot,gt,rt,wt⟩ => ?_
    refine ⟨fun i hi => ?_,(ou.mono (Nat.le_refl _) (by omega)).trans (ot.mono (by omega) (by omega)),
      gt.trans gu,rt.trans ru,wt.trans wu⟩
    by_cases he : i=n
    · subst i
      rw [et,ou.read128 (by omega) (by have:=hs.nowrap; omega)]
    · rw [ot.read128 (by omega) (by have:=hs.nowrap; omega),eu i (by omega)]

theorem nafCopy_words {mem mem' : Mem} {base : Addr} {n a o : Nat}
    (h : ∀ c<n,mem'.readW (off base (o+16*c)) 128=mem.readW (off base (a+16*c)) 128) :
    ∀ i<2*n,word mem' base (o+8*i)=word mem base (a+8*i) := by
  intro i hi
  obtain ⟨c,q,hq,rfl⟩ : ∃ c q,q<2 ∧ i=2*c+q :=
    ⟨i/2,i%2,Nat.mod_lt _ (by decide),by omega⟩
  have e := readW_extract mem' (off base (o+16*c)) (w:=128) (k:=8*q) (n:=8) (by omega)
  rw [show 8*8=64 from rfl,off,Offset.add_add,
    show o+16*c+8*q=o+8*(2*c+q) from by omega] at e
  rw [VG.Proof.Mont.word,off,←e,h c (by omega)]
  have e2 := readW_extract mem (off base (a+16*c)) (w:=128) (k:=8*q) (n:=8) (by omega)
  rw [show 8*8=64 from rfl,off,Offset.add_add] at e2
  rw [e2,VG.Proof.Mont.word,off,show a+16*c+8*q=a+8*(2*c+q) from by omega]

private theorem words_eq_of_words {m m' : Mem} {base : Addr} : ∀ n a o,
    (∀ i<n,word m' base (o+8*i)=word m base (a+8*i)) →
    wordsVal m' base o n=wordsVal m base a n
  | 0,_,_,_ => rfl
  | n+1,a,o,h => by
    have h0 := h 0 (by omega)
    simp only [Nat.mul_zero,Nat.add_zero] at h0
    rw [wordsVal,wordsVal,h0,words_eq_of_words n (a+8) (o+8) (fun i hi => ?_)]
    have he := h (i+1) (by omega)
    simpa only [Nat.mul_add,Nat.mul_one,Nat.add_assoc,Nat.add_comm 8] using he

theorem nafCopy_field {mem mem' : Mem} {base : Addr} {n a o j : Nat}
    (h : ∀ c<n,mem'.readW (off base (o+16*c)) 128=mem.readW (off base (a+16*c)) 128)
    (hj : 2*j+2≤n) : wordsVal mem' base (o+32*j) 4=wordsVal mem base (a+32*j) 4 := by
  apply words_eq_of_words
  intro i hi
  rw [show o+32*j+8*i=o+8*(4*j+i) from by omega,
    show a+32*j+8*i=a+8*(4*j+i) from by omega]
  exact nafCopy_words h _ (by omega)

theorem nafCopy_coord {mem mem' : Mem} {base : Addr} {a o j : Nat}
    (h : ∀ c<6,mem'.readW (off base (o+16*c)) 128=mem.readW (off base (a+16*c)) 128)
    (hj : j<3) : wordsVal mem' base (o+32*j) 4=wordsVal mem base (a+32*j) 4 :=
  nafCopy_field h (by omega)

end VG.Proof.Weierstrass.X86

end

/-! ## `NafAddress` -/

section

/-! Public addresses of the eight odd-multiple Jacobian table entries. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
  VG.Proof.Mont.X86 VG.Proof.Mont

theorem nafAddress_ok {s : State} {base : Addr} {size tbl j : Nat}
    (hs : Scr s base size) (hj : s.gpr .eax=BitVec.ofNat 32 j)
    (ht : tbl+96*j<size) :
    WP isa (.block (Naf.tableAddress tbl)) s fun t =>
      (t.gpr .edx).setWidth 64=off base (tbl+96*j) ∧ CKeeps [.eax,.ecx,.edx] s t := by
  apply WP.of_runBlock
  simp only [Naf.tableAddress,runBlock_cons,runStep_some,runBlock_nil,exec,readSrc,
    execAlu,execMul,hj,RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,
    RegUpd.gpr_setFlags,Option.map_some,Option.bind_some,ite_true,ite_false,reduceCtorEq,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl⟩
  · have hm : BitVec.ofNat 32 ((BitVec.ofNat 32 j).toNat*96)=BitVec.ofNat 32 (96*j) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_mul_mod,Nat.mul_comm j]
    change ((s.gpr .edi+BitVec.ofNat 32 tbl+
      BitVec.ofNat 32 ((BitVec.ofNat 32 j).toNat*96)).setWidth 64)=_
    rw [hm,Offset.add_add]
    exact hs.ea ht
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,RegUpd.gpr_setFlags,
      hr.1,hr.2.1,hr.2.2,ite_false]

theorem nafIndex_ok (s : State) {a : Nat} (ha : 1≤a) (ha' : a≤15)
    (hr : s.gpr .ebx=BitVec.ofNat 32 a) :
    WP isa (.block [.mov .eax (.reg .ebx),.alu .sub .eax (.imm 1),.shift .shr .eax 1]) s fun t =>
      t.gpr .eax=BitVec.ofNat 32 ((a-1)/2) ∧ CKeeps [.eax] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,readSrc,execAlu,execShift,
    Option.map_some,Option.bind_some,RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,
    RegUpd.gpr_setFlags,hr,ite_true,and_self,
    show 1≤1 ∧ 1≤31 from by decide,Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun r h => ?_,rfl,rfl,rfl⟩
  · change ((BitVec.ofNat 32 a-BitVec.ofNat 32 1)>>>1)=_
    rw [BitVec.ofNat_sub_ofNat_of_le a 1 (by decide) ha]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,BitVec.toNat_ofNat]
    omega
  · simp only [List.mem_singleton] at h
    simp only [RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,RegUpd.gpr_setFlags,h,ite_false]

end VG.Proof.Weierstrass.X86

end

/-! ## `NafState` -/

section

/-! Field environments and point preservation for public Jacobian loops. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Proof.Mont.X86 VG.Proof.Mont Spec.Weierstrass

/-- A multiple-slot update can reconstruct its environment from the resulting
memory. Bounds on changed slots and the frame preserve every initialized slot. -/
theorem Inv.of_progKeep {F : Spec.Weierstrass.Mont.Modulus} {M : Mod} {base : Addr} {size m wk : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAcc : WkOk F M m size wk Sl) {V W : List Nat}
    {E : Nat → Fin m} {s t : State} (hI : Inv M base size m Sl V E s)
    (hk : ProgKeep M base wk W s t) (hW : ∀ x ∈ W, Sl x)
    (hlt : ∀ x ∈ W, wordsVal t.mem base x M.n < m) :
    Inv M base size m Sl (W++V)
      (fun x => toM m (2^(64*M.n)) (wordsVal t.mem base x M.n)) t := by
  have hM := hI.mod
  refine ⟨hk.scr hI.scr,⟨hM.n0,hM.mo,hM.tmp,hM.sep,?_,hM.inv,hM.red⟩,?_,?_,fun _ _ => rfl⟩
  · rw [hk.wordsVal hI.scr.nowrap hM.mo (fun w hw => (hL.mo w (hW w hw)).symm)
      hM.sep hAcc.mo (by have := hAcc.toCallCfg.own_le; have := hAcc.mo; omega)]
    exact hM.val
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hW x hx
    · exact hI.sl x hx
  · intro x hx
    by_cases hw : x∈W
    · exact hlt x hw
    · have hv := (List.mem_append.mp hx).resolve_left hw
      have sl := hI.sl x hv
      rw [hk.wordsVal hI.scr.nowrap (hL.le x sl)
        (fun y hy => hL.apart x y sl (hW y hy) (fun he => hw (he ▸ hy)))
        (hL.tmp x sl) (hAcc.sl x sl) (by have := hAcc.toCallCfg.own_le; have := hAcc.sl x sl; omega)]
      exact hI.lt x hv


def jacCoords (p : Pt) : List Nat := [p.x,p.y,p.z]

theorem ProgKeep.slot {F : Spec.Weierstrass.Mont.Modulus} {M : Mod} {base : Addr} {size wk m : Nat} {Sl : Nat → Prop}
    {s t : State} {W : List Nat} (hL : Lay M size Sl) (hAcc : WkOk F M m size wk Sl) (hs : Scr s base size)
    (hk : ProgKeep M base wk W s t) (hW : ∀ x∈W, Sl x) {x : Nat}
    (hx : Sl x) (hn : x∉W) : VG.Proof.Mont.wordsVal t.mem base x M.n=VG.Proof.Mont.wordsVal s.mem base x M.n := by
  exact hk.wordsVal hs.nowrap (hL.le x hx)
    (fun y hy => hL.apart x y hx (hW y hy) (fun he => hn (he ▸ hy)))
    (hL.tmp x hx) (hAcc.sl x hx) (by have := hAcc.toCallCfg.own_le; have := hAcc.sl x hx; omega)

/-- An initialized environment can always be represented by the current
memory function, avoiding artificial relationships between temporary environments. -/
theorem Inv.to_tmv {M : Mod} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fe C} {s : State}
    (h : Inv M base size C.p Sl V E s) : Inv M base size C.p Sl V (tmv C M.n base s) s :=
  ⟨h.scr,h.mod,h.sl,h.lt,fun _ _ => rfl⟩

theorem Inv.point_tmv {M : Mod} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fe C} {s : State}
    (h : Inv M base size C.p Sl V E s) {p : Pt} {P : Point C}
    (hp : ∀ x ∈ [p.x,p.y,p.z], x ∈ V) (hJ : InvJ C (E p.x) (E p.y) (E p.z) P) :
    InvJ C (tmv C M.n base s p.x) (tmv C M.n base s p.y) (tmv C M.n base s p.z) P := by
  unfold tmv
  rw [h.val _ (hp _ (by simp)),h.val _ (hp _ (by simp)),h.val _ (hp _ (by simp))]
  exact hJ


theorem copyPointFields_ok {F : Spec.Weierstrass.Mont.Modulus} {M : Mod} {base : Addr} {size m wk : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAcc : WkOk F M m size wk Sl)
    {q o : Pt} (hN : (jacCoords o).Nodup)
    (hqa : ∀ x∈jacCoords q, ∀ y∈jacCoords o, x≠y)
    (hO : ∀ x∈jacCoords o, Sl x)
    {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) (hV : ∀ x∈jacCoords q, x∈V) :
    WP isa (.block (copyPt M.n o q)) s fun t =>
      ∃ E', ProgKeep M base wk (jacCoords o) s t ∧
      Inv M base size m Sl (jacCoords o ++ V) E' t ∧
      (E' o.x,E' o.y,E' o.z)=(E q.x,E q.y,E q.z) := by
  have hn := hN
  simp only [jacCoords,List.nodup_cons,List.mem_cons,List.not_mem_nil,
    or_false,not_or,List.nodup_nil,and_true] at hn
  have hox := hO o.x (by simp [jacCoords])
  have hoy := hO o.y (by simp [jacCoords])
  have hoz := hO o.z (by simp [jacCoords])
  have hqx := hV q.x (by simp [jacCoords])
  have hqy := hV q.y (by simp [jacCoords])
  have hqz := hV q.z (by simp [jacCoords])
  rw [copyPt,List.append_assoc,WP.block_append_iff]
  refine WP.mono (copyField_ok hL hAcc hI hox hqx) fun a ⟨ka,ia⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (copyField_ok hL hAcc ia hoy (List.mem_cons_of_mem _ hqy)) fun b ⟨kb,ib⟩ => ?_
  refine WP.mono (copyField_ok hL hAcc ib hoz
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hqz))) fun t ⟨kt,it⟩ => ?_
  refine ⟨_,(progKeep_of_op ka (by simp [jacCoords])).trans
    ((progKeep_of_op kb (by simp [jacCoords])).trans (progKeep_of_op kt (by simp [jacCoords]))),
    it.sub ?_,?_⟩
  · intro x hx
    simp only [jacCoords,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  · simp only [Function.update_self,Function.update_of_ne hn.1.1,
      Function.update_of_ne hn.1.2,Function.update_of_ne hn.2.1,
      Function.update_of_ne (hqa q.y (by simp [jacCoords]) o.x (by simp [jacCoords])),
      Function.update_of_ne (hqa q.z (by simp [jacCoords]) o.x (by simp [jacCoords])),
      Function.update_of_ne (hqa q.z (by simp [jacCoords]) o.y (by simp [jacCoords]))]

theorem ProgKeep.invJ {F : Spec.Weierstrass.Mont.Modulus} {M : Mod} {base : Addr} {size wk : Nat} {C : Curve}
    {Sl : Nat → Prop} {s t : State} {W : List Nat} (hL : Lay M size Sl) (hAcc : WkOk F M C.p size wk Sl) (hs : Scr s base size)
    (hk : ProgKeep M base wk W s t) (hW : ∀ x∈W, Sl x) {p : Pt}
    (hp : ∀ x∈jacCoords p, Sl x) (hDisj : ∀ x∈jacCoords p, x∉W) {P : Point C}
    (hJ : InvJ C (tmv C M.n base s p.x) (tmv C M.n base s p.y) (tmv C M.n base s p.z) P) :
    InvJ C (tmv C M.n base t p.x) (tmv C M.n base t p.y) (tmv C M.n base t p.z) P := by
  have eqv (x : Nat) (hx : x∈jacCoords p) : tmv C M.n base t x=tmv C M.n base s x := by
    unfold tmv; rw [hk.slot hL hAcc hs hW (hp x hx) (hDisj x hx)]
  rw [eqv _ (by simp [jacCoords]),eqv _ (by simp [jacCoords]),eqv _ (by simp [jacCoords])]
  exact hJ

end VG.Proof.Weierstrass.X86

end

/-! ## `NafSubtract` -/

section

/-! The sign-extended subtraction produces twice the next NAF residual. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Weierstrass.X86 VG.Proof.Mont.X86 VG.Proof.Mont

theorem nafWord_toNat (k j : Nat) :
    (BitVec.ofInt 32 (Naf5.digit k j)).toNat =
      if Naf5.negative k j then 2^32-Naf5.magnitude k j else Naf5.magnitude k j := by
  have hb := Naf5.magnitude_le k j
  simp only [Naf5.digit,BitVec.toNat_ofInt]
  cases hn : Naf5.negative k j
  · simp only [Bool.false_eq_true,ite_false]
    change ((Naf5.magnitude k j:Int)%4294967296).toNat=_
    omega
  · have hp := Naf5.negative_magnitude_pos k j hn
    simp only [ite_true]
    change ((-(Naf5.magnitude k j:Int))%4294967296).toNat=_
    omega

theorem nafSign_toNat (k j : Nat) :
    (0#32-(BitVec.ofInt 32 (Naf5.digit k j)>>>31)).toNat =
      if Naf5.negative k j then 2^32-1 else 0 := by
  have hb := Naf5.magnitude_le k j
  have hp := Naf5.negative_magnitude_pos k j
  simp only [BitVec.toNat_sub,BitVec.toNat_zero,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,nafWord_toNat]
  cases hn : Naf5.negative k j
  · simp only [Bool.false_eq_true,ite_false]; omega
  · have hp := hp hn
    simp only [ite_true]; omega

theorem nafDigitVal9 (k j : Nat) :
    nafDigitVal (BitVec.ofInt 32 (Naf5.digit k j))
      (0#32-(BitVec.ofInt 32 (Naf5.digit k j)>>>31)) 8 =
      if Naf5.negative k j then 2^288-Naf5.magnitude k j else Naf5.magnitude k j := by
  simp only [nafDigitVal,nafWord_toNat,nafSign_toNat]
  have := Naf5.magnitude_le k j
  cases hn : Naf5.negative k j <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega

theorem nafSubtract_next {v v' : Nat} {c : Bool} (k j : Nat)
    (hv : v=Naf5.residual k j) (hb : v≤2^256) (hlt : v'<2^288)
    (he : v'+nafDigitVal (BitVec.ofInt 32 (Naf5.digit k j))
      (0#32-(BitVec.ofInt 32 (Naf5.digit k j)>>>31)) 8 = v+2^288*c.toNat) :
    v'=2*Naf5.residual k (j+1) := by
  rw [nafDigitVal9] at he
  have hr := Naf5.recurrence k j
  have hm := Naf5.magnitude_le k j
  cases hn : Naf5.negative k j <;>
    simp only [hn,Bool.false_eq_true,ite_false,ite_true] at he hr <;>
    cases c <;> simp only [Bool.toNat_false,Bool.toNat_true] at he <;> omega

theorem nafSign_ok (s : State) :
    WP isa (.block Naf.sign) s fun t =>
      t.gpr .edx=0#32-(s.gpr .ecx>>>31) ∧ CKeeps [.eax,.edx] s t := by
  unfold Naf.sign
  refine wp_movS rfl fun s₁ U₁ _ => ?_
  refine wp_shr (by decide) fun s₂ U₂ _ => ?_
  refine wp_movS rfl fun s₃ U₃ _ => ?_
  refine wp_subS rfl fun t U₄ _ => WP.block_nil ?_
  refine ⟨?_,fun r hr => ?_,?_,?_,?_⟩
  · rw [U₄.gpr,U₃.gpr,U₃.other _ (by decide),U₂.gpr,U₁.gpr]
    rfl
  · have ha : r≠.eax := fun h => hr (h ▸ (by simp))
    have hd : r≠.edx := fun h => hr (h ▸ (by simp))
    rw [U₄.other _ hd,U₃.other _ hd,U₂.other _ ha,U₁.other _ ha]
  · rw [U₄.mem,U₃.mem,U₂.mem,U₁.mem]
  · rw [U₄.rd,U₃.rd,U₂.rd,U₁.rd]
  · rw [U₄.wr,U₃.wr,U₂.wr,U₁.wr]

theorem nafSubtract_ok {s : State} {base : Addr} {size work k j : Nat}
    (hs : Scr s base size) (ha : work+36≤size)
    (hx : s.gpr .ecx=BitVec.ofInt 32 (Naf5.digit k j))
    (hv : val32 s.mem base work 9=Naf5.residual k j)
    (hb : Naf5.residual k j≤2^256) :
    WP isa (.block (Naf.subtractDigit work)) s fun t =>
      val32 t.mem base work 9=2*Naf5.residual k (j+1) ∧
      Keeps [.eax,.edx] s t ∧ Outside base work 36 s.mem t.mem := by
  rw [Naf.subtractDigit,List.append_assoc,WP.block_append_iff]
  refine WP.mono (nafSign_ok s) fun a ⟨va,ka⟩ => ?_
  refine WP.mono (nafSubChain_ok (hs.of_keeps ka.keeps (by decide)) 8 ha)
    fun t ⟨ot,⟨c,hc,vt⟩,kt⟩ => ⟨?_,ka.keeps.trans (kt.mono (by decide)),?_⟩
  · rw [va,ka.1 .ecx (by decide),ka.2.1,hx] at vt
    have hlt : val32 t.mem base work 9 < 2^288 := by
      simpa only [show 32*9=288 from rfl] using val32_lt t.mem base work 9
    have radix : (2:Nat)^288 = 497323236409786642155382248146820840100456150797347717440463976893159497012533375533056 := by decide +kernel
    have ve : val32 t.mem base work 9 + nafDigitVal (BitVec.ofInt 32 (Naf5.digit k j))
        (0#32-(BitVec.ofInt 32 (Naf5.digit k j)>>>31)) 8 =
        val32 s.mem base work 9 + 2^288*c.toNat := by
      simpa only [Nat.reduceAdd,Nat.reduceMul,radix] using vt
    exact nafSubtract_next (c := c) k j hv (by omega) hlt ve
  · rw [ka.2.1] at ot
    exact ot

end VG.Proof.Weierstrass.X86

end

/-! ## `NafAdjust` -/

section

/-! Choose and subtract one signed width-five digit from the public residual. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86
  VG.Proof.Mont.X86 VG.Proof.Mont

theorem nafAdjust_ok {s : State} {base : Addr} {size work k j : Nat}
    (hs : Scr s base size) (ha : work+36≤size)
    (hv : val32 s.mem base work 9=Naf5.residual k j)
    (hb : Naf5.residual k j≤2^256) :
    WP isa (Naf.adjust work) s fun t =>
      t.gpr .ecx=BitVec.ofInt 32 (Naf5.digit k j) ∧
      val32 t.mem base work 9=2*Naf5.residual k (j+1) ∧
      Keeps [.eax,.ecx,.edx] s t ∧ Outside base work 36 s.mem t.mem := by
  rw [Naf.adjust]
  refine WP.seq (wp_movS (readSrc_sc hs (by omega)) fun a ua _ => ?_)
  refine WP.mono (nafParity_ok a) fun b ⟨vb,zb,kb⟩ => ?_
  have sa := hs.of_keeps ua.keeps (by decide)
  have sb := sa.of_keeps kb.keeps (by decide)
  have mb : b.mem=s.mem := kb.2.1.trans ua.mem
  have low : (a.gpr .eax).toNat%32=Naf5.residual k j%32 := by
    rw [ua.gpr]
    have he : val32 s.mem base work 9 =
        w32 s.mem base work+2^32*val32 s.mem base (work+4) 8 := rfl
    change w32 s.mem base work%32=_
    omega
  have hd := nafRaw_eq low
  have K : Keeps [.eax,.ecx,.edx] s b :=
    (ua.keeps.mono (by decide)).trans (kb.keeps.mono (by decide))
  refine WP.ite (decide (a.gpr .eax &&& 1=0)) zb (fun h => ?_) (fun h => ?_)
  · have h0 := of_decide_eq_true h
    have hp := (nafParity _).mp h0
    have he : Naf5.residual k j%2=0 := by omega
    have hn : Naf5.residual k j=2*Naf5.residual k (j+1) := by
      simp only [Naf5.residual_succ,Naf5.next,he,ite_true]
      omega
    apply WP.block_nil
    refine ⟨?_,?_,K,?_⟩
    · rw [vb,h0]
      simpa only [nafRaw,h0,ite_true] using hd
    · rw [mb,hv,hn]
    · rw [mb]; exact Outside.refl _ _ _ _
  · have h0 := of_decide_eq_false h
    refine WP.seq (WP.mono (nafOdd_ok b) fun c ⟨vc,kc⟩ => ?_)
    have hc : c.gpr .ecx=BitVec.ofInt 32 (Naf5.digit k j) := by
      rw [vc,kb.1 .eax (by decide)]
      simpa only [nafRaw,h0,ite_false] using hd
    have mc : c.mem=s.mem := kc.2.1.trans mb
    refine WP.mono (nafSubtract_ok (sb.of_keeps kc.keeps (by decide)) ha hc
      (by rw [mc]; exact hv) hb) fun t ⟨vt,kt,ot⟩ => ⟨?_,vt,?_,?_⟩
    · rw [kt.1 .ecx (by decide),hc]
    · exact (K.trans (kc.keeps.mono (by decide))).trans (kt.mono (by decide))
    · rw [mc] at ot; exact ot

end VG.Proof.Weierstrass.X86

end
