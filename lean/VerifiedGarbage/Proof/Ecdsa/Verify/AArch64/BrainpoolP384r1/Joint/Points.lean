module

public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.ProjectiveFlags
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.Loop
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Scalars
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.Digit

import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.LoopOps
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.Math
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.Table
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.TableLayout
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.Moves
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint.Math
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.CompactStep
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bits
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
/-! The joint multiplier feeds the unchanged complete ECDSA final check. -/

-- Formerly `VerifiedGarbage/Proof/Ecdsa/Verify/AArch64/BrainpoolP384r1/Joint/CompactLoop.lean`, which only this module imported.
section

/-! The fifteen table additions share one bounded public loop. -/

section
namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps read_x)
open VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint

theorem tableIncrement_ok (s : State) {d : Nat} (h19 : s.gpr .x19=BitVec.ofNat 64 d) :
    WP isa (.block [.addImm .x .x19 .x19 1,.subImm .x .x6 .x19 16]) s fun t =>
      t.gpr .x19=BitVec.ofNat 64 (d+1) ∧
      t.gpr .x6=BitVec.ofNat 64 (d+1)-16 ∧ Keeps [.x19,.x6] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    show (1 : Nat)<4096 by decide,show (16 : Nat)<4096 by decide,
    ite_true,BitVec.setWidth_eq,RegUpd.gpr_write,reduceCtorEq,ite_false,h19,
    Option.some.injEq,exists_eq_left']
  have e : BitVec.ofNat 64 d+1=BitVec.ofNat 64 (d+1) := by
    change BitVec.ofNat 64 d+BitVec.ofNat 64 1=_
    rw [←BitVec.ofNat_add]
  refine ⟨e,congrArg (fun x : BitVec 64 => x-BitVec.ofNat 64 16) e,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  simp only [List.mem_cons,not_or] at hr
  simp only [RegUpd.gpr_write,hr.1,hr.2,ite_false]

theorem tableLoopStep_ok {base : Addr} {P Q : Point C} {s : State}
    (hc : BaseCfgOk cfg) (hC : Law C) (hP : onCurve C P=true) (hQ : onCurve C Q=true)
    {d : Nat} (h1 : 1 ≤ d) (h15 : d ≤ 15) (hi : Inputs base P Q s)
    (ht : Table base P Q (d-1) s) (h19 : s.gpr .x19=BitVec.ofNat 64 d) :
    WP isa tableLoopStep s fun t =>
      Changes base arithmeticWork s t ∧ Inputs base P Q t ∧ Table base P Q d t ∧
      t.gpr .x19=BitVec.ofNat 64 (d+1) ∧ t.gpr .x6=BitVec.ofNat 64 (d+1)-16 := by
  rw [tableLoopStep]
  refine WP.seq (WP.mono (prepChoice_ok hc hC h1 h15 hi ht h19) fun a ⟨⟨W,I,R,E⟩,c⟩ => ?_)
  have hA : onCurve C (pair P Q ((previous d)%4) ((previous d)/4))=true := pair_curve hC hP hQ _ _
  have he : onCurve C (if d%4=0 then Q else P)=true := by split <;> with_reducible assumption
  refine WP.seq (WP.mono (sum_points hc hC I.scr I.mod I.a I.b I.a_lt I.b_lt he hA E R)
    fun b ⟨W',R',c'⟩ => ?_)
  have K := W.trans (W'.mono addWork_sub)
  have I' := hi.unch (K.mono loopWork_sub)
  have T : Table base P Q (d-1) b := fun j hj hjm => K.table hi.scr hj (by omega) (ht j hj hjm)
  rw [table_step hC hP hQ h1] at R'
  refine WP.seq (WP.mono (storeChoice_ok h1 h15 I' T R' (c'.trans (c.trans h19)))
    fun u ⟨⟨L,Iu,Tu⟩,cu⟩ => ?_)
  refine WP.mono (tableIncrement_ok u (cu.trans (c'.trans (c.trans h19)))) fun t ⟨ct,ft,kt⟩ => ?_
  have Z : Changes base arithmeticWork u t := Changes.of_keeps kt (by decide)
  exact ⟨((K.mono loopWork_sub).trans L).trans Z,Iu.unch Z,
    fun j hj hjd => (Tu j hj hjd).of_mem kt.mem,ct,ft⟩

theorem buildTable_ok {base : Addr} {P Q : Point C} {s : State}
    (hc : BaseCfgOk cfg) (hC : Law C) (hP : onCurve C P=true) (hQ : onCurve C Q=true)
    (hi : Inputs base P Q s) :
    WP isa buildTable s fun t =>
      Changes base arithmeticWork s t ∧ Inputs base P Q t ∧ Table base P Q 15 t := by
  rw [buildTable]
  refine WP.seq (WP.mono (setCounter_ok s (j:=1) (by decide)) fun a ⟨ca,ka⟩ => ?_)
  have Wa : Changes base arithmeticWork s a := Changes.of_keeps ka (by decide)
  let Inv := fun j t => Changes base arithmeticWork s t ∧ Inputs base P Q t ∧
    Table base P Q (15-j) t ∧ t.gpr .x19=BitVec.ofNat 64 (16-j)
  refine WP.loop (M:=isa) (fun j t => 1 ≤ j ∧ j ≤ 15 ∧ Inv j t)
    (fun j t ⟨h1,h15,ht⟩ => ?_) 15 a ⟨by decide,by decide,Wa,hi.unch Wa,?_,ca⟩
  · obtain ⟨W,I,T,c⟩ := ht
    have T' : Table base P Q ((16-j)-1) t := by simpa only [show 16-j-1=15-j by omega] using T
    refine WP.mono (tableLoopStep_ok hc hC hP hQ (by omega) (by omega) I T' c)
      fun u ⟨L,Iu,Tu,cu,fu⟩ => ?_
    by_cases e : j=1
    · subst j
      refine Or.inl ⟨?_,W.trans L,Iu,Tu⟩
      change some (u.read .x .x6 != 0)=some false
      rw [read_x,fu]; rfl
    · refine Or.inr ⟨?_,j-1,by omega,by omega,by omega,W.trans L,Iu,?_,?_⟩
      · change some (u.read .x .x6 != 0)=some true
        rw [read_x,fu]
        apply congrArg some
        rw [bne_iff_ne]
        intro hz
        have hh := congrArg BitVec.toNat hz
        rw [BitVec.toNat_sub,BitVec.toNat_ofNat] at hh
        change (2^64-16+((16-j+1)%(2^64)))%(2^64)=0 at hh
        rw [Nat.mod_eq_of_lt (by omega : 16-j+1 < 2^64)] at hh
        omega
      · simpa only [show 15-(j-1)=16-j by omega] using Tu
      · simpa only [show 16-(j-1)=16-j+1 by omega] using cu
  · intro j hj h0; omega
end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint
end

end

-- Formerly `VerifiedGarbage/Proof/Ecdsa/Verify/AArch64/BrainpoolP384r1/Joint/Prepare.lean`, which only this module imported.
section

/-! Preparing the two bit tables and the general complete-addition coefficient. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Spec.Weierstrass
open VG.Impl.Ecdsa.Verify.AArch64 (U V)
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint

abbrev prepWork : List (Nat × Nat) := [(bitsU,768),(cfg.sl EXPP,48)]

theorem generator_point {base : Addr} {s : State} {g : Reg → BitVec 64}
    (hc : BaseCfgOk cfg) (hC : Law C) (hf : Fixed cfg base g s.mem) :
    PointAt base s gSource (G C) := by
  have hp : 0 < cfg.C.p := by have := hc.p_ge; omega
  have hm (x : Nat) : cfg.mont x < C.p := Nat.mod_lt _ hp
  have e1 : num base s (cfg.sl ONEP)=cfg.mont 1 := by
    rw [num,hf.onep]; simp only [Cfg.mont,Cfg.R,Nat.one_mul]
  refine ⟨?_,?_⟩
  · intro x hx
    simp only [coordinates,gSource,Cfg.pt,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [num,hf.gx]; exact hm _
    · rw [num,hf.gy]; exact hm _
    · rw [e1]; exact hm _
  · have ex : val base s gSource.x=Fin.ofNat C.p C.gx :=
      (congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) hf.gx).trans (toM_cmont hc _)
    have ey : val base s gSource.y=Fin.ofNat C.p C.gy :=
      (congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) hf.gy).trans (toM_cmont hc _)
    have ez : val base s gSource.z=1 :=
      (congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) e1).trans (toM_cmont hc 1)
    rw [ex,ey,ez]
    exact rep_affine' hC _ _

theorem prepare_ok {base : Addr} {s₀ s : State} {g : Reg → BitVec 64} {P : Point C}
    (hc : BaseCfgOk cfg) (hC : Law C) (hM : Mid cfg s₀ base g s)
    (hrep : Rep C (val base s qSource.x) (val base s qSource.y) (val base s qSource.z) P) :
    WP isa prepare s fun t =>
      Changes base prepWork s t ∧ Inputs base (G C) P t ∧
      Bits base (sv cfg base s U) (sv cfg base s V) t := by
  have hn8 : cfg.n=6 := rfl
  have boundV : cfg.sl V+48 ≤ 8192 := by decide
  have hs := hM.scr
  have hn := hs.nowrap
  have hm0 : 0 < cfg.C.p := by have := hc.p_ge; omega
  have hm (x : Nat) : cfg.mont x < C.p := Nat.mod_lt _ hm0
  have hbconst : cfg.mont (3*cfg.C.b) < 2^(64*cfg.n) := Nat.lt_trans (hm _) hc.p_lt
  rw [prepare]
  refine WP.seq (WP.mono (bits_ok hs (n:=6) (src:=cfg.sl U) (dst:=bitsU)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide)))
    fun s₁ ⟨b₁,k₁,u₁⟩ => ?_)
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  have v₁ : wordsVal s₁.mem base (cfg.sl V) 6=wordsVal s.mem base (cfg.sl V) 6 :=
    u₁.wordsVal (by decide) (by omega)
  refine WP.seq (WP.mono (bits_ok hs₁ (n:=6) (src:=cfg.sl V) (dst:=bitsV)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide)))
    fun s₂ ⟨b₂,k₂,u₂⟩ => ?_)
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  refine WP.mono (setConst_ok hs₂ (n:=cfg.n) (o:=cfg.sl EXPP) (by decide) (by decide) hbconst)
    fun t ⟨b₃,k₃,u₃⟩ => ?_
  have W : Changes base prepWork s t := by
    have kt := (k₁.trans k₂).trans (k₃.mono (by decide))
    refine ⟨kt.gpr _ (by decide),kt.rd,kt.wr,kt.sp,?_⟩
    exact (u₁.unch.trans (u₂.unch.trans u₃.unch)).cover (by
      intro w hw
      simp only [List.mem_append,List.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact ⟨(bitsU,768),by simp,by decide,by decide⟩
      · exact ⟨(bitsU,768),by simp,by decide,by decide⟩
      · exact ⟨(cfg.sl EXPP,48),by simp,by decide,by decide⟩)
  have F := hM.fixed.unch hc.n10 hn (by unfold FixedOk prepWork; decide) W.mem
  have hqp : PointAt base s qSource P := by
    refine ⟨?_,hrep⟩
    intro x hx
    simp only [coordinates,qSource,Cfg.pt,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact hM.px_lt
    · exact hM.py_lt
    · rw [num,hM.fixed.onep]; exact Nat.mod_lt _ hm0
  have I : Inputs base (G C) P t := by
    refine ⟨W.scr hs,modP_of hc F.mp,?_,?_,?_,?_,generator_point hc hC F,
      W.point hs hqp (by decide) (by decide)⟩
    · rw [num,F.ap]; exact hm _
    · rw [num,b₃]; exact hm _
    · exact (congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) F.ap).trans (toM_cmont hc _)
    · exact (congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) b₃).trans (toM_cmont hc _)
  refine ⟨W,I,?_,?_⟩
  · intro j hj
    rw [u₃.unch.byte (by intro w hw; rw [List.mem_singleton.mp hw]; change _ ≤ _ ∨ 640+48 ≤ 2944+j; omega)
        (by change 2944+j < 2^64; omega),
      u₂.unch.byte (by intro w hw; rw [List.mem_singleton.mp hw]; change 2944+j+1 ≤ 3328 ∨ _; omega)
        (by change 2944+j < 2^64; omega),b₁ j hj]
    rfl
  · intro j hj
    rw [u₃.unch.byte (by intro w hw; rw [List.mem_singleton.mp hw]; change _ ≤ _ ∨ 640+48 ≤ 3328+j; omega)
        (by change 3328+j < 2^64; omega),b₂ j hj,v₁]
    rfl
end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint
end

end

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Spec.Weierstrass
open VG.Impl.Ecdsa.Verify.AArch64 (U V RM')
open VG.Proof.Ed25519.AArch64 (Keeps)
open VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint

theorem arithmeticWork_sub : ∀ w ∈ arithmeticWork,w ∈ work := by decide
theorem prepWork_sub : ∀ w ∈ prepWork,w ∈ work := by decide

theorem setup_ok {base : Addr} {s₀ s : State} {g : Reg → BitVec 64} {P : Point C}
    (hc : BaseCfgOk cfg) (hC : Law C) (hP : onCurve C P=true) (hM : Mid cfg s₀ base g s)
    (hrep : Rep C (val base s qSource.x) (val base s qSource.y) (val base s qSource.z) P) :
    WP isa setup s fun t => Changes base work s t ∧
      Running base (G C) P (sv cfg base s U) (sv cfg base s V) 192 t := by
  rw [setup]
  refine WP.seq (WP.mono (prepare_ok hc hC hM hrep) fun s₁ ⟨k₁,I₁,B₁⟩ => ?_)
  refine WP.seq (WP.mono (buildTable_ok hc hC hc.onG hP I₁) fun s₂ ⟨k₂,I₂,T₂⟩ => ?_)
  have B₂ := k₂.bits B₁
  rw [WP.block_append_iff]
  refine WP.mono (infinity_ok I₂.scr hc hC) fun s₃ ⟨k₃,R₃,_⟩ => ?_
  have W₃ := k₃.mono resultWork_sub
  have I₃ := I₂.unch (W₃.mono loopWork_sub)
  have B₃ := (W₃.mono loopWork_sub).bits B₂
  have T₃ := T₂.of_changes I₂.scr W₃
  refine WP.mono (setCounter_ok s₃ (j:=192) (by decide)) fun s₄ ⟨c₄,k₄⟩ => ?_
  have W₄ : Changes base loopWork s₃ s₄ := Changes.of_keeps k₄ (by decide)
  have I₄ := I₃.unch (W₄.mono loopWork_sub)
  have B₄ := (W₄.mono loopWork_sub).bits B₃
  have T₄ := T₃.of_changes I₃.scr W₄
  have R₄ := R₃.of_mem k₄.mem
  have hu := Nat.lt_trans hM.u_lt hc.n_lt
  have hv := Nat.lt_trans hM.v_lt hc.n_lt
  have hstart := at_top (G C) P (n:=cfg.n) hu hv
  rw [show 32*cfg.n=192 from rfl] at hstart
  rw [←hstart] at R₄
  exact ⟨(((k₁.mono prepWork_sub).trans (k₂.mono arithmeticWork_sub)).trans
    ((W₃.mono loopWork_sub).mono arithmeticWork_sub)).trans
    ((W₄.mono loopWork_sub).mono arithmeticWork_sub),⟨I₄,B₄,T₄,c₄,R₄⟩⟩

theorem points_raw {base : Addr} {s₀ s : State} {g : Reg → BitVec 64} {P : Point C}
    (hc : BaseCfgOk cfg) (hC : Law C) (hP : onCurve C P=true) (hM : Mid cfg s₀ base g s)
    (hrep : Rep C (val base s qSource.x) (val base s qSource.y) (val base s qSource.z) P) :
    WP isa points s fun t =>
      Changes base work s t ∧ PointAt base t resultPt
        (add (mul (sv cfg base s U) (G C)) (mul (sv cfg base s V) P)) := by
  rw [points]
  refine WP.seq (WP.mono (setup_ok hc hC hP hM hrep) fun s₄ ⟨k₄,R₄⟩ => ?_)
  refine WP.mono (loop_ok hc hC hc.onG hP R₄) fun t ⟨k₅,h₅⟩ => ?_
  have W := k₄.trans ((k₅.mono loopWork_sub).mono arithmeticWork_sub)
  have p := h₅.point
  rw [at_zero] at p
  exact ⟨W,p⟩

theorem final_state {base : Addr} {s₀ s t : State} {g : Reg → BitVec 64} {P : Point C}
    (hc : BaseCfgOk cfg) (hM : Mid cfg s₀ base g s) (h : Changes base work s t)
    (hp : PointAt base t resultPt P) : FinalState cfg s₀ base g t := by
  have hn := hM.scr.nowrap
  have flagBound : cfg.sl FLAG+8 ≤ 8192 := by decide
  have hn8 : cfg.n=6 := rfl
  have same (i : Nat) (hle : cfg.sl i+48 ≤ 8192)
      (hap : ∀ w ∈ work,cfg.sl i+48 ≤ w.1 ∨ w.1+w.2 ≤ cfg.sl i) :
      sv cfg base t i=sv cfg base s i :=
    h.mem.wordsVal hap (by omega)
  have r := same RM' (by decide) (by decide)
  have k := same K (by decide) (by decide)
  refine ⟨h.scr hM.scr,h.wr.trans hM.wr,h.rd.trans hM.rd,
    hM.fixed.unch hc.n10 hn (by unfold FixedOk work loopWork addWork entryWork; decide) h.mem,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [h.mem.word (by decide) (by omega)]
    exact hM.flag
  · rw [r]; exact hM.rm_lt
  · rw [r]; exact hM.rm
  · exact hp.1 _ (by decide)
  · exact (hM.unch.trans h.mem).cover (by
      intro w hw
      refine ⟨(0,8192),by simp,by omega,?_⟩
      rcases List.mem_append.mp hw with hw | hw
      · rw [List.mem_singleton.mp hw]
      · have hd : ∀ w ∈ work,w.1+w.2 ≤ 8192 := by decide
        exact hd w hw)
  · exact k.trans hM.k
  · exact hp.1 _ (by decide)

theorem points_ok {base : Addr} {s₀ s : State} {g : Reg → BitVec 64} {P : Point C}
    (hc : BaseCfgOk cfg) (hC : Law C) (hP : onCurve C P=true) (hM : Mid cfg s₀ base g s)
    (hrep : Rep C (val base s qSource.x) (val base s qSource.y) (val base s qSource.z) P) :
    WP isa points s fun t => FinalState cfg s₀ base g t ∧
      Rep C (val base t resultPt.x) (val base t resultPt.y) (val base t resultPt.z)
        (add (mul (sv cfg base s U) (G C)) (mul (sv cfg base s V) P)) :=
  WP.mono (points_raw hc hC hP hM hrep) fun _ ⟨W,p⟩ => ⟨final_state hc hM W p,p.2⟩
end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint
