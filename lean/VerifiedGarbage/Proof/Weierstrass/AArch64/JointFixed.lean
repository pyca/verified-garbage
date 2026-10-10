import VerifiedGarbage.Proof.Weierstrass.AArch64.JointGenerator
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointPairedTiming

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass

structure JointFixedLayout (c : Joint.Cfg) (size : Nat) : Prop where
  layout : JointLayout c size
  exy : c.K.E.y=c.K.E.x+32
  entryNodup : [c.K.E.x,c.K.E.y,c.K.E.z].Nodup
  accumulator : ∀ x∈[c.K.R.x,c.K.R.y,c.K.R.z],x∉[c.K.E.x,c.K.E.y,c.K.E.z]
  oneLive : c.onep∈jointLive c
  oneApart : c.onep∉[c.K.E.x,c.K.E.y,c.K.E.z]
  gBits : c.gBits<4096
  addApart : RcbApart c.K.S c.K.R c.K.E c.K.D
  copyApart : RcbApart c.K.S c.K.D c.K.D c.K.R

theorem jointEntry_slots (c : Joint.Cfg) : ∀ x∈[c.K.E.x,c.K.E.y,c.K.E.z],x∈jointSlots c := by
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
    simp [jointSlots,jacWinSlots,winOther,rcbW]

theorem jointEntry_work (c : Joint.Cfg) : ∀ x∈[c.K.E.x,c.K.E.y,c.K.E.z],x∈jointWork c := by
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl <;> simp [jointWork,winOther,rcbW]

theorem jointLookup_generator_ok {c : Joint.Cfg} {C : Curve} {base T : Addr} {size u v j : Nat}
    {G Q A : Point C} {s : State} (hL : JointFixedLayout c size)
    (h : JointCore c C base size Q u v (JointGenerator c C base size G T) A s)
    (h2 : s.gpr .x2=(FastNaf.byte 7 u j).setWidth 64)
    (hm0 : FastNaf.magnitude 7 u j≠0) :
    WP isa (.block (Naf.digitIndex++Joint.fixedLoad c)) s fun t =>
      ProgKeep c.K.M base [c.K.E.x,c.K.E.y,c.K.E.z] s t ∧
      JointCore c C base size Q u v (JointGenerator c C base size G T) A t ∧
      Inv c.K.M base size C.p (·∈jointSlots c)
        ([c.K.E.x,c.K.E.y,c.K.E.z]++jointLive c) (tmv C c.K.M.n base t) t ∧
      InvJ C (tmv C c.K.M.n base t c.K.E.x) (tmv C c.K.M.n base t c.K.E.y)
        (tmv C c.K.M.n base t c.K.E.z) (mul (FastNaf.magnitude 7 u j) G) ∧
      tmv C c.K.M.n base t c.K.E.z=1 := by
  let a := (FastNaf.magnitude 7 u j+1)/2
  have hmag := FastNaf.magnitude_le (w:=7) (Or.inr rfl) u j
  have hodd := (FastNaf.magnitude_odd_or_zero 7 u j).resolve_left hm0
  have ha : 1≤a := by dsimp [a]; omega
  have ha32 : a≤32 := by dsimp [a]; change FastNaf.magnitude 7 u j≤63 at hmag; omega
  have he : 2*a-1=FastNaf.magnitude 7 u j := by dsimp [a]; omega
  have hbmag : nafMagnitude (FastNaf.byte 7 u j)=FastNaf.magnitude 7 u j := FastNaf.byte_magnitude 7 u j
  have hnodup := hL.entryNodup
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hnodup
  have hnot := hL.oneApart
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hnot
  have hout {W : List Nat} (hw : ∀ x∈W,x∈jointSlots c) : ∀ x∈W,x+8*c.K.M.n≤size :=
    fun x hx => hL.layout.lay.le x (hw x hx)
  rw [WP.block_append_iff]
  refine WP.mono_syms (nafIndex_ok h2) fun b ⟨b2,kb⟩ sb => ?_
  rw [hbmag] at b2
  have kpb : ProgKeep c.K.M base [] s b := keeps_prog kb (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [clob])
  have eb := h.external.keep kpb sb (by simp) h.field.mod.tmp
  have cb := h.of_keeps kb (by decide) eb
  refine WP.mono_syms (jointFixedPoint_ok c hL.layout.lay hL.layout.aligned hL.layout.n cb.field ha b2
    eb.symbol hL.exy (jointEntry_slots c) hnodup.1.2 hnodup.2.1
    (Ne.symm hnot.1) (Ne.symm hnot.2.1) hL.oneLive cb.stable.one
    (eb.read a ha ha32) (eb.outside a ha ha32) (eb.bounds a ha ha32) (eb.point a ha ha32))
    fun d ⟨kd,id,jd,zd⟩ sd => ?_
  have ed := eb.keep kd sd (hout (jointEntry_slots c)) cb.field.mod.tmp
  have cd := cb.of_write hL.layout kd (jointEntry_work c) (jointEntry_slots c) hL.accumulator
    (id.sub (fun _ hx => List.mem_append_right _ hx)) ed
  rw [he] at jd
  exact ⟨(kpb.mono (by simp)).trans kd,cd,id,jd,zd⟩

theorem jointEntry_generator_ok {c : Joint.Cfg} {C : Curve} {base T : Addr} {size u v j : Nat}
    {G Q A : Point C} {s : State} (hL : JointFixedLayout c size)
    (hm : UnitMod C.p (2^(64*c.K.M.n)))
    (h : JointCore c C base size Q u v (JointGenerator c C base size G T) A s)
    (hj : j<257) (h2 : s.gpr .x2=(FastNaf.byte 7 u j).setWidth 64)
    (h19 : s.gpr .x19=BitVec.ofNat 64 j)
    (hm0 : FastNaf.magnitude 7 u j≠0) :
    WP isa (Joint.fixedEntry c) s fun t =>
      ProgKeep c.K.M base (jointWork c) s t ∧
      JointCore c C base size Q u v (JointGenerator c C base size G T) A t ∧
      Inv c.K.M base size C.p (·∈jointSlots c)
        ([c.K.E.x,c.K.E.y,c.K.E.z]++jointLive c) (tmv C c.K.M.n base t) t ∧
      InvJ C (tmv C c.K.M.n base t c.K.E.x) (tmv C c.K.M.n base t c.K.E.y)
        (tmv C c.K.M.n base t c.K.E.z) (FastNaf.point C G 7 u j) ∧
      tmv C c.K.M.n base t c.K.E.z=1 := by
  let a := (FastNaf.magnitude 7 u j+1)/2
  have hmag := FastNaf.magnitude_le (w:=7) (Or.inr rfl) u j
  have hodd := (FastNaf.magnitude_odd_or_zero 7 u j).resolve_left hm0
  have ha : 1≤a := by dsimp [a]; omega
  have ha32 : a≤32 := by dsimp [a]; change FastNaf.magnitude 7 u j≤63 at hmag; omega
  have he : 2*a-1=FastNaf.magnitude 7 u j := by dsimp [a]; omega
  have hbmag : nafMagnitude (FastNaf.byte 7 u j)=FastNaf.magnitude 7 u j := FastNaf.byte_magnitude 7 u j
  have hnodup := hL.entryNodup
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hnodup
  have hnot := hL.oneApart
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hnot
  have hout {W : List Nat} (hw : ∀ x∈W,x∈jointSlots c) : ∀ x∈W,x+8*c.K.M.n≤size :=
    fun x hx => hL.layout.lay.le x (hw x hx)
  rw [Joint.fixedEntry]
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono_syms (nafIndex_ok h2) fun b ⟨b2,kb⟩ sb => ?_
  rw [hbmag] at b2
  have kpb : ProgKeep c.K.M base [] s b := keeps_prog kb (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [clob])
  have eb := h.external.keep kpb sb (by simp) h.field.mod.tmp
  have cb := h.of_keeps kb (by decide) eb
  refine WP.mono_syms (jointFixedPoint_ok c hL.layout.lay hL.layout.aligned hL.layout.n cb.field ha b2
    eb.symbol hL.exy (jointEntry_slots c) hnodup.1.2 hnodup.2.1
    (Ne.symm hnot.1) (Ne.symm hnot.2.1) hL.oneLive cb.stable.one
    (eb.read a ha ha32) (eb.outside a ha ha32) (eb.bounds a ha ha32) (eb.point a ha ha32))
    fun d ⟨kd,id,jd,zd⟩ sd => ?_
  have ed := eb.keep kd sd (hout (jointEntry_slots c)) cb.field.mod.tmp
  have cd := cb.of_write hL.layout kd (jointEntry_work c) (jointEntry_slots c) hL.accumulator
    (id.sub (fun _ hx => List.mem_append_right _ hx)) ed
  rw [he] at jd
  have d19 : d.gpr .x19=BitVec.ofNat 64 j := by
    rw [kd.gpr _ (x19_not_clob _),kb.gpr _ (by decide),h19]
  have hzero : tmv C c.K.M.n base d c.K.zero=0 := by
    unfold tmv; rw [cd.stable.peer.zero,toM_zero]
  have hzeroLive : c.K.zero∈jointLive c := by simp [jointLive,nafLive,winRo]
  have hv : ∀ x∈[c.K.E.x,c.K.E.y,c.K.E.z,c.K.zero],
      x∈[c.K.E.x,c.K.E.y,c.K.E.z]++jointLive c := by
    intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp [hzeroLive]
  have hbytes : c.gBits+j<size := by
    have := hL.layout.stableBounds (c.gBits,257) (by simp [jointStableRanges]); dsimp only at this; omega
  refine WP.mono_syms (jointSignEntry_ok c hL.layout.lay hL.layout.aligned hm id hv
    hnodup.1.1 (Ne.symm hnodup.2.1) hzero hL.gBits hbytes d19 (cd.stable.generator j hj) jd zd)
    fun t ⟨Et,kt,it,jt,zt⟩ st => ?_
  have hyw : ∀ x∈[c.K.E.y],x∈jointWork c := by
    intro x hx; rw [List.mem_singleton.mp hx]; exact jointEntry_work c _ (by simp)
  have hys : ∀ x∈[c.K.E.y],x∈jointSlots c := by
    intro x hx; rw [List.mem_singleton.mp hx]; exact jointEntry_slots c _ (by simp)
  have et := ed.keep kt st (hout hys) cd.field.mod.tmp
  have ct := cd.of_write hL.layout kt hyw hys (by
    intro x hx hy; exact hL.accumulator x hx (by rw [List.mem_singleton.mp hy]; simp))
    (it.sub (fun _ hx => List.mem_append_right _ hx)) et
  refine ⟨(kpb.mono (by simp)).trans ((kd.mono (jointEntry_work c)).trans (kt.mono hyw)),ct,it.to_tmv,?_,?_⟩
  · have jp := it.point_tmv (fun _ hx => List.mem_append_left _ hx) jt
    simpa only [nafNegative,FastNaf.byte_negative,FastNaf.point] using jp
  · exact (it.val c.K.E.z (by simp)).trans zt

end VG.Proof.Weierstrass.AArch64
