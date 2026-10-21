module

public import VerifiedGarbage.Proof.Weierstrass.Arm.TCombConfig
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombStep
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombStart
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombScan
import VerifiedGarbage.Proof.Weierstrass.Arm.Loop
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Correctness of the complete ARM signed-comb scalar multiplication. -/

@[expose] public section
namespace VG.Proof.Weierstrass.Arm.TComb
open VG VG.Arm VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass.Arm.Point
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.X25519.Arm
open VG.Proof.Weierstrass.Arm.Point
open Spec.Weierstrass

theorem comb_ok (K : TCombCfg) {C : Curve} {tbl : List (List (Nat × Nat))} {start : Nat × Nat}
    (h : Config K C tbl start) (hC : Law C) (hG : onCurve C (G C)=true)
    {s : State} {base T : Addr} {k : Nat}
    (hs : Scr s base 4096) (hf : Far s base 8192)
    (ht : TableMem s T (tableWords K C tbl)) (sym : State.addr (s.syms K.tsym)=T)
    (hd : Region.Disjoint ⟨T,8*(tableWords K C tbl).length⟩ ⟨base,4096⟩)
    (hk : k<2^K.L.nbits) (zero : wordsVal s.mem base K.zero K.L.M.n=0)
    (bits : ∀ i<K.L.nbits,s.mem (off base (K.L.bits+i))=if k.testBit i then 1 else 0)
    (coeffA : wordsVal s.mem base K.L.S.a K.L.M.n=C.a*2^(64*K.L.M.n)%C.p)
    (coeffB : wordsVal s.mem base K.L.S.b3 K.L.M.n=(3*C.b)*2^(64*K.L.M.n)%C.p) :
    WP isa K.comb s fun t =>
      Rest powClob s t ∧ Unch base (writes K) s.mem t.mem ∧
      (∀ x ∈ [K.L.R.x,K.L.R.y,K.L.R.z],wordsVal t.mem base x K.L.M.n<C.p) ∧
      Rep C (tmv C K.L.M.n base t K.L.R.x) (tmv C K.L.M.n base t K.L.R.y)
        (tmv C K.L.M.n base t K.L.R.z) (mul k (G C)) := by
  have hp : 0<C.p := Nat.pos_of_ne_zero (NeZero.ne C.p)
  have fit := h.modulus.m_lt
  have sx : K.start.1<C.p := by rw [h.startX]; exact Nat.mod_lt _ hp
  have sy : K.start.2<C.p := by rw [h.startY]; exact Nat.mod_lt _ hp
  unfold TCombCfg.comb
  refine WP.seq (WP.mono_syms (start_ok K h.layout hs (Nat.lt_trans sx fit) (Nat.lt_trans sy fit)
    (Nat.lt_trans h.one_lt fit) h.encJ) fun u ⟨ku,ou,cp,gu,xu,yu,zu⟩ syu => ?_)
  have frame : Frame [⟨base,4096⟩] s.mem u.mem := outside_frame
    (ou.outside (o := 0) (n := 4096) h.layout.bounded) (Nat.le_refl _)
  have low := h.layout.low K.zero (by simp)
  have hl := lay_nums h.layout.n3 h.layout.n6
  have iu : CurveInputs K C tbl base T k u := by
    refine ⟨hs.of_rest ku (by decide),hf.of_rest ku,
      ht.of_frame (by rw [ku.rd,ku.wr]) frame (by simpa only [List.mem_singleton,forall_eq] using hd),
      by rw [syu]; exact sym,?_,?_,?_,?_⟩
    · rw [ou.wordsVal (by
        intro r hr
        simp only [writes,List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl|rfl|rfl|rfl
        · exact h.layout.zeroApart _ (by simp)
        · exact h.layout.zeroApart _ (by simp)
        · exact h.layout.zeroApart _ (by simp)
        · exact (h.layout.negApart K.zero (by simp)).symm
        · exact .inl low) (by omega),zero]
    · intro j hj
      rw [ou.byte (fun w hw => .inr (by have := h.layout.bounded w hw; have := h.bitsLow; omega))
        (by have := h.bitsHigh; omega),bits j hj]
    · exact cp.2.2.2.1.trans coeffA
    · exact cp.2.2.2.2.trans coeffB
  have au : Acc K C base k K.J u := by
    refine ⟨?_,?_⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
      rw [xu,yu,zu]
      exact ⟨sx,sy,h.one_lt⟩
    · show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
      rw [xu,yu,zu,h.startX,h.startY,toM_mont h.unit,toM_mont h.unit,h.one,combEW_top,h.tables.start]
      exact rep_affine' hC _ _
  let Inv := fun j t => CurveInputs K C tbl base T k t ∧ Acc K C base k j t ∧
    t.gpr .r11=BitVec.ofNat 32 j ∧ Rest powClob s t ∧ Unch base (writes K) s.mem t.mem
  apply countLoop_ok (Inv := Inv)
    (fun j t hj hJ hi => ?_) (fun t hi => ?_) h.J1
    ⟨iu,au,gu,ku.mono (by simp [powClob,VG.Proof.Mont.Arm.clob]),ou⟩
  · obtain ⟨it,accT,gt,kt,ot⟩ := hi
    refine WP.mono (step_ok K h hC hG it accT hj hJ hk gt hd) fun v ⟨kv,ov,iv,av,gv,zv⟩ => ?_
    refine ⟨⟨iv,av,gv,kt.trans kv,?_⟩,zv⟩
    exact (ot.trans (ov.cover h.layout.loop_cover)).cover fun w hw => ⟨w,by
      simpa only [List.mem_append,or_self] using hw,Nat.le_refl _,Nat.le_refl _⟩
  · obtain ⟨_,accT,_,kt,ot⟩ := hi
    refine ⟨kt,ot,accT.lt,?_⟩
    have hk' : k<2^(K.w*K.J) := Nat.lt_of_lt_of_le hk (Nat.pow_le_pow_right (by decide) h.coverBits)
    simpa only [combEW_zero hk'] using accT.rep

end VG.Proof.Weierstrass.Arm.TComb
