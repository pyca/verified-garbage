module

public import VerifiedGarbage.Proof.Weierstrass.Arm.TCombConfig
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombDigit
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombSelectTable
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombSign
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombNegate
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Weierstrass.Arm.Saves
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Weierstrass.CombPointW

/-! Decode, select, and reflect one table entry while keeping the accumulator. -/

@[expose] public section
namespace VG.Proof.Weierstrass.Arm.TComb
open VG VG.Arm VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass.Arm.Point
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.X25519.Arm
open VG.Proof.Weierstrass.Arm.Point
open Spec.Weierstrass

theorem entry_ok (K : TCombCfg) {C : Curve} {tbl : List (List (Nat × Nat))} {start : Nat × Nat}
    (h : Config K C tbl start) (hC : Law C) {s : State} {base T : Addr} {k j : Nat}
    (i : CurveInputs K C tbl base T k s) (hj : j<K.J) (hk : k<2^K.L.nbits)
    (gj : s.gpr .r11=BitVec.ofNat 32 j)
    (hd : Region.Disjoint ⟨T,8*(tableWords K C tbl).length⟩ ⟨base,4096⟩) :
    WP isa K.entry s fun t =>
      Rest VG.Proof.Weierstrass.Arm.Mont.callClob s t ∧ Unch base (loopWrites K) s.mem t.mem ∧
      (∀ x ∈ [K.L.R.x,K.L.R.y,K.L.R.z],wordsVal t.mem base x K.L.M.n=wordsVal s.mem base x K.L.M.n) ∧
      (∀ x ∈ [K.Q.x,K.Q.y,K.Q.z],wordsVal t.mem base x K.L.M.n<C.p) ∧
      Rep C (tmv C K.L.M.n base t K.Q.x) (tmv C K.L.M.n base t K.Q.y)
        (tmv C K.L.M.n base t K.Q.z) (signedPtW C K.w k j) := by
  unfold TCombCfg.entry
  have hp : 0<C.p := Nat.pos_of_ne_zero (NeZero.ne C.p)
  have hfit : C.p≤2^(64*K.L.M.n) := Nat.le_of_lt h.modulus.m_lt
  have lo := h.layout.low
  have hl := lay_nums h.layout.n3 h.layout.n6
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq] at lo
  obtain ⟨rx,ry,rz,zlo,nlo⟩ := lo
  refine WP.seq (WP.mono_syms (digit_ok K i.scr i.far h.w9 hj (by have := h.J32; omega)
    h.encLast h.startBits h.coverBits h.bitsFit h.windowFit h.bitsHigh hk gj i.bits)
    fun u ⟨gu,ku⟩ syu => ?_)
  have iu : CurveInputs K C tbl base T k u := i.keep h.layout h.bitsLow h.bitsHigh hd ku.keep
    (by decide) (by rw [ku.mem]; exact Unch.refl _ _ _) syu
  refine WP.seq (WP.mono_syms (selectTable_ok K iu.scr
    (by simp only [TCombCfg.Q,ptAt]; omega) (by omega)
    (.inl (Nat.le_trans zlo (oAt_le_qAt _))) (Nat.lt_of_lt_of_le h.one_lt hfit) iu.zero
    (by have := h.layout.n3; omega) h.halfBound (h.magnitude k j) gu
    (by rw [ku.keep.gpr .r11 (by decide),gj]) iu.table iu.symbol h.tables.len h.tables.lenH hj hp hfit hd
    h.encRow h.encEntry h.encH) fun v ⟨xv,yv,zv,kv,ov⟩ syv => ?_)
  have ouv := ov.unch.cover h.layout.q_cover
  have iv : CurveInputs K C tbl base T k v := iu.keep h.layout h.bitsLow h.bitsHigh hd kv
    (by decide) ouv syv
  have ylt : wordsVal v.mem base K.Q.y K.L.M.n<C.p := by rw [yv]; split <;> first | exact h.one_lt | exact Nat.mod_lt _ hp
  have oldR : ∀ x ∈ [K.L.R.x,K.L.R.y,K.L.R.z],wordsVal v.mem base x K.L.M.n=wordsVal s.mem base x K.L.M.n := by
    intro x hx
    have lowx := h.layout.low x (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl <;> simp)
    rw [ov.wordsVal (.inl (Nat.le_trans lowx (oAt_le_qAt _))) (by have := i.scr.nowrap; omega),ku.mem]
  have mask : ∀ a, Rest VG.Proof.Weierstrass.Arm.Mont.callClob v a →
      Unch base [(K.neg,8*K.L.M.n),(VG.Impl.Weierstrass.Arm.Mont.own K.L.M.n,64*K.L.M.n)] v.mem a.mem →
      WP isa K.signMask a fun b =>
        b.gpr .r10=(if K.H≤combWin K.w k j then 0 else BitVec.allOnes 32) ∧ RegOnly [.r4,.r10] a b := by
    intro a keep mem
    apply signMask_ok K (iv.scr.of_rest keep (by decide)) (iv.far.of_rest keep)
      ⟨h.w1,h.w9⟩ hj (by have := h.J32; omega) h.encLast h.startBits h.coverBits h.bitsFit
      h.windowFit h.bitsHigh hk
      (by rw [keep.gpr .r11 (by decide),kv.gpr .r11 (by decide),ku.keep.gpr .r11 (by decide),gj])
    intro b hb
    have mem' := (mem.cover h.layout.sub_cover).cover h.layout.loop_cover
    rw [mem'.byte (fun w hw => .inr (by have := h.layout.bounded w hw; have := h.bitsLow; omega))
      (by have := h.bitsHigh; omega),iv.bits b hb]
  refine WP.mono (negate_ok K (K.H≤combWin K.w k j) h.layout iv.scr iv.far
    h.fieldM h.fieldK h.modulus iv.zero ylt mask) fun t ⟨kt,ot,rt,xt,yt,zt⟩ => ?_
  have ku' : Rest VG.Proof.Weierstrass.Arm.Mont.callClob s u := ku.keep.mono (by
    simp [VG.Proof.Weierstrass.Arm.Mont.callClob,VG.Proof.Mont.Arm.clob])
  have kv' : Rest VG.Proof.Weierstrass.Arm.Mont.callClob u v := kv.mono (by
    simp [VG.Proof.Weierstrass.Arm.Mont.callClob,VG.Proof.Mont.Arm.clob])
  refine ⟨ku'.trans (kv'.trans kt),?_,fun x hx => (rt x hx).trans (oldR x hx),?_,?_⟩
  · have ou : Unch base (loopWrites K) s.mem u.mem := by rw [ku.mem]; exact Unch.refl _ _ _
    exact (ou.trans (ouv.trans ot)).cover fun w hw => ⟨w,by
      simpa only [List.mem_append,or_self] using hw,Nat.le_refl _,Nat.le_refl _⟩
  · simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
    rw [xt,yt,zt,xv,zv]
    refine ⟨?_,?_,?_⟩
    · split <;> first | exact hp | exact Nat.mod_lt _ hp
    · split <;> first | exact ylt | exact Nat.mod_lt _ hp
    · split <;> first | exact hp | exact h.one_lt
  · show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
    rw [xt,yt,zt]
    exact combSigned_rep hC h.tables h.unit h.one hj h.w1 xv yv zv ylt

end VG.Proof.Weierstrass.Arm.TComb
