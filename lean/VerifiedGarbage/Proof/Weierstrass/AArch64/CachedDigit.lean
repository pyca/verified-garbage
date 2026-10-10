import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedEntry
import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedAddTiming
import VerifiedGarbage.Proof.Framework.AArch64.Syms

namespace VG.Proof.Weierstrass.AArch64.CachedField
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

theorem magnitude_byte (w v j : Nat) : nafMagnitude (FastNaf.byte w v j)=FastNaf.magnitude w v j :=
  FastNaf.byte_magnitude w v j

theorem negative_byte (w v j : Nat) : nafNegative (FastNaf.byte w v j)=FastNaf.negative w v j :=
  FastNaf.byte_negative w v j

/-- Stable external generator data is framed by work writes and unchanged symbols. -/
def ExternalFrame (base : Addr) (External : State → Prop) : Prop :=
  ∀ {s t},ProgKeep K.M base (jointWork cfg) s t → t.syms=s.syms → External s → External t

theorem entry_core_ok {C : Curve} {base : Addr} {size u v j : Nat}
    (hL : JointLayout cfg size) (hsize : 6512≤size)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hj : j<257)
    (hmag : 1≤nafMagnitude (FastNaf.byte 5 v j)) (hmag15 : nafMagnitude (FastNaf.byte 5 v j)≤15)
    (hodd : nafMagnitude (FastNaf.byte 5 v j)%2=1)
    {Q A : Point C} {External : State → Prop} (hExt : ExternalFrame base External) {s : State}
    (h : JointCore cfg C base size Q u v External A s)
    (h19 : s.gpr .x19=BitVec.ofNat 64 j) (h2 : s.gpr .x2=(FastNaf.byte 5 v j).setWidth 64) :
    WP isa (CachedJac.entry K) s fun t =>
      EntryPost C base size (FastNaf.point C Q 5 v j) (jointLive cfg) s t ∧
      JointCore cfg C base size Q u v External A t := by
  refine WP.mono_syms (entry_ok hL hsize hm hj hmag hmag15 hodd h.field h.stable h19 h2)
    fun t hp sy => ?_
  have pointEq : (if nafNegative (FastNaf.byte 5 v j) then negPt (mul (nafMagnitude (FastNaf.byte 5 v j)) Q)
      else mul (nafMagnitude (FastNaf.byte 5 v j)) Q)=FastNaf.point C Q 5 v j := by
    rw [negative_byte,magnitude_byte]; rfl
  rw [pointEq] at hp
  refine ⟨hp,h.of_write (E:=tmv C K.M.n base t) hL hp.1 entry_work entry_slots (by decide +kernel) ?_
    (hExt (hp.1.mono entry_work) sy h.external)⟩
  exact hp.2.1.sub (fun _ hx => List.mem_append_right _ (List.mem_append_right _ hx))

theorem sum_ok {C : Curve} {base : Addr} {size u v : Nat}
    (hL : JointLayout cfg size) (hsize : 8192≤size)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hOne : K.one<C.p)
    {Q A B : Point C} (hA : onCurve C A=true) (hB : onCurve C B=true)
    {External : State → Prop} (hExt : ExternalFrame base External) {s : State}
    (h : JointCore cfg C base size Q u v External A s)
    (hi : Inv K.M base size C.p (·∈jointSlots cfg) (entryLive (jointLive cfg)) (tmv C K.M.n base s) s)
    (hj : InvJ C (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) (tmv C K.M.n base s K.E.z) B)
    (h2 : tmv C K.M.n base s 5400=tmv C K.M.n base s K.E.z*tmv C K.M.n base s K.E.z)
    (h3 : tmv C K.M.n base s 5432=tmv C K.M.n base s K.E.z*(tmv C K.M.n base s K.E.z*tmv C K.M.n base s K.E.z)) :
    WP isa (.seq (CachedJac.add K ops) (.block (copyPt 4 K.R K.D))) s fun t =>
      ProgKeep K.M base (jointWork cfg) s t ∧ JointCore cfg C base size Q u v External (add A B) t := by
  apply WP.of_syms
  apply WP.seq
  refine WP.mono (add_ok hL.lay hL.aligned (callOf_small (Nat.le_of_eq hL.n)) hm hsize hC ha (by decide +kernel)
    hi (by decide +kernel) h2 h3 hOne hA hB h.point hj) fun b ⟨eb,kb,ib,jb⟩ => ?_
  have apart : RcbApart K.S K.D K.D K.R := ⟨by decide +kernel,by decide +kernel⟩
  refine WP.mono (copyPoint_ok hL.lay hL.aligned apart (by decide +kernel) ib
    (by decide +kernel)) fun t ⟨et,kt,it,hv⟩ sy => ?_
  have kp : ProgKeep K.M base (jointWork cfg) s t :=
    (kb.mono (by decide +kernel)).trans (kt.mono (by decide +kernel))
  refine ⟨kp,h.next hL kp (it.sub (fun _ hx => List.mem_append_right _
    (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ hx))))) ?_
    (hExt kp sy h.external)⟩
  simp only [Prod.mk.injEq] at hv
  rw [cfg_K,hv.1,hv.2.1,hv.2.2]
  exact jb

private theorem byteTest : ∀ b : BitVec 8,(b.setWidth 64 != 0)=decide (nafMagnitude b≠0) := by decide +kernel

theorem digit_ok {C : Curve} {base : Addr} {size u v j : Nat}
    (hL : JointLayout cfg size) (hsize : 8192≤size)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hOne : K.one<C.p)
    (hj : j<257) {Q A : Point C} (hQ : onCurve C Q=true) (hA : onCurve C A=true)
    {External : State → Prop} (hExt : ExternalFrame base External) {s : State}
    (h : JointCore cfg C base size Q u v External A s) (h19 : s.gpr .x19=BitVec.ofNat 64 j) :
    WP isa (CachedJac.digit K ops) s fun t =>
      ProgKeep K.M base (jointWork cfg) s t ∧
      JointCore cfg C base size Q u v External (add A (FastNaf.point C Q 5 v j)) t := by
  rw [CachedJac.digit]
  apply WP.seq
  refine WP.mono_syms (nafRead_ok h.field.scr (by decide) (by change 1824+j<size; omega) h19
    (h.stable.peer.bits j hj) .x2) fun b ⟨b2,kb⟩ sy => ?_
  have kp : ProgKeep K.M base (jointWork cfg) s b := keeps_prog kb (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> simp [clob])
  have cb := h.of_keeps kb (by decide) (hExt kp sy h.external)
  have b19 : b.gpr .x19=BitVec.ofNat 64 j := (kb.gpr _ (by decide)).trans h19
  refine WP.ite (decide (FastNaf.magnitude 5 v j≠0)) (by
    change some (b.read .x .x2 != 0)=_
    rw [read_x,b2,byteTest,magnitude_byte]) (fun hn => ?_) (fun hz => ?_)
  · have hm0 : FastNaf.magnitude 5 v j≠0 := of_decide_eq_true hn
    apply WP.seq
    refine WP.mono (entry_core_ok hL (by omega) hm hj
      (by rw [magnitude_byte]; omega)
      (by rw [magnitude_byte]; exact FastNaf.magnitude_le (Or.inl rfl) v j)
      (by rw [magnitude_byte]; exact (FastNaf.magnitude_odd_or_zero 5 v j).resolve_left hm0)
      hExt cb b19 b2) fun d ⟨⟨kd,id,jd,d2,d3⟩,cd⟩ => ?_
    exact WP.mono (sum_ok hL hsize hm hC ha hOne hA (FastNaf.onCurve_point hC hQ 5 v j)
      hExt cd id jd d2 d3) fun t ⟨kt,ct⟩ => ⟨kp.trans ((kd.mono entry_work).trans kt),ct⟩
  · have hm0 : FastNaf.magnitude 5 v j=0 := by simpa only [ne_eq,not_not] using of_decide_eq_false hz
    have hp : FastNaf.point C Q 5 v j=.infinity := by
      unfold FastNaf.point
      rw [hm0,Spec.Weierstrass.mul]
      cases FastNaf.negative 5 v j <;> rfl
    have he : add A (FastNaf.point C Q 5 v j)=A := by rw [hp]; cases A <;> rfl
    apply WP.block_nil
    exact ⟨kp,he.symm ▸ cb⟩

end VG.Proof.Weierstrass.AArch64.CachedField
