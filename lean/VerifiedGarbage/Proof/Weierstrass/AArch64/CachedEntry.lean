import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Joint
import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedEntryLoad
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointInvariant
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafEntry

namespace VG.Proof.Weierstrass.AArch64.CachedField
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

abbrev cfg := VG.Impl.Ecdsa.Verify.AArch64.P256Joint.cfg

theorem cfg_K : cfg.K=K := rfl

theorem entry_work : ∀ x∈entryWrites,x∈jointWork cfg := by decide +kernel
theorem entry_slots : ∀ x∈entryWrites,x∈jointSlots cfg := by decide +kernel

theorem entrySources_live {a : Nat} (ha : 1≤a) (ha8 : a≤8) : ∀ x∈[(Jacobian.tablePt K a).x,(Jacobian.tablePt K a).y,(Jacobian.tablePt K a).z,
      6000+64*(a-1),6032+64*(a-1)],x∈jointLive cfg := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · apply List.mem_append_left; apply List.mem_append_right
      exact List.mem_map.mpr ⟨3*(a-1),List.mem_range.mpr (by omega),by simp only [Jacobian.tablePt,cfg_K]; omega⟩
    · apply List.mem_append_left; apply List.mem_append_right
      exact List.mem_map.mpr ⟨3*(a-1)+1,List.mem_range.mpr (by omega),by simp only [Jacobian.tablePt,cfg_K]; omega⟩
    · apply List.mem_append_left; apply List.mem_append_right
      exact List.mem_map.mpr ⟨3*(a-1)+2,List.mem_range.mpr (by omega),by simp only [Jacobian.tablePt,cfg_K]; omega⟩
    · apply List.mem_append_right
      exact List.mem_map.mpr ⟨2*(a-1),List.mem_range.mpr (by omega),by omega⟩
    · apply List.mem_append_right
      exact List.mem_map.mpr ⟨2*(a-1)+1,List.mem_range.mpr (by omega),by omega⟩

def EntryPost (C : Curve) (base : Addr) (size : Nat) (P : Point C)
    (V : List Nat) (s t : State) : Prop :=
  ProgKeep K.M base entryWrites s t ∧
  Inv K.M base size C.p (·∈jointSlots cfg) (entryLive V) (tmv C K.M.n base t) t ∧
  InvJ C (tmv C K.M.n base t K.E.x) (tmv C K.M.n base t K.E.y) (tmv C K.M.n base t K.E.z) P ∧
  tmv C K.M.n base t 5400=tmv C K.M.n base t K.E.z*tmv C K.M.n base t K.E.z ∧
  tmv C K.M.n base t 5432=tmv C K.M.n base t K.E.z*(tmv C K.M.n base t K.E.z*tmv C K.M.n base t K.E.z)

theorem entry_ok {C : Curve} {base : Addr} {size u v j : Nat}
    (hL : JointLayout cfg size) (hsize : 6512≤size)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hj : j<257)
    (hmag : 1≤nafMagnitude (FastNaf.byte 5 v j)) (hmag15 : nafMagnitude (FastNaf.byte 5 v j)≤15)
    (hodd : nafMagnitude (FastNaf.byte 5 v j)%2=1)
    {Q : Point C} {s : State}
    (hi : Inv K.M base size C.p (·∈jointSlots cfg) (jointLive cfg) (tmv C K.M.n base s) s)
    (hs : JointStable cfg C base Q u v s)
    (h19 : s.gpr .x19=BitVec.ofNat 64 j) (h2 : s.gpr .x2=(FastNaf.byte 5 v j).setWidth 64) :
    WP isa (CachedJac.entry K) s
      (EntryPost C base size (if nafNegative (FastNaf.byte 5 v j) then
        negPt (mul (nafMagnitude (FastNaf.byte 5 v j)) Q) else mul (nafMagnitude (FastNaf.byte 5 v j)) Q)
        (jointLive cfg) s) := by
  let a := (nafMagnitude (FastNaf.byte 5 v j)+1)/2
  have ha : 1≤a := by dsimp [a]; omega
  have ha8 : a≤8 := by dsimp [a]; omega
  have he : 2*a-1=nafMagnitude (FastNaf.byte 5 v j) := by dsimp [a]; omega
  have ht := entrySources_live ha ha8
  rw [CachedJac.entry]
  apply WP.seq
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (nafIndex_ok h2) fun b ⟨b2,kb⟩ => ?_
  have eb : tmv C K.M.n base b=tmv C K.M.n base s := by funext x; unfold tmv; rw [kb.mem]
  have ib := hi.of_keeps kb (by decide)
  rw [←eb] at ib
  have sb := hs.of_mem kb.mem
  have kb' : ProgKeep K.M base entryWrites s b := keeps_prog kb (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [clob])
  have cb2 : tmv C K.M.n base b (6000+64*(a-1))=
      tmv C K.M.n base b (Jacobian.tablePt K a).z*tmv C K.M.n base b (Jacobian.tablePt K a).z := by
    simpa only [cfg_K,VG.Impl.Weierstrass.CachedJac.tableZ2,Nat.sub_add_cancel ha] using sb.cache2 (a-1) (by omega)
  have cb3 : tmv C K.M.n base b (6032+64*(a-1))=
      tmv C K.M.n base b (Jacobian.tablePt K a).z*(tmv C K.M.n base b (Jacobian.tablePt K a).z*tmv C K.M.n base b (Jacobian.tablePt K a).z) := by
    have h := sb.cache3 (a-1) (by omega)
    simp only [cfg_K,VG.Impl.Weierstrass.CachedJac.tableZ2,VG.Impl.Weierstrass.CachedJac.tableZ3,Nat.sub_add_cancel ha] at h
    rw [h,cb2]; grind
  refine WP.mono (entryLoad_ok hL.lay hL.aligned hsize ib b2 ha ha8 entry_slots ht cb2 cb3
    (sb.peer.table a ha ha8)) fun d ⟨kd,id,jd,d2,d3⟩ => ?_
  rw [he] at jd
  have kp := kb'.trans kd
  have sd := hs.keep (kp.mono entry_work) (fun r hr => by
    have := hL.stableBounds r hr; have := hi.scr.nowrap; omega) hL.stableSep
  have d19 : d.gpr .x19=BitVec.ofNat 64 j := by
    rw [kp.gpr _ (by decide),h19]
  apply WP.seq
  refine WP.mono (nafSignRead_ok id.scr (by decide) (by change 1824+j<size; omega) d19
    (sd.peer.bits j hj)) fun e ⟨e3,ke⟩ => ?_
  have ee : tmv C K.M.n base e=tmv C K.M.n base d := by funext x; unfold tmv; rw [ke.mem]
  have ie := id.of_keeps ke (by decide)
  rw [←ee] at ie jd d2 d3
  have se := sd.of_mem ke.mem
  have kpe : ProgKeep K.M base entryWrites s e := kp.trans (keeps_prog ke (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> simp [clob]))
  refine WP.ite (nafNegative (FastNaf.byte 5 v j)) (by
    change some (e.read .x .x3 != 0)=some _
    rw [read_x,e3]; cases nafNegative (FastNaf.byte 5 v j) <;> decide) (fun hn => ?_) (fun hn => ?_)
  · have hz : tmv C K.M.n base e K.zero=0 := by
      have hz := se.peer.zero
      rw [cfg_K] at hz
      unfold tmv; rw [hz,toM_zero]
    have ev : ∀ x∈[K.E.x,K.E.y,K.E.z,K.zero],x∈entryLive (jointLive cfg) := by decide +kernel
    refine WP.mono (nafNeg_ok (K:=K) hL.lay hL.aligned hm ie ev (by decide) (by decide) hz jd)
      fun t ⟨kt,it,jt⟩ => ?_
    have vy := it.val
    have same (x : Nat) (hx : x∈entryLive (jointLive cfg)) (hn : x≠K.E.y) :
        tmv C K.M.n base t x=tmv C K.M.n base e x := by
      exact (vy x hx).trans (Function.update_of_ne hn _ _)
    refine ⟨kpe.trans (kt.mono (by simp [entryWrites])),it.to_tmv,?_,?_,?_⟩
    · rw [hn]; exact it.point_tmv (fun x hx => by
        simp only [entryLive,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind) jt
    · rw [same 5400 (by decide) (by decide),same K.E.z (by decide) (by decide)]; exact d2
    · rw [same 5432 (by decide) (by decide),same K.E.z (by decide) (by decide)]; exact d3
  · apply WP.block_nil
    refine ⟨kpe,ie,?_,d2,d3⟩
    rw [hn]; exact jd

end VG.Proof.Weierstrass.AArch64.CachedField
