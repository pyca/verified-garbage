import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Joint
import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedInit
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointInvariant

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64.P256Joint
open Spec.Weierstrass

private theorem cache_sources : ∀ x∈CachedInit.sources,x∈nafLive cfg.K := by decide +kernel
private theorem cache_slots : ∀ op∈CachedInit.ops,∀ x∈op.out::op.ins,x∈jointSlots cfg := by decide +kernel
private theorem live_bounds : ∀ x∈nafLive cfg.K,x<6000 := by decide +kernel
private theorem cache_zero : ∀ w∈CachedInit.outputs.map (·,32)++[(128,32)],160+32≤w.1 ∨ w.1+w.2≤160 := by decide +kernel
private theorem cache_bits : ∀ w∈CachedInit.outputs.map (·,32)++[(128,32)],2088≤w.1 ∨ w.1+w.2≤1504 := by decide +kernel

/-- Initialize cached powers, leaving the original table and both scalar buffers intact. -/
theorem jointCache_ok {C : Curve} {base : Addr} {size u v : Nat} {Q : Point C} {s : State}
    (hL : JointLayout cfg size) (hm : UnitMod C.p (2^(64*cfg.K.M.n)))
    (hI : Inv cfg.K.M base size C.p (·∈jointSlots cfg) (nafLive cfg.K)
      (tmv C cfg.K.M.n base s) s)
    (hp : NafStable cfg.K C base Q (FastNaf.byte 5 v) s)
    (hg : ∀ j<257,s.mem (off base (cfg.gBits+j))=FastNaf.byte 7 u j)
    (hone : tmv C cfg.K.M.n base s cfg.onep=1) :
    WP isa (CachedJac.cache cfg.K) s fun t =>
      ProgKeep cfg.K.M base CachedInit.outputs s t ∧
      Inv cfg.K.M base size C.p (·∈jointSlots cfg) (jointLive cfg) (tmv C cfg.K.M.n base t) t ∧
      JointStable cfg C base Q u v t := by
  refine WP.mono (CachedInit.cache_ok hL.lay hL.aligned hm hI cache_slots cache_sources)
    fun t ⟨kt,it⟩ => ?_
  have ni : Inv cfg.K.M base size C.p (·∈jointSlots cfg) (jointLive cfg)
      (runOps CachedInit.ops (tmv C cfg.K.M.n base s)) t := it.sub (by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_right _ hx
    · exact List.mem_append_left _ hx)
  have same (x : Nat) (hx : x∈nafLive cfg.K) :
      tmv C cfg.K.M.n base t x=tmv C cfg.K.M.n base s x := by
    have e := it.val x (List.mem_append_right _ hx)
    change tmv C cfg.K.M.n base t x=_ at e
    rw [CachedInit.unchanged _ (live_bounds x hx)] at e
    exact e
  have ht (a : Nat) (ha : 1≤a) (ha8 : a≤8) (x : Nat)
      (hx : x∈[(Jacobian.tablePt cfg.K a).x,(Jacobian.tablePt cfg.K a).y,(Jacobian.tablePt cfg.K a).z]) :
      x∈nafLive cfg.K := by
    apply List.mem_append_right
    simp only [Jacobian.tablePt,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact List.mem_map.mpr ⟨3*(a-1),List.mem_range.mpr (by omega),by omega⟩
    · exact List.mem_map.mpr ⟨3*(a-1)+1,List.mem_range.mpr (by omega),by omega⟩
    · exact List.mem_map.mpr ⟨3*(a-1)+2,List.mem_range.mpr (by omega),by omega⟩
  have bytes (d : Nat) (hd : d=cfg.K.bits ∨ d=cfg.gBits) (j : Nat) (hj : j<257) :
      t.mem (off base (d+j))=s.mem (off base (d+j)) := by
    apply kt.unch.byte
    · intro w hw
      have hb := cache_bits w hw
      rcases hd with rfl | rfl
      · change 1824+j<w.1 ∨ w.1+w.2≤1824+j
        omega
      · change 1504+j<w.1 ∨ w.1+w.2≤1504+j
        omega
    · rcases hd with rfl | rfl
      · change 1824+j<2^64; omega
      · change 1504+j<2^64; omega
  refine ⟨kt,ni.to_tmv,⟨⟨?_,?_,?_⟩,?_,?_,?_,?_⟩⟩
  · change wordsVal t.mem base 160 4=0
    rw [kt.unch.wordsVal (d:=160) (k:=4) cache_zero (by decide)]
    exact hp.zero
  · intro a ha ha8
    rw [same _ (ht a ha ha8 _ (by simp)),same _ (ht a ha ha8 _ (by simp)),same _ (ht a ha ha8 _ (by simp))]
    exact hp.table a ha ha8
  · intro j hj; rw [bytes _ (Or.inl rfl) j hj]; exact hp.bits j hj
  · intro j hj; rw [bytes _ (Or.inr rfl) j hj]; exact hg j hj
  · rw [same _ (by decide +kernel),hone]
  · intro i hi
    have p := CachedInit.pow_values (tmv C cfg.K.M.n base s) i hi
    have h2 : 6000+64*i∈CachedInit.outputs := List.mem_map.mpr ⟨2*i,List.mem_range.mpr (by omega),by omega⟩
    have hz := ht (i+1) (by omega) (by omega) _ (by simp : (Jacobian.tablePt cfg.K (i+1)).z∈[_,_,_])
    have e2 := it.val _ (List.mem_append_left _ h2)
    have ez := it.val _ (List.mem_append_right _ hz)
    change tmv C cfg.K.M.n base t (6000+64*i)=_ at e2
    have tz : (Jacobian.tablePt cfg.K (i+1)).z=2912+96*i := by
      change 2848+96*(i+1-1)+64=2912+96*i
      omega
    rw [tz] at ez
    change tmv C cfg.K.M.n base t (2912+96*i)=_ at ez
    change tmv C cfg.K.M.n base t (6000+64*i)=tmv C cfg.K.M.n base t (Jacobian.tablePt cfg.K (i+1)).z*tmv C cfg.K.M.n base t (Jacobian.tablePt cfg.K (i+1)).z
    rw [tz]
    rw [e2,ez]; exact p.1
  · intro i hi
    have p := CachedInit.pow_values (tmv C cfg.K.M.n base s) i hi
    have h2 : 6000+64*i∈CachedInit.outputs := List.mem_map.mpr ⟨2*i,List.mem_range.mpr (by omega),by omega⟩
    have h3 : 6032+64*i∈CachedInit.outputs := List.mem_map.mpr ⟨2*i+1,List.mem_range.mpr (by omega),by omega⟩
    have hz := ht (i+1) (by omega) (by omega) _ (by simp : (Jacobian.tablePt cfg.K (i+1)).z∈[_,_,_])
    have e2 := it.val _ (List.mem_append_left _ h2)
    have e3 := it.val _ (List.mem_append_left _ h3)
    have ez := it.val _ (List.mem_append_right _ hz)
    change tmv C cfg.K.M.n base t (6000+64*i)=_ at e2
    change tmv C cfg.K.M.n base t (6032+64*i)=_ at e3
    have tz : (Jacobian.tablePt cfg.K (i+1)).z=2912+96*i := by
      change 2848+96*(i+1-1)+64=2912+96*i
      omega
    rw [tz] at ez
    change tmv C cfg.K.M.n base t (2912+96*i)=_ at ez
    change tmv C cfg.K.M.n base t (6032+64*i)=tmv C cfg.K.M.n base t (6000+64*i)*tmv C cfg.K.M.n base t (Jacobian.tablePt cfg.K (i+1)).z
    rw [tz]
    rw [e3,e2,ez]; exact p.2

end VG.Proof.Ecdsa.Verify.AArch64
