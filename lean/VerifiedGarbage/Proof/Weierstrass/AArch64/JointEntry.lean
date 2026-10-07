import VerifiedGarbage.Proof.Weierstrass.AArch64.JointLoad
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeArithmetic
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowState
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafNeg
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafDigitRead

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass

/-- The generator row is consumed directly as canonical Montgomery coordinates. -/
theorem jointFixedPoint_ok (c : Joint.Cfg) {s : State} {base T : Addr} {size a : Nat} {C : Curve}
    {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fe C}
    (hL : Lay c.K.M size Sl) (hAl : Aligned c.K.M Sl) (hn : c.K.M.n=4)
    (hi : Inv c.K.M base size C.p Sl V E s)
    (ha : 1≤a) (h2 : s.gpr .x2=BitVec.ofNat 64 a) (ht : s.syms c.tsym=T)
    (hy : c.K.E.y=c.K.E.x+32)
    (hD : ∀ x∈[c.K.E.x,c.K.E.y,c.K.E.z],Sl x)
    (hdz : c.K.E.x≠c.K.E.z) (hyz : c.K.E.y≠c.K.E.z)
    (hx1 : c.K.E.x≠c.onep) (hy1 : c.K.E.y≠c.onep)
    (hOne : c.onep∈V) (hOneVal : E c.onep=1)
    (hr : ∀ i<8, InRegions (s.rd++s.wr)
      (T+BitVec.ofNat 64 (128*(a-1))+BitVec.ofNat 64 (8*i)) 8)
    (hout : ∀ i<8, ∀ b<8, size≤ofs base
      (T+BitVec.ofNat 64 (128*(a-1))+BitVec.ofNat 64 (8*i)+BitVec.ofNat 64 b))
    (hxy : wordsVal s.mem (T+BitVec.ofNat 64 (128*(a-1))) 0 4<C.p ∧
      wordsVal s.mem (T+BitVec.ofNat 64 (128*(a-1))) 32 4<C.p)
    {P : Point C} (hJ : InvJ C
      (toM C.p (2^256) (wordsVal s.mem (T+BitVec.ofNat 64 (128*(a-1))) 0 4))
      (toM C.p (2^256) (wordsVal s.mem (T+BitVec.ofNat 64 (128*(a-1))) 32 4)) 1 P) :
    WP isa (.block (Joint.fixedLoad c)) s fun t =>
      ProgKeep c.K.M base [c.K.E.x,c.K.E.y,c.K.E.z] s t ∧
      Inv c.K.M base size C.p Sl ([c.K.E.x,c.K.E.y,c.K.E.z]++V) (tmv C c.K.M.n base t) t ∧
      InvJ C (tmv C c.K.M.n base t c.K.E.x) (tmv C c.K.M.n base t c.K.E.y)
        (tmv C c.K.M.n base t c.K.E.z) P ∧ tmv C c.K.M.n base t c.K.E.z=1 := by
  have bx := hL.le _ (hD c.K.E.x (by simp))
  have by' := hL.le _ (hD c.K.E.y (by simp))
  have bz := hL.le _ (hD c.K.E.z (by simp))
  have b1 := hL.le _ (hi.sl _ hOne)
  have sxz := hL.apart _ _ (hD c.K.E.x (by simp)) (hD c.K.E.z (by simp)) hdz
  have syz := hL.apart _ _ (hD c.K.E.y (by simp)) (hD c.K.E.z (by simp)) hyz
  have sx1 := hL.apart _ _ (hD c.K.E.x (by simp)) (hi.sl _ hOne) hx1
  have sy1 := hL.apart _ _ (hD c.K.E.y (by simp)) (hi.sl _ hOne) hy1
  have sz1 : c.K.E.z≤c.onep ∨ c.onep+32≤c.K.E.z := by
    by_cases e : c.K.E.z=c.onep
    · omega
    · have := hL.apart _ _ (hD c.K.E.z (by simp)) (hi.sl _ hOne) e
      rw [hn] at this; omega
  simp only [hn,hy] at bx by' bz b1 sxz syz sx1 sy1
  refine WP.mono (jointFixedLoad_ok c hi.scr ha h2 ht hy (by omega)
    (hAl.sl _ (hD c.K.E.x (by simp))) bz (hAl.sl _ (hD c.K.E.z (by simp)))
    b1 (hAl.sl _ (hi.sl _ hOne)) (by omega) (by omega) sz1 hr hout)
    fun t ⟨vx,vy,vz,kt,ut⟩ => ?_
  have kp : ProgKeep c.K.M base [c.K.E.x,c.K.E.y,c.K.E.z] s t := by
    refine ⟨fun r hr => kt.gpr r (fun hh => hr ?_),kt.rd,kt.wr,kt.sp,fun x hx _ => ut x ?_⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
      rcases hh with rfl | rfl | rfl | rfl <;> simp [clob]
    · intro w hw
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      have hx0 := hx c.K.E.x (by simp)
      have hx1 := hx c.K.E.y (by simp)
      have hx2 := hx c.K.E.z (by simp)
      rw [hn] at hx0 hx1 hx2
      rw [hy] at hx1
      rcases hw with rfl | rfl <;> dsimp only <;> omega
  have hlt : ∀ x∈[c.K.E.x,c.K.E.y,c.K.E.z],wordsVal t.mem base x c.K.M.n<C.p := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rw [hn]
    rcases hx with rfl | rfl | rfl
    · rw [vx]; exact hxy.1
    · rw [vy]; exact hxy.2
    · rw [vz,←hn]; exact hi.lt _ hOne
  have zz : tmv C c.K.M.n base t c.K.E.z=1 := by
    unfold tmv
    rw [hn,vz,←hn,hi.val _ hOne,hOneVal]
  refine ⟨kp,hi.of_progKeep hL kp hD hlt,?_,zz⟩
  rw [zz]
  unfold tmv
  rw [hn,vx,vy]
  exact hJ

theorem jointSignEntry_ok (c : Joint.Cfg) {s : State} {base : Addr} {size j : Nat} {C : Curve}
    {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fe C} {b : BitVec 8}
    (hL : Lay c.K.M size Sl) (hAl : Aligned c.K.M Sl)
    (hm : UnitMod C.p (2^(64*c.K.M.n))) (hi : Inv c.K.M base size C.p Sl V E s)
    (hV : ∀ x∈[c.K.E.x,c.K.E.y,c.K.E.z,c.K.zero],x∈V)
    (hxy : c.K.E.x≠c.K.E.y) (hzy : c.K.E.z≠c.K.E.y) (hzero : E c.K.zero=0)
    (hBits : c.gBits<4096) (hj : c.gBits+j<size)
    (h19 : s.gpr .x19=BitVec.ofNat 64 j) (hb : s.mem (off base (c.gBits+j))=b)
    {P : Point C} (hp : InvJ C (E c.K.E.x) (E c.K.E.y) (E c.K.E.z) P) (hz : E c.K.E.z=1) :
    WP isa (Joint.signEntry c) s fun t =>
      ∃ E', ProgKeep c.K.M base [c.K.E.y] s t ∧ Inv c.K.M base size C.p Sl V E' t ∧
      InvJ C (E' c.K.E.x) (E' c.K.E.y) (E' c.K.E.z) (if nafNegative b then negPt P else P) ∧
      E' c.K.E.z=1 := by
  rw [Joint.signEntry]
  apply WP.seq
  refine WP.mono (nafSignRead_ok (K:=c.G) hi.scr hBits hj h19 hb) fun a ⟨a3,ka⟩ => ?_
  have ia := hi.of_keeps ka (by decide)
  have kp : ProgKeep c.K.M base [c.K.E.y] s a := keeps_prog ka (by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> simp [clob])
  refine WP.ite (nafNegative b) (by
    change some (a.read .x .x3 != 0)=some (nafNegative b)
    rw [VG.Proof.Ed25519.AArch64.read_x,a3]
    cases nafNegative b <;> decide) (fun hn => ?_) (fun hn => ?_)
  · refine WP.mono (nafNeg_ok hL hAl hm ia hV hxy hzy hzero hp) fun t ⟨kt,it,jt⟩ => ?_
    refine ⟨_,kp.trans kt,it,?_,?_⟩
    · simpa only [hn,ite_true] using jt
    · rw [Function.update_of_ne hzy,hz]
  · apply WP.block_nil
    refine ⟨E,kp,ia,?_,hz⟩
    simpa only [hn,Bool.false_eq_true,ite_false] using hp

end VG.Proof.Weierstrass.AArch64
