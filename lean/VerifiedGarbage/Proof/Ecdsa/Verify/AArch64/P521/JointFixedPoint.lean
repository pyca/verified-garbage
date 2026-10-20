module
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedLoad
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowState
@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass
/-- The generator row is consumed directly as canonical Montgomery coordinates. -/
theorem fixedPoint_ok {s : State} {base T : Addr} {size a : Nat} {C : Curve}
    {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fe C}
    (hL : Lay P521Joint.K.M size Sl) (hAl : Aligned P521Joint.K.M Sl) (hn : P521Joint.K.M.n=9)
    (hi : Inv P521Joint.K.M base size C.p Sl V E s)
    (ha : 1≤a) (h2 : s.gpr .x2=BitVec.ofNat 64 a) (ht : s.syms "VG_P521_COMB"=T)
    (hy : P521Joint.K.E.y=P521Joint.K.E.x+72)
    (hD : ∀ x∈[P521Joint.K.E.x,P521Joint.K.E.y,P521Joint.K.E.z],Sl x)
    (hdz : P521Joint.K.E.x≠P521Joint.K.E.z) (hyz : P521Joint.K.E.y≠P521Joint.K.E.z)
    (hx1 : P521Joint.K.E.x≠(p521.sl ONEP)) (hy1 : P521Joint.K.E.y≠(p521.sl ONEP))
    (hOne : (p521.sl ONEP)∈V) (hOneVal : E (p521.sl ONEP)=1)
    (hr : ∀ i<18, InRegions (s.rd++s.wr)
      (T+BitVec.ofNat 64 (288*(a-1))+BitVec.ofNat 64 (8*i)) 8)
    (hout : ∀ i<18, ∀ b<8, size≤ofs base
      (T+BitVec.ofNat 64 (288*(a-1))+BitVec.ofNat 64 (8*i)+BitVec.ofNat 64 b))
    (hxy : wordsVal s.mem (T+BitVec.ofNat 64 (288*(a-1))) 0 9<C.p ∧
      wordsVal s.mem (T+BitVec.ofNat 64 (288*(a-1))) 72 9<C.p)
    {P : Point C} (hJ : InvJ C
      (toM C.p (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat)) 2 (64*9)) (wordsVal s.mem (T+BitVec.ofNat 64 (288*(a-1))) 0 9))
      (toM C.p (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat)) 2 (64*9)) (wordsVal s.mem (T+BitVec.ofNat 64 (288*(a-1))) 72 9)) 1 P) :
    WP isa (.block fixedLoadBody) s fun t =>
      ProgKeep P521Joint.K.M base [P521Joint.K.E.x,P521Joint.K.E.y,P521Joint.K.E.z] s t ∧
      Inv P521Joint.K.M base size C.p Sl ([P521Joint.K.E.x,P521Joint.K.E.y,P521Joint.K.E.z]++V) (tmv C P521Joint.K.M.n base t) t ∧
      InvJ C (tmv C P521Joint.K.M.n base t P521Joint.K.E.x) (tmv C P521Joint.K.M.n base t P521Joint.K.E.y)
        (tmv C P521Joint.K.M.n base t P521Joint.K.E.z) P ∧ tmv C P521Joint.K.M.n base t P521Joint.K.E.z=1 := by
  have bx := hL.le _ (hD P521Joint.K.E.x (by simp))
  have by' := hL.le _ (hD P521Joint.K.E.y (by simp))
  have bz := hL.le _ (hD P521Joint.K.E.z (by simp))
  have b1 := hL.le _ (hi.sl _ hOne)
  have sxz := hL.apart _ _ (hD P521Joint.K.E.x (by simp)) (hD P521Joint.K.E.z (by simp)) hdz
  have syz := hL.apart _ _ (hD P521Joint.K.E.y (by simp)) (hD P521Joint.K.E.z (by simp)) hyz
  have sx1 := hL.apart _ _ (hD P521Joint.K.E.x (by simp)) (hi.sl _ hOne) hx1
  have sy1 := hL.apart _ _ (hD P521Joint.K.E.y (by simp)) (hi.sl _ hOne) hy1
  have sz1 : P521Joint.K.E.z≤(p521.sl ONEP) ∨ (p521.sl ONEP)+72≤P521Joint.K.E.z := by
    by_cases e : P521Joint.K.E.z=(p521.sl ONEP)
    · omega
    · have := hL.apart _ _ (hD P521Joint.K.E.z (by simp)) (hi.sl _ hOne) e
      rw [hn] at this; omega
  simp only [hn,hy] at bx by' bz b1 sxz syz sx1 sy1
  refine WP.mono (fixedLoadBody_ok hi.scr ha h2 ht hy (by omega)
    (hAl.sl _ (hD P521Joint.K.E.x (by simp))) bz (hAl.sl _ (hD P521Joint.K.E.z (by simp)))
    b1 (hAl.sl _ (hi.sl _ hOne)) (by omega) (by omega) sz1 hr hout)
    fun t ⟨vx,vy,vz,kt,ut⟩ => ?_
  have kp : ProgKeep P521Joint.K.M base [P521Joint.K.E.x,P521Joint.K.E.y,P521Joint.K.E.z] s t := by
    refine ⟨fun r hr => kt.gpr r (fun hh => hr ?_),kt.rd,kt.wr,kt.sp,fun x hx _ => ut x ?_⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
      rcases hh with rfl | rfl | rfl | rfl | rfl <;> simp [clob]
    · intro w hw
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      have hx0 := hx P521Joint.K.E.x (by simp)
      have hx1 := hx P521Joint.K.E.y (by simp)
      have hx2 := hx P521Joint.K.E.z (by simp)
      rw [hn] at hx0 hx1 hx2
      rw [hy] at hx1
      rcases hw with rfl | rfl <;> dsimp only <;> omega
  have hlt : ∀ x∈[P521Joint.K.E.x,P521Joint.K.E.y,P521Joint.K.E.z],wordsVal t.mem base x P521Joint.K.M.n<C.p := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rw [hn]
    rcases hx with rfl | rfl | rfl
    · rw [vx]; exact hxy.1
    · rw [vy]; exact hxy.2
    · rw [vz,←hn]; exact hi.lt _ hOne
  have zz : tmv C P521Joint.K.M.n base t P521Joint.K.E.z=1 := by
    unfold tmv
    rw [hn,vz,←hn,hi.val _ hOne,hOneVal]
  refine ⟨kp,hi.of_progKeep hL kp hD hlt,?_,zz⟩
  rw [zz]
  unfold tmv
  rw [hn,vx,vy]
  exact hJ

end VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
