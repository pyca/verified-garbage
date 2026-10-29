module

public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointFixedSource
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointFixedLoad
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.State
public import VerifiedGarbage.Proof.Weierstrass.FastNaf
public import VerifiedGarbage.Impl.Ecdsa.AArch64
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words

import VerifiedGarbage.Proof.Weierstrass.AArch64.JointRead9
import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafArith
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeStore
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointEntry
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeArithmetic
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointRead
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowState
import VerifiedGarbage.Proof.Weierstrass.AArch64.Ladder
import VerifiedGarbage.Proof.Weierstrass.Jac

-- Formerly `VerifiedGarbage/Proof/Ecdsa/Verify/AArch64/P384/JointFixedPoint.lean`, which only this module imported.
section

section
namespace VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass
/-- The generator row is consumed directly as canonical Montgomery coordinates. -/
theorem fixedPoint_ok {s : State} {base T : Addr} {size a : Nat} {C : Curve}
    {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fe C}
    (hL : Lay P384Joint.K.M size Sl) (hAl : Aligned P384Joint.K.M Sl) (hn : P384Joint.K.M.n=6)
    (hi : Inv P384Joint.K.M base size C.p Sl V E s)
    (ha : 1≤a) (h2 : s.gpr .x2=BitVec.ofNat 64 a) (ht : s.syms "VG_P384_GTAB"=T)
    (hy : P384Joint.K.E.y=P384Joint.K.E.x+48)
    (hD : ∀ x∈[P384Joint.K.E.x,P384Joint.K.E.y,P384Joint.K.E.z],Sl x)
    (hdz : P384Joint.K.E.x≠P384Joint.K.E.z) (hyz : P384Joint.K.E.y≠P384Joint.K.E.z)
    (hx1 : P384Joint.K.E.x≠(p384.sl ONEP)) (hy1 : P384Joint.K.E.y≠(p384.sl ONEP))
    (hOne : (p384.sl ONEP)∈V) (hOneVal : E (p384.sl ONEP)=1)
    (hr : ∀ i<12, InRegions (s.rd++s.wr)
      (T+BitVec.ofNat 64 (192*(a-1))+BitVec.ofNat 64 (8*i)) 8)
    (hout : ∀ i<12, ∀ b<8, size≤ofs base
      (T+BitVec.ofNat 64 (192*(a-1))+BitVec.ofNat 64 (8*i)+BitVec.ofNat 64 b))
    (hxy : wordsVal s.mem (T+BitVec.ofNat 64 (192*(a-1))) 0 6<C.p ∧
      wordsVal s.mem (T+BitVec.ofNat 64 (192*(a-1))) 48 6<C.p)
    {P : Point C} (hJ : InvJ C
      (toM C.p (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat)) 2 (64*6)) (wordsVal s.mem (T+BitVec.ofNat 64 (192*(a-1))) 0 6))
      (toM C.p (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat)) 2 (64*6)) (wordsVal s.mem (T+BitVec.ofNat 64 (192*(a-1))) 48 6)) 1 P) :
    WP isa (.block fixedLoadBody) s fun t =>
      ProgKeep P384Joint.K.M base [P384Joint.K.E.x,P384Joint.K.E.y,P384Joint.K.E.z] s t ∧
      Inv P384Joint.K.M base size C.p Sl ([P384Joint.K.E.x,P384Joint.K.E.y,P384Joint.K.E.z]++V) (tmv C P384Joint.K.M.n base t) t ∧
      InvJ C (tmv C P384Joint.K.M.n base t P384Joint.K.E.x) (tmv C P384Joint.K.M.n base t P384Joint.K.E.y)
        (tmv C P384Joint.K.M.n base t P384Joint.K.E.z) P ∧ tmv C P384Joint.K.M.n base t P384Joint.K.E.z=1 := by
  have bx := hL.le _ (hD P384Joint.K.E.x (by simp))
  have by' := hL.le _ (hD P384Joint.K.E.y (by simp))
  have bz := hL.le _ (hD P384Joint.K.E.z (by simp))
  have b1 := hL.le _ (hi.sl _ hOne)
  have sxz := hL.apart _ _ (hD P384Joint.K.E.x (by simp)) (hD P384Joint.K.E.z (by simp)) hdz
  have syz := hL.apart _ _ (hD P384Joint.K.E.y (by simp)) (hD P384Joint.K.E.z (by simp)) hyz
  have sx1 := hL.apart _ _ (hD P384Joint.K.E.x (by simp)) (hi.sl _ hOne) hx1
  have sy1 := hL.apart _ _ (hD P384Joint.K.E.y (by simp)) (hi.sl _ hOne) hy1
  have sz1 : P384Joint.K.E.z≤(p384.sl ONEP) ∨ (p384.sl ONEP)+48≤P384Joint.K.E.z := by
    by_cases e : P384Joint.K.E.z=(p384.sl ONEP)
    · omega
    · have := hL.apart _ _ (hD P384Joint.K.E.z (by simp)) (hi.sl _ hOne) e
      rw [hn] at this; omega
  simp only [hn,hy] at bx by' bz b1 sxz syz sx1 sy1
  refine WP.mono (fixedLoadBody_ok hi.scr ha h2 ht hy (by omega)
    (hAl.sl _ (hD P384Joint.K.E.x (by simp))) bz (hAl.sl _ (hD P384Joint.K.E.z (by simp)))
    b1 (hAl.sl _ (hi.sl _ hOne)) (by omega) (by omega) sz1 hr hout)
    fun t ⟨vx,vy,vz,kt,ut⟩ => ?_
  have kp : ProgKeep P384Joint.K.M base [P384Joint.K.E.x,P384Joint.K.E.y,P384Joint.K.E.z] s t := by
    refine ⟨fun r hr => kt.gpr r (fun hh => hr ?_),kt.rd,kt.wr,kt.sp,fun x hx _ => ut x ?_⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
      rcases hh with rfl | rfl | rfl | rfl | rfl <;> simp [clob]
    · intro w hw
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      have hx0 := hx P384Joint.K.E.x (by simp)
      have hx1 := hx P384Joint.K.E.y (by simp)
      have hx2 := hx P384Joint.K.E.z (by simp)
      rw [hn] at hx0 hx1 hx2
      rw [hy] at hx1
      rcases hw with rfl | rfl <;> dsimp only <;> omega
  have hlt : ∀ x∈[P384Joint.K.E.x,P384Joint.K.E.y,P384Joint.K.E.z],wordsVal t.mem base x P384Joint.K.M.n<C.p := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rw [hn]
    rcases hx with rfl | rfl | rfl
    · rw [vx]; exact hxy.1
    · rw [vy]; exact hxy.2
    · rw [vz,←hn]; exact hi.lt _ hOne
  have zz : tmv C P384Joint.K.M.n base t P384Joint.K.E.z=1 := by
    unfold tmv
    rw [hn,vz,←hn,hi.val _ hOne,hOneVal]
  refine ⟨kp,hi.of_progKeep hL kp hD hlt,?_,zz⟩
  rw [zz]
  unfold tmv
  rw [hn,vx,vy]
  exact hJ

end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
end

end

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass
open VG.Proof.Weierstrass.AArch64.PubNaf

theorem fixedLoad_eq : P384Joint.fixedLoad = Joint.fixedIndex P384Joint.cfg ++ fixedLoadBody := by
 simp only [P384Joint.fixedLoad,fixedLoadBody,List.append_assoc]

def fixedCoords : List Nat := [P384Joint.K.E.x,P384Joint.K.E.y,P384Joint.K.E.z]

theorem cfg_gw : P384Joint.cfg.gw=9 := rfl

/-- Digit `j`'s bytes, as the generator's digits hold them. -/
structure GBytes (base : Addr) (u j : Nat) (s : State) : Prop where
  lo : s.mem (off base (P384Joint.KG.bits+2*j))=FastNaf.wbyte u (2*j)
  hi : s.mem (off base (P384Joint.KG.bits+(2*j+1)))=FastNaf.wbyte u (2*j+1)

/-- The generator's digits miss what a lookup writes: its coordinates and the temporary. -/
theorem gbytes_apart : ∀ x∈fixedCoords,x+8*P384Joint.K.M.n≤P384Joint.KG.bits := by decide

theorem GBytes.keep {base : Addr} {u j : Nat} {s t : State} (h : GBytes base u j s) (hj : j<385)
    (hk : ProgKeep P384Joint.K.M base fixedCoords s t) : GBytes base u j t := by
  have ha := gbytes_apart
  have ht : P384Joint.K.M.tmp=4000 := rfl
  have hb : P384Joint.KG.bits=3152 := rfl
  have hn : P384Joint.K.M.n=6 := rfl
  have e : ∀ d, P384Joint.KG.bits≤d → d<P384Joint.KG.bits+770 → t.mem (off base d)=s.mem (off base d) := by
    intro d h0 h1
    apply hk.unch.byte (by
      intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · simp only [List.mem_map] at hw
        obtain ⟨x,hx,rfl⟩ := hw
        have := ha x hx
        right; dsimp only; omega
      · rw [List.mem_singleton.mp hw]; left; dsimp only; omega)
      (by omega)
  exact ⟨by rw [e _ (by omega) (by omega)]; exact h.lo,by rw [e _ (by omega) (by omega)]; exact h.hi⟩

theorem fixedLookup_ok {s : State} {base T : Addr} {u j : Nat} {C : Curve} {G : Point C}
 {V : List Nat} {E : Nat → Fe C}
 (hL : NafLay P384Joint.K 8192)
 (hi : Inv P384Joint.K.M base 8192 C.p (·∈winSlots P384Joint.K) V E s)
 (hV : ∀ x∈[P384Joint.K.zero,p384.sl ONEP],x∈V)
 (hone : E (p384.sl ONEP)=1)
 (source : FixedGenerator C base 8192 G T s)
 (hj : j<385) (h19 : s.gpr .x19=BitVec.ofNat 64 j)
 (hbytes : GBytes base u j s)
 (h2 : s.gpr .x2=(FastNaf.wbyte u (2*j)).setWidth 64)
 (h3 : s.gpr .x3=(FastNaf.wbyte u (2*j+1)).setWidth 64)
 (hm0 : FastNaf.magnitude 9 u j≠0) :
 WP isa (.block P384Joint.fixedLoad) s fun d =>
 ProgKeep P384Joint.K.M base fixedCoords s d ∧
 Inv P384Joint.K.M base 8192 C.p (·∈winSlots P384Joint.K) (fixedCoords++V) (tmv C P384Joint.K.M.n base d) d ∧
 InvJ C (tmv C P384Joint.K.M.n base d P384Joint.K.E.x)
   (tmv C P384Joint.K.M.n base d P384Joint.K.E.y) (tmv C P384Joint.K.M.n base d P384Joint.K.E.z)
   (mul (FastNaf.magnitude 9 u j) G) ∧
 tmv C P384Joint.K.M.n base d P384Joint.K.E.z=1 ∧
 d.gpr .x19=BitVec.ofNat 64 j ∧ GBytes base u j d := by
 let a := (FastNaf.magnitude 9 u j+1)/2
 have hmag := fastMagnitude_bound 9 u j
 have hodd := (FastNaf.magnitude_odd_or_zero 9 u j).resolve_left hm0
 have ha : 1≤a := by dsimp [a]; omega
 have ha32 : a≤128 := by dsimp [a]; omega
 have he : 2*a-1=FastNaf.magnitude 9 u j := by dsimp [a]; omega
 have es : ∀x∈fixedCoords,x∈winSlots P384Joint.K := by decide
 rw [fixedLoad_eq,WP.block_append_iff]
 refine WP.mono_syms (jointFixedIndex_ok (c:=P384Joint.cfg) (Or.inr rfl)
   (by rw [jointGCell,ite_eq_left cfg_gw]; exact h2) (fun _ => h3)) fun b ⟨b2,kb⟩ sb => ?_
 rw [cfg_gw] at b2
 have ib := hi.of_keeps kb (by decide)
 have kp : ProgKeep P384Joint.K.M base [] s b := keeps_prog kb (by decide)
 have srcb := source.keep kp sb (by simp) hi.mod.tmp
 refine WP.mono (fixedPoint_ok hL.win.lay hL.al.al (by decide) ib ha b2 srcb.symbol
   (by decide) es (by decide) (by decide) (by decide) (by decide)
   (hV _ (by simp)) hone (srcb.read a ha ha32) (srcb.outside a ha ha32)
   (srcb.bounds a ha ha32) (srcb.point a ha ha32)) fun d ⟨kd,id,jd,zd⟩ => ?_
 have dj : d.gpr .x19=BitVec.ofNat 64 j := by rw [kd.gpr _ (x19_not_clob _),kb.gpr _ (by decide),h19]
 have kbd : ProgKeep P384Joint.K.M base fixedCoords s d := (kp.mono (by simp)).trans kd
 rw [he] at jd
 exact ⟨kbd,id,jd,zd,dj,hbytes.keep hj kbd⟩

theorem fixedEntry_ok {s : State} {base T : Addr} {u j : Nat} {C : Curve} {G : Point C}
 {V : List Nat} {E : Nat → Fe C}
 (hL : NafLay P384Joint.K 8192)
 (hm : UnitMod C.p (2^(64*P384Joint.K.M.n)))
 (hi : Inv P384Joint.K.M base 8192 C.p (·∈winSlots P384Joint.K) V E s)
 (hV : ∀ x∈[P384Joint.K.zero,p384.sl ONEP],x∈V)
 (hzero : E P384Joint.K.zero=0) (hone : E (p384.sl ONEP)=1)
 (source : FixedGenerator C base 8192 G T s)
 (hj : j<385) (h19 : s.gpr .x19=BitVec.ofNat 64 j)
 (hbytes : GBytes base u j s)
 (h2 : s.gpr .x2=(FastNaf.wbyte u (2*j)).setWidth 64)
 (h3 : s.gpr .x3=(FastNaf.wbyte u (2*j+1)).setWidth 64)
 (hm0 : FastNaf.magnitude 9 u j≠0) :
 WP isa P384Joint.fixedEntry s fun t =>
 ∃ E', ProgKeep P384Joint.K.M base fixedCoords s t ∧
 Inv P384Joint.K.M base 8192 C.p (·∈winSlots P384Joint.K) (fixedCoords++V) E' t ∧
 InvJ C (E' P384Joint.K.E.x) (E' P384Joint.K.E.y) (E' P384Joint.K.E.z)
   (FastNaf.point C G 9 u j) ∧ E' P384Joint.K.E.z=1 := by
 rw [P384Joint.fixedEntry]
 apply WP.seq
 refine WP.mono (fixedLookup_ok hL hi hV hone source hj h19 hbytes h2 h3 hm0) fun d ⟨kd,id,jd,zd,dj,db⟩ => ?_
 have vz : tmv C P384Joint.K.M.n base d P384Joint.K.zero=0 := by
   unfold tmv
   rw [kd.slot hL.win.lay hi.scr (by decide) (by decide) (by decide),hi.val _ (hV _ (by simp)),hzero]
 have vv : ∀x∈[P384Joint.K.E.x,P384Joint.K.E.y,P384Joint.K.E.z,P384Joint.K.zero],x∈fixedCoords++V := by
   intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
   rcases hx with rfl | rfl | rfl | rfl
   · exact List.mem_append_left _ (by simp [fixedCoords])
   · exact List.mem_append_left _ (by simp [fixedCoords])
   · exact List.mem_append_left _ (by simp [fixedCoords])
   · exact List.mem_append_right _ (hV _ (by simp))
 refine WP.mono (jointSignEntryG_ok P384Joint.cfg (FastNaf.negative 9 u j) hL.win.lay hL.al.al (by simpa only [P384Joint.cfg] using hm) id vv
   (by decide) (by decide) vz
   (signRead9_ok cfg_gw id.scr (by decide) (by change 3152+2*j+2≤8192; omega) dj db.hi) jd zd)
   fun t ⟨Et,kt,it,jt,zt⟩ => ?_
 refine ⟨Et,kd.trans (kt.mono (by simp [fixedCoords,P384Joint.cfg])),it,?_,zt⟩
 simpa only [FastNaf.point,P384Joint.cfg] using jt
end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
