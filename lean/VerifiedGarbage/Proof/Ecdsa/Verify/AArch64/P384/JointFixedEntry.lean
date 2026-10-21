module
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointFixedSource
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointFixedLoad
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointRead9
import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafArith
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.State
public import VerifiedGarbage.Proof.Weierstrass.FastNaf
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeStore
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointFixedPoint
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointEntry
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeArithmetic
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Ecdsa.AArch64
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointRead
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
