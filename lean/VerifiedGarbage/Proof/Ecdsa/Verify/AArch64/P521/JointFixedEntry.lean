module
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedSource
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedLoad
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafDigitRead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.State
public import VerifiedGarbage.Proof.Weierstrass.FastNaf
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeStore
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedPoint
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointEntry
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeArithmetic
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Weierstrass.AArch64.Unch
@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass
open VG.Proof.Weierstrass.AArch64.PubNaf

def fixedCfg : Impl.Weierstrass.AArch64.Joint.Cfg :=
 ⟨P521Joint.K,P521Joint.KG.bits,p521.sl ONEP,"VG_P521_COMB",7⟩

theorem fixedLoad_eq : P521Joint.fixedLoad = Naf.digitIndex ++ fixedLoadBody := by
 simp only [P521Joint.fixedLoad,fixedLoadBody,fixedAddress,Impl.Weierstrass.AArch64.Joint.loadWords,List.append_assoc]

def fixedCoords : List Nat := [P521Joint.K.E.x,P521Joint.K.E.y,P521Joint.K.E.z]

theorem fixedLookup_ok {s : State} {base T : Addr} {u j : Nat} {C : Curve} {G : Point C}
 {V : List Nat} {E : Nat → Fe C}
 (hL : NafLay P521Joint.K 8192)
 (hi : Inv P521Joint.K.M base 8192 C.p (·∈winSlots P521Joint.K) V E s)
 (hV : ∀ x∈[P521Joint.K.zero,p521.sl ONEP],x∈V)
 (hone : E (p521.sl ONEP)=1)
 (source : FixedGenerator C base 8192 G T s)
 (hj : j<577) (h19 : s.gpr .x19=BitVec.ofNat 64 j)
 (hbytes : s.mem (off base (P521Joint.KG.bits+j))=FastNaf.byte 7 u j)
 (h2 : s.gpr .x2=(FastNaf.byte 7 u j).setWidth 64)
 (hm0 : FastNaf.magnitude 7 u j≠0) :
 WP isa (.block P521Joint.fixedLoad) s fun d =>
 ProgKeep P521Joint.K.M base fixedCoords s d ∧
 Inv P521Joint.K.M base 8192 C.p (·∈winSlots P521Joint.K) (fixedCoords++V) (tmv C P521Joint.K.M.n base d) d ∧
 InvJ C (tmv C P521Joint.K.M.n base d P521Joint.K.E.x)
   (tmv C P521Joint.K.M.n base d P521Joint.K.E.y) (tmv C P521Joint.K.M.n base d P521Joint.K.E.z)
   (mul (FastNaf.magnitude 7 u j) G) ∧
 tmv C P521Joint.K.M.n base d P521Joint.K.E.z=1 ∧
 d.gpr .x19=BitVec.ofNat 64 j ∧
 d.mem (off base (P521Joint.KG.bits+j))=FastNaf.byte 7 u j := by
 let a := (FastNaf.magnitude 7 u j+1)/2
 have hmag := FastNaf.magnitude_le (w:=7) (Or.inr rfl) u j
 have hodd := (FastNaf.magnitude_odd_or_zero 7 u j).resolve_left hm0
 have ha : 1≤a := by dsimp [a]; omega
 have ha32 : a≤32 := by dsimp [a]; change FastNaf.magnitude 7 u j≤63 at hmag; omega
 have he : 2*a-1=FastNaf.magnitude 7 u j := by dsimp [a]; omega
 have es : ∀x∈fixedCoords,x∈winSlots P521Joint.K := by decide
 rw [fixedLoad_eq]
 rw [WP.block_append_iff]
 refine WP.mono_syms (nafIndex_ok h2) fun b ⟨b2,kb⟩ sb => ?_
 have hbmag : nafMagnitude (FastNaf.byte 7 u j)=FastNaf.magnitude 7 u j := FastNaf.byte_magnitude 7 u j
 rw [hbmag] at b2
 have ib := hi.of_keeps kb (by decide)
 have kp : ProgKeep P521Joint.K.M base [] s b := keeps_prog kb (by decide)
 have srcb := source.keep kp sb (by simp) hi.mod.tmp
 refine WP.mono (fixedPoint_ok hL.win.lay hL.al.al (by decide) ib ha b2 srcb.symbol
   (by decide) es (by decide) (by decide) (by decide) (by decide)
   (hV _ (by simp)) hone (srcb.read a ha ha32) (srcb.outside a ha ha32)
   (srcb.bounds a ha ha32) (srcb.point a ha ha32)) fun d ⟨kd,id,jd,zd⟩ => ?_
 have dj : d.gpr .x19=BitVec.ofNat 64 j := by rw [kd.gpr _ (x19_not_clob _),kb.gpr _ (by decide),h19]
 have db : d.mem (off base (P521Joint.KG.bits+j))=FastNaf.byte 7 u j := by
   rw [kd.unch.byte (by
     intro w hw
     rcases List.mem_append.mp hw with hw | hw
     · simp only [List.mem_map] at hw
       obtain ⟨x,hx,rfl⟩ := hw
       have end' : ∀x∈fixedCoords,x+8*P521Joint.K.M.n≤3304 := by decide
       have := end' x hx
       right
       change x+8*P521Joint.K.M.n≤P521Joint.KG.bits+j
       change x+8*P521Joint.K.M.n≤3304+j
       omega
     · rw [List.mem_singleton.mp hw]; change 3304+j+1≤3952 ∨ _; omega)
     (by change 3304+j<2^64; omega),kb.mem,hbytes]
 rw [he] at jd
 exact ⟨(kp.mono (by simp)).trans kd,id,jd,zd,dj,db⟩

theorem fixedEntry_ok {s : State} {base T : Addr} {u j : Nat} {C : Curve} {G : Point C}
 {V : List Nat} {E : Nat → Fe C}
 (hL : NafLay P521Joint.K 8192)
 (hm : UnitMod C.p (2^(64*P521Joint.K.M.n)))
 (hi : Inv P521Joint.K.M base 8192 C.p (·∈winSlots P521Joint.K) V E s)
 (hV : ∀ x∈[P521Joint.K.zero,p521.sl ONEP],x∈V)
 (hzero : E P521Joint.K.zero=0) (hone : E (p521.sl ONEP)=1)
 (source : FixedGenerator C base 8192 G T s)
 (hj : j<577) (h19 : s.gpr .x19=BitVec.ofNat 64 j)
 (hbytes : s.mem (off base (P521Joint.KG.bits+j))=FastNaf.byte 7 u j)
 (h2 : s.gpr .x2=(FastNaf.byte 7 u j).setWidth 64)
 (hm0 : FastNaf.magnitude 7 u j≠0) :
 WP isa P521Joint.fixedEntry s fun t =>
 ∃ E', ProgKeep P521Joint.K.M base fixedCoords s t ∧
 Inv P521Joint.K.M base 8192 C.p (·∈winSlots P521Joint.K) (fixedCoords++V) E' t ∧
 InvJ C (E' P521Joint.K.E.x) (E' P521Joint.K.E.y) (E' P521Joint.K.E.z)
   (FastNaf.point C G 7 u j) ∧ E' P521Joint.K.E.z=1 := by
 let a := (FastNaf.magnitude 7 u j+1)/2
 have hmag := FastNaf.magnitude_le (w:=7) (Or.inr rfl) u j
 have hodd := (FastNaf.magnitude_odd_or_zero 7 u j).resolve_left hm0
 have ha : 1≤a := by dsimp [a]; omega
 have ha32 : a≤32 := by dsimp [a]; change FastNaf.magnitude 7 u j≤63 at hmag; omega
 have he : 2*a-1=FastNaf.magnitude 7 u j := by dsimp [a]; omega
 have es : ∀x∈fixedCoords,x∈winSlots P521Joint.K := by decide
 rw [P521Joint.fixedEntry,fixedLoad_eq]
 apply WP.seq
 rw [WP.block_append_iff]
 refine WP.mono_syms (nafIndex_ok h2) fun b ⟨b2,kb⟩ sb => ?_
 have hbmag : nafMagnitude (FastNaf.byte 7 u j)=FastNaf.magnitude 7 u j := FastNaf.byte_magnitude 7 u j
 rw [hbmag] at b2
 have ib := hi.of_keeps kb (by decide)
 have kp : ProgKeep P521Joint.K.M base [] s b := keeps_prog kb (by decide)
 have srcb := source.keep kp sb (by simp) hi.mod.tmp
 refine WP.mono (fixedPoint_ok hL.win.lay hL.al.al (by decide) ib ha b2 srcb.symbol
   (by decide) es (by decide) (by decide) (by decide) (by decide)
   (hV _ (by simp)) hone (srcb.read a ha ha32) (srcb.outside a ha ha32)
   (srcb.bounds a ha ha32) (srcb.point a ha ha32)) fun d ⟨kd,id,jd,zd⟩ => ?_
 have dj : d.gpr .x19=BitVec.ofNat 64 j := by rw [kd.gpr _ (x19_not_clob _),kb.gpr _ (by decide),h19]
 have db : d.mem (off base (P521Joint.KG.bits+j))=FastNaf.byte 7 u j := by
   rw [kd.unch.byte (by
     intro w hw
     rcases List.mem_append.mp hw with hw | hw
     · simp only [List.mem_map] at hw
       obtain ⟨x,hx,rfl⟩ := hw
       have end' : ∀x∈fixedCoords,x+8*P521Joint.K.M.n≤3304 := by decide
       have := end' x hx
       right
       change x+8*P521Joint.K.M.n≤P521Joint.KG.bits+j
       change x+8*P521Joint.K.M.n≤3304+j
       omega
     · rw [List.mem_singleton.mp hw]; change 3304+j+1≤3952 ∨ _; omega)
     (by change 3304+j<2^64; omega),kb.mem,hbytes]
 have vz : tmv C P521Joint.K.M.n base d P521Joint.K.zero=0 := by
   unfold tmv
   rw [kd.slot hL.win.lay ib.scr es (by decide) (by decide),ib.val _ (hV _ (by simp)),hzero]
 have vv : ∀x∈[P521Joint.K.E.x,P521Joint.K.E.y,P521Joint.K.E.z,P521Joint.K.zero],x∈fixedCoords++V := by
   intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
   rcases hx with rfl | rfl | rfl | rfl
   · exact List.mem_append_left _ (by simp [fixedCoords])
   · exact List.mem_append_left _ (by simp [fixedCoords])
   · exact List.mem_append_left _ (by simp [fixedCoords])
   · exact List.mem_append_right _ (hV _ (by simp))
 change WP isa (Impl.Weierstrass.AArch64.Joint.signEntry fixedCfg) d _
 refine WP.mono (jointSignEntry_ok fixedCfg (by decide) hL.win.lay hL.al.al (by
   simpa only [fixedCfg] using hm) id vv
   (by decide) (by decide) vz (by decide) (by change 3304+j<8192; omega) dj db jd zd) fun t ⟨Et,kt,it,jt,zt⟩ => ?_
 refine ⟨Et,(kp.mono (by simp)).trans (kd.trans (kt.mono (by simp [fixedCfg]))),it,?_,zt⟩
 simpa only [fixedCfg,he,nafNegative,FastNaf.byte_negative 7 u j,FastNaf.point] using jt
end VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
