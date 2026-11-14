module

public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointFixedSource
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.P384Joint
public import VerifiedGarbage.Impl.Weierstrass.AArch64.Joint
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointLoad
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelectV
import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Mont.AArch64.Row
public import VerifiedGarbage.Proof.Mont.AArch64.Words
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
public import VerifiedGarbage.Proof.Weierstrass.CheckPointContract
public import VerifiedGarbage.Proof.Weierstrass.PointOpsContract
public import VerifiedGarbage.Proof.Weierstrass.InverseContract
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

/-! ### `Ecdsa.Verify.AArch64.P384.JointFixedLoad`, which only this module used -/

section

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)
def fixedLoadBody : List Instr := P384Joint.fixedAddress ++ Joint.loadWords P384Joint.K.E.x 12 ++
 copy 6 P384Joint.K.E.z (p384.sl ONEP)
private theorem syms_write (s : State) (sz : Size) (r : Reg) (x : BitVec sz.bits) :
 (s.write sz r x).syms=s.syms := rfl
theorem fixedAddress_ok {s : State} {a : Nat} {T : Addr}
 (ha : 1≤a) (h2 : s.gpr .x2=BitVec.ofNat 64 a) (ht : s.syms "VG_P384_GTAB"=T) :
 WP isa (.block P384Joint.fixedAddress) s fun t =>
 t.gpr .x16=T+BitVec.ofNat 64 (192*(a-1)) ∧ Keeps [.x2,.x3,.x16] s t := by
 apply WP.of_runBlock
 simp only [P384Joint.fixedAddress,show P384Joint.p384v.tsym="VG_P384_GTAB" from rfl,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
 RegUpd.gpr_write,syms_write,BitVec.setWidth_eq,Size.bits,h2,ht,
 show 1<4096 by decide,show 16*0<64 by decide,
 ite_true,ite_false,reduceCtorEq,Option.some.injEq,exists_eq_left']
 refine ⟨?_,?_,rfl,rfl,rfl,rfl⟩
 · simp only [Nat.mul_zero,BitVec.shiftLeft_zero]
   change T + ((BitVec.ofNat 64 a - BitVec.ofNat 64 1) * BitVec.ofNat 64 192) = _
   rw [BitVec.ofNat_sub_ofNat_of_le a 1 (by decide) (by omega_using [ha]),←BitVec.ofNat_mul]
   congr 2
   omega_using []
 · intro r hr
   simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
   simp only [RegUpd.gpr_write,hr.1,hr.2.1,hr.2.2,ite_false]
/-- Loading x and y and copying the Montgomery one initializes an affine point. -/
theorem fixedLoadBody_ok {s : State} {base T : Addr} {size a : Nat}
    (hs : Scr s base size) (ha : 1≤a) (h2 : s.gpr .x2=BitVec.ofNat 64 a)
    (ht : s.syms "VG_P384_GTAB"=T) (hy : P384Joint.K.E.y=P384Joint.K.E.x+48)
    (hd : P384Joint.K.E.x+96≤size) (hd8 : P384Joint.K.E.x%8=0)
    (hz : P384Joint.K.E.z+48≤size) (hz8 : P384Joint.K.E.z%8=0)
    (hone : (p384.sl ONEP)+48≤size) (hone8 : (p384.sl ONEP)%8=0)
    (hsep : P384Joint.K.E.x+96≤P384Joint.K.E.z ∨ P384Joint.K.E.z+48≤P384Joint.K.E.x)
    (hsep1 : P384Joint.K.E.x+96≤(p384.sl ONEP) ∨ (p384.sl ONEP)+48≤P384Joint.K.E.x)
    (hsepz : P384Joint.K.E.z≤(p384.sl ONEP) ∨ (p384.sl ONEP)+48≤P384Joint.K.E.z)
    (hr : ∀ i<12, InRegions (s.rd++s.wr)
      (T+BitVec.ofNat 64 (192*(a-1))+BitVec.ofNat 64 (8*i)) 8)
    (hout : ∀ i<12, ∀ b<8, size≤ofs base
      (T+BitVec.ofNat 64 (192*(a-1))+BitVec.ofNat 64 (8*i)+BitVec.ofNat 64 b)) :
    WP isa (.block fixedLoadBody) s fun t =>
      wordsVal t.mem base P384Joint.K.E.x 6=wordsVal s.mem (T+BitVec.ofNat 64 (192*(a-1))) 0 6 ∧
      wordsVal t.mem base P384Joint.K.E.y 6=wordsVal s.mem (T+BitVec.ofNat 64 (192*(a-1))) 48 6 ∧
      wordsVal t.mem base P384Joint.K.E.z 6=wordsVal s.mem base (p384.sl ONEP) 6 ∧
      KeepRegs [.x1,.x2,.x3,.x4,.x16] s t ∧
      Unch base [(P384Joint.K.E.x,96),(P384Joint.K.E.z,48)] s.mem t.mem := by
  rw [fixedLoadBody,List.append_assoc,WP.block_append_iff]
  refine WP.mono (fixedAddress_ok ha h2 ht) fun b ⟨b16,kb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (jointLoadWords_ok (hs.of_keeps kb (by decide)) b16 hd hd8 (by decide)
    (by intro i hi; rw [kb.rd,kb.wr]; exact hr i hi) hout 12 (by decide)) fun d ⟨wd,kd,od⟩ => ?_
  refine WP.mono (copy_ok 6 ((hs.of_keeps kb (by decide)).of_keepRegs kd (by decide))
    hz hone hz8 hone8 hsepz) fun t ⟨zt,kt,ot⟩ => ?_
  have hn := hs.nowrap
  have wx : wordsVal d.mem base P384Joint.K.E.x 6=wordsVal s.mem (T+BitVec.ofNat 64 (192*(a-1))) 0 6 := by
    refine wordsVal_of_words₂ _ _ _ fun i hi => ?_
    simpa only [Nat.zero_add,kb.mem] using wd i (by omega_using [hi])
  have wy : wordsVal d.mem base P384Joint.K.E.y 6=wordsVal s.mem (T+BitVec.ofNat 64 (192*(a-1))) 48 6 := by
    refine wordsVal_of_words₂ _ _ _ fun i hi => ?_
    rw [hy]
    have e := wd (6+i) (by omega_using [hi])
    simpa only [Nat.mul_add,Nat.add_assoc,kb.mem] using e
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [ot.wordsVal (by omega_using [hsep]) (by omega_using [hd, hn]),wx]
  · rw [ot.wordsVal (by omega_using [hy, hsep]) (by omega_using [hy, hd, hn]),wy]
  · rw [zt,od.wordsVal (by omega_using [hsep1]) (by omega_using [hone, hn]),kb.mem]
  · exact ((Keeps.regs kb).mono (by sub_regs)).trans
      ((kd.mono (by sub_regs)).trans (kt.mono (by sub_regs)))
  · intro x hx
    have hx0 := hx (P384Joint.K.E.x,96) (by simp)
    have hx1 := hx (P384Joint.K.E.z,48) (by simp)
    rw [ot x hx1,od x hx0,kb.mem]

end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint

end

end


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
        right; dsimp only; omega_using [h0, this]
      · rw [List.mem_singleton.mp hw]; left; dsimp only; omega_using [ht, hb, h1])
      (by omega_using [hb, h1])
  exact ⟨by rw [e _ (by omega_using []) (by omega_using [hj])]; exact h.lo,by rw [e _ (by omega_using []) (by omega_using [hj])]; exact h.hi⟩

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
 have ha : 1≤a := by dsimp [a]; omega_using [hm0]
 have ha32 : a≤128 := by dsimp [a]; omega_using [hmag]
 have he : 2*a-1=FastNaf.magnitude 9 u j := by dsimp [a]; omega_using [hodd]
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
   (signRead9_ok cfg_gw id.scr (by decide) (by change 3152+2*j+2≤8192; omega_using [hj]) dj db.hi) jd zd)
   fun t ⟨Et,kt,it,jt,zt⟩ => ?_
 refine ⟨Et,kd.trans (kt.mono (by simp [fixedCoords,P384Joint.cfg])),it,?_,zt⟩
 simpa only [FastNaf.point,P384Joint.cfg] using jt
end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
