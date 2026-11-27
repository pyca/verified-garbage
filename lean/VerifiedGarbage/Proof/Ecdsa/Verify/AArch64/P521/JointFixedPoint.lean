module

import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowState
import VerifiedGarbage.Proof.Weierstrass.AArch64.Fprog
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Ladder
public import VerifiedGarbage.Proof.Weierstrass.Jac
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.P521Joint
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

/-! ### `Ecdsa.Verify.AArch64.P521.JointFixedLoad`, which this module and modules that import it used -/

section

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)
def fixedAddress : List Instr := [.lsl .x .x2 .x2 1,.subImm .x .x2 .x2 2,.movz .x .x3 144 0,
 .mul .x .x2 .x2 .x3,.adrSym .x16 "VG_P521_COMB",.add .x .x16 .x16 .x2]
def fixedLoadBody : List Instr := fixedAddress ++ Joint.loadWords P521Joint.K.E.x 18 ++
 copy 9 P521Joint.K.E.z (p521.sl ONEP)
private theorem syms_write (s : State) (sz : Size) (r : Reg) (x : BitVec sz.bits) :
 (s.write sz r x).syms=s.syms := rfl
theorem fixedAddress_ok {s : State} {a : Nat} {T : Addr}
 (ha : 1≤a) (h2 : s.gpr .x2=BitVec.ofNat 64 a) (ht : s.syms "VG_P521_COMB"=T) :
 WP isa (.block fixedAddress) s fun t =>
 t.gpr .x16=T+BitVec.ofNat 64 (288*(a-1)) ∧ Keeps [.x2,.x3,.x16] s t := by
 apply WP.of_runBlock
 simp only [fixedAddress,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
 RegUpd.gpr_write,syms_write,BitVec.setWidth_eq,Size.bits,h2,ht,
 show 1<64 by decide,show 2<4096 by decide,show 16*0<64 by decide,
 ite_true,ite_false,reduceCtorEq,Option.some.injEq,exists_eq_left']
 refine ⟨?_,?_,rfl,rfl,rfl,rfl⟩
 · simp only [Nat.mul_zero,BitVec.shiftLeft_zero]
   rw [BitVec.shiftLeft_eq_mul_twoPow]
   change T + ((BitVec.ofNat 64 a * BitVec.ofNat 64 2 - BitVec.ofNat 64 2) * BitVec.ofNat 64 144) = _
   rw [←BitVec.ofNat_mul,BitVec.ofNat_sub_ofNat_of_le (a*2) 2 (by decide) (by omega_using [ha]),←BitVec.ofNat_mul]
   congr 2
   omega_using []
 · intro r hr
   simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
   simp only [RegUpd.gpr_write,hr.1,hr.2.1,hr.2.2,ite_false]
/-- Loading x and y and copying the Montgomery one initializes an affine point. -/
theorem fixedLoadBody_ok {s : State} {base T : Addr} {size a : Nat}
    (hs : Scr s base size) (ha : 1≤a) (h2 : s.gpr .x2=BitVec.ofNat 64 a)
    (ht : s.syms "VG_P521_COMB"=T) (hy : P521Joint.K.E.y=P521Joint.K.E.x+72)
    (hd : P521Joint.K.E.x+144≤size) (hd8 : P521Joint.K.E.x%8=0)
    (hz : P521Joint.K.E.z+72≤size) (hz8 : P521Joint.K.E.z%8=0)
    (hone : (p521.sl ONEP)+72≤size) (hone8 : (p521.sl ONEP)%8=0)
    (hsep : P521Joint.K.E.x+144≤P521Joint.K.E.z ∨ P521Joint.K.E.z+72≤P521Joint.K.E.x)
    (hsep1 : P521Joint.K.E.x+144≤(p521.sl ONEP) ∨ (p521.sl ONEP)+72≤P521Joint.K.E.x)
    (hsepz : P521Joint.K.E.z≤(p521.sl ONEP) ∨ (p521.sl ONEP)+72≤P521Joint.K.E.z)
    (hr : ∀ i<18, InRegions (s.rd++s.wr)
      (T+BitVec.ofNat 64 (288*(a-1))+BitVec.ofNat 64 (8*i)) 8)
    (hout : ∀ i<18, ∀ b<8, size≤ofs base
      (T+BitVec.ofNat 64 (288*(a-1))+BitVec.ofNat 64 (8*i)+BitVec.ofNat 64 b)) :
    WP isa (.block fixedLoadBody) s fun t =>
      wordsVal t.mem base P521Joint.K.E.x 9=wordsVal s.mem (T+BitVec.ofNat 64 (288*(a-1))) 0 9 ∧
      wordsVal t.mem base P521Joint.K.E.y 9=wordsVal s.mem (T+BitVec.ofNat 64 (288*(a-1))) 72 9 ∧
      wordsVal t.mem base P521Joint.K.E.z 9=wordsVal s.mem base (p521.sl ONEP) 9 ∧
      KeepRegs [.x1,.x2,.x3,.x4,.x16] s t ∧
      Unch base [(P521Joint.K.E.x,144),(P521Joint.K.E.z,72)] s.mem t.mem := by
  rw [fixedLoadBody,List.append_assoc,WP.block_append_iff]
  refine WP.mono (fixedAddress_ok ha h2 ht) fun b ⟨b16,kb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (jointLoadWords_ok (hs.of_keeps kb (by decide)) b16 hd hd8 (by decide)
    (by intro i hi; rw [kb.rd,kb.wr]; exact hr i hi) hout 18 (by decide)) fun d ⟨wd,kd,od⟩ => ?_
  refine WP.mono (copy_ok 9 ((hs.of_keeps kb (by decide)).of_keepRegs kd (by decide))
    hz hone hz8 hone8 hsepz) fun t ⟨zt,kt,ot⟩ => ?_
  have hn := hs.nowrap
  have wx : wordsVal d.mem base P521Joint.K.E.x 9=wordsVal s.mem (T+BitVec.ofNat 64 (288*(a-1))) 0 9 := by
    refine wordsVal_of_words₂ _ _ _ fun i hi => ?_
    simpa only [Nat.zero_add,kb.mem] using wd i (by omega_using [hi])
  have wy : wordsVal d.mem base P521Joint.K.E.y 9=wordsVal s.mem (T+BitVec.ofNat 64 (288*(a-1))) 72 9 := by
    refine wordsVal_of_words₂ _ _ _ fun i hi => ?_
    rw [hy]
    have e := wd (9+i) (by omega_using [hi])
    simpa only [Nat.mul_add,Nat.add_assoc,kb.mem] using e
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [ot.wordsVal (by omega_using [hsep]) (by omega_using [hd, hn]),wx]
  · rw [ot.wordsVal (by omega_using [hy, hsep]) (by omega_using [hy, hd, hn]),wy]
  · rw [zt,od.wordsVal (by omega_using [hsep1]) (by omega_using [hone, hn]),kb.mem]
  · exact ((Keeps.regs kb).mono (by sub_regs)).trans
      ((kd.mono (by sub_regs)).trans (kt.mono (by sub_regs)))
  · intro x hx
    have hx0 := hx (P521Joint.K.E.x,144) (by simp)
    have hx1 := hx (P521Joint.K.E.z,72) (by simp)
    rw [ot x hx1,od x hx0,kb.mem]

end VG.Proof.Ecdsa.Verify.AArch64.P521.Joint

end

end

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
    · omega_using [e]
    · have := hL.apart _ _ (hD P521Joint.K.E.z (by simp)) (hi.sl _ hOne) e
      rw [hn] at this; omega_using [this]
  simp only [hn,hy] at bx by' bz b1 sxz syz sx1 sy1
  refine WP.mono (fixedLoadBody_ok hi.scr ha h2 ht hy (by omega_using [by'])
    (hAl.sl _ (hD P521Joint.K.E.x (by simp))) bz (hAl.sl _ (hD P521Joint.K.E.z (by simp)))
    b1 (hAl.sl _ (hi.sl _ hOne)) (by omega_using [sxz, syz]) (by omega_using [sx1, sy1]) sz1 hr hout)
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
      rcases hw with rfl | rfl <;> dsimp only <;> omega_arith
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
