module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.JointDigit
public import VerifiedGarbage.Proof.Weierstrass.Joint
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedEntry
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.DigitTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedTiming

import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedBridge
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointLayout
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedChecks
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedLookupTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTableTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedSignTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedTimingB
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeArithmetic

-- Formerly `VerifiedGarbage/Proof/Ecdsa/Verify/AArch64/P521/JointFixedLookupTiming.lean`, which only this module imported.
section

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass
open VG.Proof.Weierstrass.AArch64.PubNaf

structure FixedInput (C : Curve) (base T : Addr) (G : Point C) (u j : Nat) (s : State) : Prop where
 source : FixedGenerator C base 8192 G T s
 x19 : s.gpr .x19=BitVec.ofNat 64 j
 bytes : s.mem (off base (P521Joint.KG.bits+j))=FastNaf.byte 7 u j
 x2 : s.gpr .x2=(FastNaf.byte 7 u j).setWidth 64

theorem fixedLookup_relCT {C : Curve} {base T : Addr} {G : Point C} {u j : Nat}
 {V : List Nat} {E : Nat → Fe C} (hL : NafLay P521Joint.K 8192) (hC : Law C)
 (hV : ∀x∈[P521Joint.K.zero,p521.sl ONEP],x∈V) (hone : E (p521.sl ONEP)=1)
 (hj : j<577) (hm0 : FastNaf.magnitude 7 u j≠0) :
 RelCT isa (fun s t=>FieldPair P521Joint.K.M base 8192 C.p (·∈winSlots P521Joint.K) V E s t ∧
 FixedInput C base T G u j s ∧ FixedInput C base T G u j t)
 (.block P521Joint.fixedLoad)
 (fun s t=>∃ E',FieldPair P521Joint.K.M base 8192 C.p (·∈winSlots P521Joint.K) (fixedCoords++V) E' s t ∧
 s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j ∧
 s.mem (off base (P521Joint.KG.bits+j))=FastNaf.byte 7 u j ∧
 t.mem (off base (P521Joint.KG.bits+j))=FastNaf.byte 7 u j) := by
 intro s t ts tt s' t' ⟨hp,ps,pt⟩ es et
 obtain ⟨_,_,xs,ks,is,js,zs,s19,sbytes⟩ := fixedLookup_ok hL hp.left hV hone ps.source hj ps.x19 ps.bytes ps.x2 hm0
 obtain ⟨_,_,xt,kt,it,jt,zt,t19,tbytes⟩ := fixedLookup_ok hL hp.right hV hone pt.source hj pt.x19 pt.bytes pt.x2 hm0
 obtain ⟨_,rfl⟩ := Exec.det es xs
 obtain ⟨_,rfl⟩ := Exec.det et xt
 have pub : Taint.AgreeS ["VG_P521_COMB"] (Taint.ofRegs [.x0,.x2]) s t := by
   refine ⟨⟨hp.sp,fun r hr=>?_⟩,?_⟩
   · simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
     rcases hr with rfl | rfl
     · exact hp.left.scr.x0.trans hp.right.scr.x0.symm
     · exact ps.x2.trans pt.x2.symm
   · intro n hn; rw [List.mem_singleton.mp hn]
     exact ps.source.symbol.trans pt.source.symbol.symm
 rw [zs] at js
 rw [zt] at jt
 have exy := (jointAffine_unique hC js).trans (jointAffine_unique hC jt).symm
 refine ⟨fixedLookup_ct _ _ _ _ _ _ trivial trivial pub es et,tmv C P521Joint.K.M.n base s',?_,s19,t19,sbytes,tbytes⟩
 apply hp.rebuild hL.win.lay ks kt (by decide) is it
 · intro x hx; exact List.mem_append.mp hx
 · intro x _ hx
   simp only [fixedCoords,List.mem_cons,List.not_mem_nil,or_false] at hx
   rcases hx with rfl | rfl | rfl
   · exact congrArg Prod.fst exy
   · exact congrArg Prod.snd exy
   · exact zs.trans zt.symm
end VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
end

end

-- Formerly `VerifiedGarbage/Proof/Ecdsa/Verify/AArch64/P521/JointFixedTiming.lean`, which only this module imported.
section

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass
open VG.Proof.Weierstrass.AArch64.PubNaf
open VG.Proof.Ed25519.AArch64 (read_x)

theorem fixedEntry_relCT {C : Curve} {base T : Addr} {G : Point C} {u j : Nat}
 {V : List Nat} {E : Nat → Fe C} (hL : NafLay P521Joint.K 8192) (hC : Law C)
 (hm : UnitMod C.p (2^(64*P521Joint.K.M.n)))
 (hV : ∀x∈[P521Joint.K.zero,p521.sl ONEP],x∈V) (hone : E (p521.sl ONEP)=1)
 (hj : j<577) (hm0 : FastNaf.magnitude 7 u j≠0) :
 RelCT isa (fun s t=>FieldPair P521Joint.K.M base 8192 C.p (·∈winSlots P521Joint.K) V E s t ∧
 FixedInput C base T G u j s ∧ FixedInput C base T G u j t)
 P521Joint.fixedEntry
 (fun s t=>∃ E',FieldPair P521Joint.K.M base 8192 C.p (·∈winSlots P521Joint.K) (fixedCoords++V) E' s t) := by
 change RelCT isa _ (.seq (.block P521Joint.fixedLoad) (Impl.Weierstrass.AArch64.Joint.signEntry fixedCfg)) _
 apply RelCT.seq (fixedLookup_relCT hL hC hV hone hj hm0)
 apply RelCT.exists_
 intro E'
 apply fixedSign_relCT hL hm _ hj
 intro x hx
 rcases (by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hx : x=P521Joint.K.zero ∨ x=P521Joint.K.E.y) with rfl | rfl
 · exact List.mem_append_right _ (hV _ (by simp))
 · exact List.mem_append_left _ (by simp [fixedCoords])

structure FixedDigitInput (C : Curve) (base T : Addr) (G : Point C) (u j : Nat) (s : State) : Prop where
 source : FixedGenerator C base 8192 G T s
 x19 : s.gpr .x19=BitVec.ofNat 64 j
 bytes : s.mem (off base (P521Joint.KG.bits+j))=FastNaf.byte 7 u j

theorem fixedDigit_relCT {C : Curve} {base T : Addr} {G : Point C} {u j : Nat}
 {E : Nat → Fe C} (hL : NafLay P521Joint.K 8192) (hC : Law C)
 (hm : UnitMod C.p (2^(64*P521Joint.K.M.n))) (hone : P521Joint.K.one<C.p)
 (h1 : E (p521.sl ONEP)=1) (hj : j<577)
 (checks : JacMixedChecks P521Joint.K P521Joint.K.R P521Joint.K.E P521Joint.K.D) :
 RelCT isa (fun s t=>FieldPair P521Joint.K.M base 8192 C.p (·∈winSlots P521Joint.K) (loopLive P521Joint.K) E s t ∧
 FixedDigitInput C base T G u j s ∧ FixedDigitInput C base T G u j t)
 P521Joint.fixedDigit
 (fun s t=>∃ E',FieldPair P521Joint.K.M base 8192 C.p (·∈winSlots P521Joint.K) (loopLive P521Joint.K) E' s t) := by
 let K := P521Joint.K
 have read : RelCT isa (fun s t=>FieldPair K.M base 8192 C.p (·∈winSlots K) (loopLive K) E s t ∧
   FixedDigitInput C base T G u j s ∧ FixedDigitInput C base T G u j t)
   (.block (Naf.digitRead P521Joint.KG))
   (fun s t=>FieldPair K.M base 8192 C.p (·∈winSlots K) (loopLive K) E s t ∧
     FixedInput C base T G u j s ∧ FixedInput C base T G u j t) := by
   intro s t ts tt s' t' ⟨hp,ps,pt⟩ es et
   obtain ⟨_,_,xs,vs,ks⟩ := nafRead_ok (K:=P521Joint.KG) hp.left.scr (by decide)
     (by change 3304+j<8192; omega) ps.x19 ps.bytes .x2
   obtain ⟨_,_,xt,vt,kt⟩ := nafRead_ok (K:=P521Joint.KG) hp.right.scr (by decide)
     (by change 3304+j<8192; omega) pt.x19 pt.bytes .x2
   obtain ⟨_,rfl⟩ := Exec.det es xs
   obtain ⟨_,rfl⟩ := Exec.det et xt
   have pub : AArch64.Taint.Agree (Taint.ofRegs [.x0,.x19]) s t := by
     refine ⟨hp.sp,fun r hr=>?_⟩
     simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
     rcases hr with rfl | rfl
     · exact hp.left.scr.x0.trans hp.right.scr.x0.symm
     · exact ps.x19.trans pt.x19.symm
   have kp {a b : State} (k : VG.Proof.Ed25519.AArch64.Keeps [.x2,.x16] a b) : ProgKeep K.M base [] a b := keeps_prog k (by decide)
   refine ⟨fixedRead_ct _ _ _ _ _ _ trivial trivial pub es et,
     ⟨hp.left.of_keeps ks (by decide),hp.right.of_keeps kt (by decide),ks.sp.trans (hp.sp.trans kt.sp.symm)⟩,
     ⟨ps.source.keep (kp ks) (Exec.syms es) (by simp) hp.left.mod.tmp,(ks.gpr _ (by decide)).trans ps.x19,?_,vs⟩,
     ⟨pt.source.keep (kp kt) (Exec.syms et) (by simp) hp.right.mod.tmp,(kt.gpr _ (by decide)).trans pt.x19,?_,vt⟩⟩
   · rw [ks.mem]; exact ps.bytes
   · rw [kt.mem]; exact pt.bytes
 rw [P521Joint.fixedDigit]
 apply RelCT.seq read
 apply RelCT.ite
 · intro s t ⟨_,ps,pt⟩
   change some (s.read .x .x2 != 0)=some (t.read .x .x2 != 0)
   rw [read_x,read_x,ps.x2,pt.x2]
 · intro s t ts tt s' t' ⟨⟨hp,ps,pt⟩,hn⟩ es et
   have nz : FastNaf.magnitude 7 u j≠0 := by
     intro hz
     have hb := (FastNaf.byte_zero_iff 7 u j).mpr hz
     change some (s.read .x .x2 != 0)=some true at hn
     rw [read_x,ps.x2,hb] at hn
     change some false=some true at hn
     cases hn
   have entry := fixedEntry_relCT (base:=base) (T:=T) (G:=G) (V:=loopLive K) (E:=E) hL hC hm (by decide) h1 hj nz
   have sum (F : Nat → Fe C) : RelCT isa
     (FieldPair K.M base 8192 C.p (·∈winSlots K) (fixedCoords++loopLive K) F)
     (.seq (Jacobian.jacMixedAdd K K.R K.E K.D) (.block (copyPt 9 K.R K.D)))
     (fun s t=>∃ E',FieldPair K.M base 8192 C.p (·∈winSlots K) (loopLive K) E' s t) := by
     obtain ⟨_,_,_,_,_,apart,_,_⟩ := rcbApart_naf hL.win
     apply RelCT.seq (jacMixedAddB_relCT hL.win.lay hL.al.al (by decide) hm apart (by decide)
       (hL.al.low (by decide)) (by decide) hone checks)
     apply RelCT.exists_
     intro F'
     have cp := copyPoint_relCT (base:=base) (E:=F') hL.win.lay hL.al.al (o:=K.R) (q:=K.D)
       (by decide) (V:=jacCoords K.D++(fixedCoords++loopLive K))
       (by intro x hx; exact List.mem_append_left _ hx) fixedCopy_ct
     exact cp.mono (fun _ _ h=>h) (fun _ _ h=>⟨_,h.sub (by decide)⟩)
   exact (RelCT.seq entry (RelCT.exists_ sum)) _ _ _ _ _ _ ⟨hp,ps,pt⟩ es et
 · exact RelCT.block_nil (fun _ _ h=>⟨E,h.1.1⟩)
end VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
end

end

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 VG.Impl.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass.AArch64.PubNaf
open Spec.Weierstrass

/-- Public generator inputs retained throughout the joint loop. -/
structure GeneratorInput (C : Curve) (base T : Addr) (G : Point C) (u : Nat) (s : State) : Prop where
 source : FixedGenerator C base 8192 G T s
 bytes : ∀j<577,s.mem (off base (P521Joint.KG.bits+j))=FastNaf.byte 7 u j
 one : tmv C P521Joint.K.M.n base s (p521.sl ONEP)=1

theorem GeneratorInput.rebase {C : Curve} {base T : Addr} {G : Point C} {u : Nat} {s t : State}
 (h : GeneratorInput C base T G u s)
 (hu : Unch base (winW P521Joint.K++cacheW P521Joint.K) s.mem t.mem)
 (hr : t.rd=s.rd) (hw : t.wr=s.wr) (hy : t.syms=s.syms) :
 GeneratorInput C base T G u t := by
 refine ⟨h.source.unch hu (by decide) hr hw hy,?_,?_⟩
 · intro j hj
   rw [hu.byte (by intro w hw; have ha:=generator_apart w hw; omega)
    (by change 3304+j<2^64; omega)]
   exact h.bytes j hj
 · unfold tmv
   rw [hu.wordsVal (by decide) (by decide)]
   exact h.one

theorem GeneratorInput.current {C : Curve} {base T : Addr} {G P A : Point C} {u j : Nat} {s₀ s : State}
 (h : GeneratorInput C base T G u s₀) (hj : j<577) (sy : s.syms=s₀.syms)
 (hs : JointDigitPost P521Joint.K C base 8192 P s₀ s j A) :
 FixedDigitInput C base T G u j s ∧ tmv C P521Joint.K.M.n base s (p521.sl ONEP)=1 := by
 refine ⟨⟨h.source.unch hs.st.unch (by decide) hs.st.keep.rd hs.st.keep.wr sy,hs.x19,?_⟩,?_⟩
 · rw [hs.st.unch.byte (by
     intro w hw
     have ha:=generator_apart w (List.mem_append_left _ hw)
     omega) (by change 3304+j<2^64; omega)]
   exact h.bytes j hj
 · unfold tmv
   rw [hs.st.unch.wordsVal (by decide) (by decide)]
   exact h.one

def JointRelation (C : Curve) (base : Addr) (P G : Point C) (u v j : Nat) (s₀ t₀ s t : State) : Prop :=
 (∃E,FieldPair P521Joint.K.M base 8192 C.p (·∈winSlots P521Joint.K) (loopLive P521Joint.K) E s t) ∧
 JointDigitPost P521Joint.K C base 8192 P s₀ s j (jointPoint G P u v j) ∧
 JointDigitPost P521Joint.K C base 8192 P t₀ t j (jointPoint G P u v j) ∧
 s.syms=s₀.syms ∧ t.syms=t₀.syms

theorem jointStep_relCT {C : Curve} {base T : Addr} {P G : Point C} {s₀ t₀ : State} {u v j : Nat}
 (hL : NafLay P521Joint.K 8192) (hp : UnitMod C.p (2^(64*P521Joint.K.M.n))) (hC : Law C)
 (hM3 : AM3 C) (hone : P521Joint.K.one<C.p) (hP : onCurve C P=true) (hG : onCurve C G=true)
 (hF₁ : NafFixed P521Joint.K C base s₀ P v) (hF₂ : NafFixed P521Joint.K C base t₀ P v)
 (g₁ : GeneratorInput C base T G u s₀) (g₂ : GeneratorInput C base T G u t₀)
 (checks : StepChecks P521Joint.K)
 (mixed : JacMixedChecks P521Joint.K P521Joint.K.R P521Joint.K.E P521Joint.K.D)
 (hj : j<576) :
 RelCT isa (JointRelation C base P G u v (j+1) s₀ t₀) P521Joint.step
  (JointRelation C base P G u v j s₀ t₀) := by
 intro s t ts tt s' t' ⟨pair,hs,ht,sys,syt⟩ es et
 have fs:=fixedStep_of_source hL hp hC hM3 hone hG hF₁ g₁.source g₁.bytes g₁.one
 have ft:=fixedStep_of_source hL hp hC hM3 hone hG hF₂ g₂.source g₂.bytes g₂.one
 obtain ⟨_,_,exs,postS⟩:=step_ok hL hp hC hM3 hone hP hG hF₁ fs hj sys hs
 obtain ⟨_,_,ext,postT⟩:=step_ok hL hp hC hM3 hone hP hG hF₂ ft hj syt ht
 obtain ⟨_,rfl⟩:=Exec.det es exs
 obtain ⟨_,rfl⟩:=Exec.det et ext
 have result : ts=tt ∧ ∃E,FieldPair P521Joint.K.M base 8192 C.p (·∈winSlots P521Joint.K)
   (loopLive P521Joint.K) E s' t' := by
  cases es with
  | seq ds es => cases es with
    | seq dbs es => cases es with
      | seq ps gs =>
       cases et with
       | seq dt et => cases et with
         | seq dbt et => cases et with
           | seq pt gt =>
            have eps : Exec isa (PubNaf.step P521Joint.K) _ _ _ := .seq ds (.seq dbs ps)
            have ept : Exec isa (PubNaf.step P521Joint.K) _ _ _ := .seq dt (.seq dbt pt)
            obtain ⟨he,E,hpair⟩:=stepRaw_relCT hL hp hone checks hF₁ hF₂ (j:=j) (by change j<577; omega)
             _ _ _ _ _ _ ⟨pair,hs.st,ht.st,hs.cache,ht.cache,hs.x19,ht.x19⟩ eps ept
            have hcA:=jointPoint_curve hC hG hP u v (j+1)
            obtain ⟨_,_,e1,h1⟩:=peerStep_ok hL hp hC hM3 hone hP hcA hF₁ hj hs
            obtain ⟨_,_,e2,h2⟩:=peerStep_ok hL hp hC hM3 hone hP hcA hF₂ hj ht
            obtain ⟨_,rfl⟩:=Exec.det eps e1
            obtain ⟨_,rfl⟩:=Exec.det ept e2
            have a:=g₁.current (by omega) ((Exec.syms eps).trans sys) h1
            have b:=g₂.current (by omega) ((Exec.syms ept).trans syt) h2
            have ev : E (p521.sl ONEP)=1 := by
             rw [←hpair.left.val _ (by decide)]
             exact a.2
            obtain ⟨hg,res⟩:=fixedDigit_relCT hL hC hp hone ev (by omega) mixed
             _ _ _ _ _ _ ⟨hpair,a.1,b.1⟩ gs gt
            exact ⟨by simpa only [List.append_assoc] using congrArg₂ (·++·) he hg,res⟩
 exact ⟨result.1,result.2,postS,postT,(Exec.syms es).trans sys,(Exec.syms et).trans syt⟩
end VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
