module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.JointDigit
public import VerifiedGarbage.Proof.Weierstrass.Joint
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WinJStep
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointFixedEntry
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.DigitTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedTiming

import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointFixedBridge
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.StepDTiming
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointFixedChecks
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointRead9
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedLookupTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTableTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedTimingB
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeArithmetic
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointRead

-- Formerly `VerifiedGarbage/Proof/Ecdsa/Verify/AArch64/P384/JointFixedSignTiming.lean`, which only this module imported.
section

section
namespace VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass
open VG.Proof.Weierstrass.AArch64.PubNaf
open VG.Proof.Ed25519.AArch64 (read_x)

theorem fixedSign_relCT {C : Curve} {base : Addr} {u j : Nat} {V : List Nat} {E : Nat → Fe C}
 (hL : NafLay P384Joint.K 8192) (hm : UnitMod C.p (2^(64*P384Joint.K.M.n)))
 (hV : ∀x∈[P384Joint.K.zero,P384Joint.K.E.y],x∈V) (hj : j<385) :
 RelCT isa (fun s t=>FieldPair P384Joint.K.M base 8192 C.p (·∈winSlots P384Joint.K) V E s t ∧
 s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j ∧
 GBytes base u j s ∧ GBytes base u j t)
 (Impl.Weierstrass.AArch64.Joint.signEntry P384Joint.cfg)
 (fun s t=>∃ E',FieldPair P384Joint.K.M base 8192 C.p (·∈winSlots P384Joint.K) V E' s t) := by
 have sign : RelCT isa (fun s t=>FieldPair P384Joint.K.M base 8192 C.p (·∈winSlots P384Joint.K) V E s t ∧
   s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j ∧
   GBytes base u j s ∧ GBytes base u j t)
   (.block (Joint.signRead P384Joint.cfg))
   (fun s t=>FieldPair P384Joint.K.M base 8192 C.p (·∈winSlots P384Joint.K) V E s t ∧
     s.gpr .x3=BitVec.ofNat 64 (FastNaf.negative 9 u j).toNat ∧
     t.gpr .x3=BitVec.ofNat 64 (FastNaf.negative 9 u j).toNat) := by
   intro s t ts tt s' t' ⟨hp,s19,t19,sb,tb⟩ es et
   obtain ⟨_,_,xs,vs,ks⟩ := signRead9_ok cfg_gw hp.left.scr (by decide)
     (by change 3152+2*j+2≤8192; omega) s19 sb.hi
   obtain ⟨_,_,xt,vt,kt⟩ := signRead9_ok cfg_gw hp.right.scr (by decide)
     (by change 3152+2*j+2≤8192; omega) t19 tb.hi
   obtain ⟨_,rfl⟩ := Exec.det es xs
   obtain ⟨_,rfl⟩ := Exec.det et xt
   have pub : AArch64.Taint.Agree (Taint.ofRegs [.x0,.x19]) s t := by
     refine ⟨hp.sp,fun r hr=>?_⟩
     simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
     rcases hr with rfl | rfl
     · exact hp.left.scr.x0.trans hp.right.scr.x0.symm
     · exact s19.trans t19.symm
   exact ⟨fixedSign_ct _ _ _ _ _ _ trivial trivial pub es et,
     ⟨hp.left.of_keeps ks (by decide),hp.right.of_keeps kt (by decide),ks.sp.trans (hp.sp.trans kt.sp.symm)⟩,vs,vt⟩
 change RelCT isa _ (.seq (.block (Joint.signRead P384Joint.cfg)) _) _
 apply RelCT.seq sign
 apply RelCT.ite
 · intro s t ⟨_,s3,t3⟩
   change some (s.read .x .x3 != 0)=some (t.read .x .x3 != 0)
   rw [read_x,read_x,s3,t3]
 · have neg : RelCT isa (FieldPair P384Joint.K.M base 8192 C.p (·∈winSlots P384Joint.K) V E)
     (.block (Impl.Mont.AArch64.sub P384Joint.K.M P384Joint.K.E.y P384Joint.K.zero P384Joint.K.E.y))
     (FieldPair P384Joint.K.M base 8192 C.p (·∈winSlots P384Joint.K)
       (validAfter [FOp.sub P384Joint.K.E.y P384Joint.K.zero P384Joint.K.E.y] V)
       (runOps [FOp.sub P384Joint.K.E.y P384Joint.K.zero P384Joint.K.E.y] E)) := by
     apply fieldWP_relCT fixedNeg_ct
     intro s hs
     have w := fprog_ok hL.win.lay hL.al.al hm [FOp.sub P384Joint.K.E.y P384Joint.K.zero P384Joint.K.E.y]
       hs (by decide) (by simp [readsOk, FOp.ins, hV P384Joint.K.zero (by simp), hV P384Joint.K.E.y (by simp)])
     simp only [fprog,List.flatMap_cons,List.flatMap_nil,List.append_nil,opCode] at w
     exact WP.mono w fun t ⟨kt,it⟩=>⟨it,kt.sp⟩
   exact neg.mono (fun _ _ h=>h.1.1) (fun _ _ h=>⟨_,h.sub (fun _ hx=>List.mem_cons_of_mem _ hx)⟩)
 · exact RelCT.block_nil (fun _ _ h=>⟨_,h.1.1⟩)
end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
end

end

-- Formerly `VerifiedGarbage/Proof/Ecdsa/Verify/AArch64/P384/JointFixedLookupTiming.lean`, which only this module imported.
section

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass
open VG.Proof.Weierstrass.AArch64.PubNaf

structure FixedInput (C : Curve) (base T : Addr) (G : Point C) (u j : Nat) (s : State) : Prop where
 source : FixedGenerator C base 8192 G T s
 x19 : s.gpr .x19=BitVec.ofNat 64 j
 bytes : GBytes base u j s
 x2 : s.gpr .x2=(FastNaf.wbyte u (2*j)).setWidth 64
 x3 : s.gpr .x3=(FastNaf.wbyte u (2*j+1)).setWidth 64

theorem fixedLookup_relCT {C : Curve} {base T : Addr} {G : Point C} {u j : Nat}
 {V : List Nat} {E : Nat → Fe C} (hL : NafLay P384Joint.K 8192) (hC : Law C)
 (hV : ∀x∈[P384Joint.K.zero,p384.sl ONEP],x∈V) (hone : E (p384.sl ONEP)=1)
 (hj : j<385) (hm0 : FastNaf.magnitude 9 u j≠0) :
 RelCT isa (fun s t=>FieldPair P384Joint.K.M base 8192 C.p (·∈winSlots P384Joint.K) V E s t ∧
 FixedInput C base T G u j s ∧ FixedInput C base T G u j t)
 (.block P384Joint.fixedLoad)
 (fun s t=>∃ E',FieldPair P384Joint.K.M base 8192 C.p (·∈winSlots P384Joint.K) (fixedCoords++V) E' s t ∧
 s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j ∧
 GBytes base u j s ∧ GBytes base u j t) := by
 intro s t ts tt s' t' ⟨hp,ps,pt⟩ es et
 obtain ⟨_,_,xs,ks,is,js,zs,s19,sbytes⟩ := fixedLookup_ok hL hp.left hV hone ps.source hj ps.x19 ps.bytes ps.x2 ps.x3 hm0
 obtain ⟨_,_,xt,kt,it,jt,zt,t19,tbytes⟩ := fixedLookup_ok hL hp.right hV hone pt.source hj pt.x19 pt.bytes pt.x2 pt.x3 hm0
 obtain ⟨_,rfl⟩ := Exec.det es xs
 obtain ⟨_,rfl⟩ := Exec.det et xt
 have pub : Taint.AgreeS ["VG_P384_GTAB"] (Taint.ofRegs [.x0,.x2,.x3]) s t := by
   refine ⟨⟨hp.sp,fun r hr=>?_⟩,?_⟩
   · simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
     rcases hr with rfl | rfl | rfl
     · exact hp.left.scr.x0.trans hp.right.scr.x0.symm
     · exact ps.x2.trans pt.x2.symm
     · exact ps.x3.trans pt.x3.symm
   · intro n hn; rw [List.mem_singleton.mp hn]
     exact ps.source.symbol.trans pt.source.symbol.symm
 rw [zs] at js
 rw [zt] at jt
 have exy := (jointAffine_unique hC js).trans (jointAffine_unique hC jt).symm
 refine ⟨fixedLookup_ct _ _ _ _ _ _ trivial trivial pub es et,tmv C P384Joint.K.M.n base s',?_,s19,t19,sbytes,tbytes⟩
 apply hp.rebuild hL.win.lay ks kt (by decide) is it
 · intro x hx; exact List.mem_append.mp hx
 · intro x _ hx
   simp only [fixedCoords,List.mem_cons,List.not_mem_nil,or_false] at hx
   rcases hx with rfl | rfl | rfl
   · exact congrArg Prod.fst exy
   · exact congrArg Prod.snd exy
   · exact zs.trans zt.symm
end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
end

end

-- Formerly `VerifiedGarbage/Proof/Ecdsa/Verify/AArch64/P384/JointFixedTiming.lean`, which only this module imported.
section

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass
open VG.Proof.Weierstrass.AArch64.PubNaf
open VG.Proof.Ed25519.AArch64 (read_x)

theorem fixedEntry_relCT {C : Curve} {base T : Addr} {G : Point C} {u j : Nat}
 {V : List Nat} {E : Nat → Fe C} (hL : NafLay P384Joint.K 8192) (hC : Law C)
 (hm : UnitMod C.p (2^(64*P384Joint.K.M.n)))
 (hV : ∀x∈[P384Joint.K.zero,p384.sl ONEP],x∈V) (hone : E (p384.sl ONEP)=1)
 (hj : j<385) (hm0 : FastNaf.magnitude 9 u j≠0) :
 RelCT isa (fun s t=>FieldPair P384Joint.K.M base 8192 C.p (·∈winSlots P384Joint.K) V E s t ∧
 FixedInput C base T G u j s ∧ FixedInput C base T G u j t)
 P384Joint.fixedEntry
 (fun s t=>∃ E',FieldPair P384Joint.K.M base 8192 C.p (·∈winSlots P384Joint.K) (fixedCoords++V) E' s t) := by
 change RelCT isa _ (.seq (.block P384Joint.fixedLoad) (Impl.Weierstrass.AArch64.Joint.signEntry P384Joint.cfg)) _
 apply RelCT.seq (fixedLookup_relCT hL hC hV hone hj hm0)
 apply RelCT.exists_
 intro E'
 apply fixedSign_relCT hL hm _ hj
 intro x hx
 rcases (by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hx : x=P384Joint.K.zero ∨ x=P384Joint.K.E.y) with rfl | rfl
 · exact List.mem_append_right _ (hV _ (by simp))
 · exact List.mem_append_left _ (by simp [fixedCoords])

structure FixedDigitInput (C : Curve) (base T : Addr) (G : Point C) (u j : Nat) (s : State) : Prop where
 source : FixedGenerator C base 8192 G T s
 x19 : s.gpr .x19=BitVec.ofNat 64 j
 bytes : GBytes base u j s

theorem fixedDigit_relCT {C : Curve} {base T : Addr} {G : Point C} {u j : Nat}
 {E : Nat → Fe C} (hL : NafLay P384Joint.K 8192) (hC : Law C)
 (hm : UnitMod C.p (2^(64*P384Joint.K.M.n))) (hone : P384Joint.K.one<C.p)
 (h1 : E (p384.sl ONEP)=1) (hj : j<385)
 (checks : JacMixedChecks P384Joint.K P384Joint.K.R P384Joint.K.E P384Joint.K.D) :
 RelCT isa (fun s t=>FieldPair P384Joint.K.M base 8192 C.p (·∈winSlots P384Joint.K) (loopLive P384Joint.K) E s t ∧
 FixedDigitInput C base T G u j s ∧ FixedDigitInput C base T G u j t)
 P384Joint.fixedDigit
 (fun s t=>∃ E',FieldPair P384Joint.K.M base 8192 C.p (·∈winSlots P384Joint.K) (loopLive P384Joint.K) E' s t) := by
 let K := P384Joint.K
 have read : RelCT isa (fun s t=>FieldPair K.M base 8192 C.p (·∈winSlots K) (loopLive K) E s t ∧
   FixedDigitInput C base T G u j s ∧ FixedDigitInput C base T G u j t)
   (.block (Joint.fixedRead P384Joint.cfg))
   (fun s t=>FieldPair K.M base 8192 C.p (·∈winSlots K) (loopLive K) E s t ∧
     FixedInput C base T G u j s ∧ FixedInput C base T G u j t) := by
   intro s t ts tt s' t' ⟨hp,ps,pt⟩ es et
   obtain ⟨_,_,xs,vs,_,vs3,ks⟩ := fixedRead9_ok cfg_gw hp.left.scr (by decide)
     (by change 3152+2*j+2≤8192; omega) ps.x19 ps.bytes.lo ps.bytes.hi
   obtain ⟨_,_,xt,vt,_,vt3,kt⟩ := fixedRead9_ok cfg_gw hp.right.scr (by decide)
     (by change 3152+2*j+2≤8192; omega) pt.x19 pt.bytes.lo pt.bytes.hi
   obtain ⟨_,rfl⟩ := Exec.det es xs
   obtain ⟨_,rfl⟩ := Exec.det et xt
   have pub : AArch64.Taint.Agree (Taint.ofRegs [.x0,.x19]) s t := by
     refine ⟨hp.sp,fun r hr=>?_⟩
     simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
     rcases hr with rfl | rfl
     · exact hp.left.scr.x0.trans hp.right.scr.x0.symm
     · exact ps.x19.trans pt.x19.symm
   have kp {a b : State} (k : VG.Proof.Ed25519.AArch64.Keeps [.x2,.x3,.x16] a b) : ProgKeep K.M base [] a b := keeps_prog k (by decide)
   refine ⟨fixedRead_ct _ _ _ _ _ _ trivial trivial pub es et,
     ⟨hp.left.of_keeps ks (by decide),hp.right.of_keeps kt (by decide),ks.sp.trans (hp.sp.trans kt.sp.symm)⟩,
     ⟨ps.source.keep (kp ks) (Exec.syms es) (by simp) hp.left.mod.tmp,(ks.gpr _ (by decide)).trans ps.x19,?_,vs,vs3⟩,
     ⟨pt.source.keep (kp kt) (Exec.syms et) (by simp) hp.right.mod.tmp,(kt.gpr _ (by decide)).trans pt.x19,?_,vt,vt3⟩⟩
   · exact ⟨by rw [ks.mem]; exact ps.bytes.lo,by rw [ks.mem]; exact ps.bytes.hi⟩
   · exact ⟨by rw [kt.mem]; exact pt.bytes.lo,by rw [kt.mem]; exact pt.bytes.hi⟩
 rw [P384Joint.fixedDigit]
 apply RelCT.seq read
 apply RelCT.ite
 · intro s t ⟨_,ps,pt⟩
   change some (s.read .x .x2 != 0)=some (t.read .x .x2 != 0)
   rw [read_x,read_x,ps.x2,pt.x2]
 · intro s t ts tt s' t' ⟨⟨hp,ps,pt⟩,hn⟩ es et
   have nz : FastNaf.magnitude 9 u j≠0 := by
     intro hz
     have hb := (jointGCell_zero_iff (c:=P384Joint.cfg) (Or.inr rfl) u j).mpr (by rw [cfg_gw]; exact hz)
     rw [jointGCell,ite_eq_left cfg_gw] at hb
     change some (s.read .x .x2 != 0)=some true at hn
     rw [read_x,ps.x2,hb] at hn
     change some false=some true at hn
     cases hn
   have entry := fixedEntry_relCT (base:=base) (T:=T) (G:=G) (V:=loopLive K) (E:=E) hL hC hm (by decide) h1 hj nz
   have sum (F : Nat → Fe C) : RelCT isa
     (FieldPair K.M base 8192 C.p (·∈winSlots K) (fixedCoords++loopLive K) F)
     (.seq (Jacobian.jacMixedAdd K K.R K.E K.D) (.block (copyPt 6 K.R K.D)))
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
end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
end

end

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 VG.Impl.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass.AArch64.PubNaf
open Spec.Weierstrass

/-- Public generator inputs retained throughout the joint loop. -/
structure GeneratorInput (C : Curve) (base T : Addr) (G : Point C) (u : Nat) (s : State) : Prop where
 source : FixedGenerator C base 8192 G T s
 bytes : ∀j<770,s.mem (off base (P384Joint.KG.bits+j))=FastNaf.wbyte u j
 one : tmv C P384Joint.K.M.n base s (p384.sl ONEP)=1

theorem GeneratorInput.rebase {C : Curve} {base T : Addr} {G : Point C} {u : Nat} {s t : State}
 (h : GeneratorInput C base T G u s)
 (hu : Unch base (winW P384Joint.K++cacheW P384Joint.K) s.mem t.mem)
 (hr : t.rd=s.rd) (hw : t.wr=s.wr) (hy : t.syms=s.syms) :
 GeneratorInput C base T G u t := by
 refine ⟨h.source.unch hu (by decide) hr hw hy,?_,?_⟩
 · intro j hj
   have hb : P384Joint.KG.bits=3152 := rfl
   rw [hu.byte (by intro w hw; have ha:=generator_apart w hw; omega) (by omega)]
   exact h.bytes j hj
 · unfold tmv
   rw [hu.wordsVal (by decide) (by decide)]
   exact h.one

theorem GeneratorInput.current {C : Curve} {base T : Addr} {G P A : Point C} {u j : Nat} {s₀ s : State}
 (h : GeneratorInput C base T G u s₀) (hj : j<385) (sy : s.syms=s₀.syms)
 (hs : JointDigitPost P384Joint.K C base 8192 P s₀ s j A) :
 FixedDigitInput C base T G u j s ∧ tmv C P384Joint.K.M.n base s (p384.sl ONEP)=1 := by
 refine ⟨⟨h.source.unch hs.st.unch (by decide) hs.st.keep.rd hs.st.keep.wr sy,hs.x19,?_⟩,?_⟩
 · exact GBytes.of_unch hs.st.unch (fun w hw => generator_apart w (List.mem_append_left _ hw)) h.bytes hj
 · unfold tmv
   rw [hs.st.unch.wordsVal (by decide) (by decide)]
   exact h.one

def JointRelation (C : Curve) (base : Addr) (P G : Point C) (u v j : Nat) (s₀ t₀ s t : State) : Prop :=
 (∃E,FieldPair P384Joint.K.M base 8192 C.p (·∈winSlots P384Joint.K) (loopLive P384Joint.K) E s t) ∧
 JointDigitPost P384Joint.K C base 8192 P s₀ s j (jointPoint G P u v j 9) ∧
 JointDigitPost P384Joint.K C base 8192 P t₀ t j (jointPoint G P u v j 9) ∧
 s.syms=s₀.syms ∧ t.syms=t₀.syms

theorem jointStep_relCT {C : Curve} {base T : Addr} {P G : Point C} {s₀ t₀ : State} {u v j : Nat}
 (hL : NafLay P384Joint.K 8192) (hp : UnitMod C.p (2^(64*P384Joint.K.M.n))) (hC : Law C)
 (hM3 : AM3 C) (hone : P384Joint.K.one<C.p) (hP : onCurve C P=true) (hG : onCurve C G=true)
 (hF₁ : NafFixed P384Joint.K C base s₀ P v) (hF₂ : NafFixed P384Joint.K C base t₀ P v)
 (g₁ : GeneratorInput C base T G u s₀) (g₂ : GeneratorInput C base T G u t₀)
 (checks : StepChecks P384Joint.K)
 (hD : DblSpec P384Joint.K C base 8192 P384Joint.double P384Joint.K.R P384Joint.K.D (dblVR P384Joint.K))
 (hct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0])) P384Joint.double)
 (mixed : JacMixedChecks P384Joint.K P384Joint.K.R P384Joint.K.E P384Joint.K.D)
 (hj : j<384) :
 RelCT isa (JointRelation C base P G u v (j+1) s₀ t₀) P384Joint.step
  (JointRelation C base P G u v j s₀ t₀) := by
 intro s t ts tt s' t' ⟨pair,hs,ht,sys,syt⟩ es et
 have fs:=fixedStep_of_source hL hp hC hM3 hone hG hF₁ g₁.source g₁.bytes g₁.one
 have ft:=fixedStep_of_source hL hp hC hM3 hone hG hF₂ g₂.source g₂.bytes g₂.one
 obtain ⟨_,_,exs,postS⟩:=step_ok hL hp hC hM3 hone hP hG hD hF₁ fs hj sys hs
 obtain ⟨_,_,ext,postT⟩:=step_ok hL hp hC hM3 hone hP hG hD hF₂ ft hj syt ht
 obtain ⟨_,rfl⟩:=Exec.det es exs
 obtain ⟨_,rfl⟩:=Exec.det et ext
 have result : ts=tt ∧ ∃E,FieldPair P384Joint.K.M base 8192 C.p (·∈winSlots P384Joint.K)
   (loopLive P384Joint.K) E s' t' := by
  cases es with
  | seq ds es => cases es with
    | seq dbs es => cases es with
      | seq ps gs =>
       cases et with
       | seq dt et => cases et with
         | seq dbt et => cases et with
           | seq pt gt =>
            have eps : Exec isa (PubNaf.stepD P384Joint.K P384Joint.double) _ _ _ := .seq ds (.seq dbs ps)
            have ept : Exec isa (PubNaf.stepD P384Joint.K P384Joint.double) _ _ _ := .seq dt (.seq dbt pt)
            obtain ⟨he,E,hpair⟩:=stepDRaw_relCT hL hp hone checks hD hct hF₁ hF₂ (j:=j) (by change j<385; omega)
             _ _ _ _ _ _ ⟨pair,hs.st,ht.st,hs.cache,ht.cache,hs.x19,ht.x19⟩ eps ept
            have hcA:=jointPoint_curve hC hG hP u v (j+1) 9
            obtain ⟨_,_,e1,h1⟩:=peerStepD_ok hL hp hC hM3 hone hP hcA hD hF₁ hj hs
            obtain ⟨_,_,e2,h2⟩:=peerStepD_ok hL hp hC hM3 hone hP hcA hD hF₂ hj ht
            obtain ⟨_,rfl⟩:=Exec.det eps e1
            obtain ⟨_,rfl⟩:=Exec.det ept e2
            have a:=g₁.current (by omega) ((Exec.syms eps).trans sys) h1
            have b:=g₂.current (by omega) ((Exec.syms ept).trans syt) h2
            have ev : E (p384.sl ONEP)=1 := by
             rw [←hpair.left.val _ (by decide)]
             exact a.2
            obtain ⟨hg,res⟩:=fixedDigit_relCT hL hC hp hone ev (by omega) mixed
             _ _ _ _ _ _ ⟨hpair,a.1,b.1⟩ gs gt
            exact ⟨by simpa only [List.append_assoc] using congrArg₂ (·++·) he hg,res⟩
 exact ⟨result.1,result.2,postS,postT,(Exec.syms es).trans sys,(Exec.syms et).trans syt⟩
end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
