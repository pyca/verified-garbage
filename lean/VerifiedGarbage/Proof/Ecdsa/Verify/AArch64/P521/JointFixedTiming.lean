module
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedSignTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedTimingB
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.DigitTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedLookupTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedChecks
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeArithmetic
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedTiming
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
