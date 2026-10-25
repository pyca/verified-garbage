module
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointFixedSignTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedTimingB
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.DigitTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointFixedLookupTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointFixedChecks
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeArithmetic
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointRead9
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointRead
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
