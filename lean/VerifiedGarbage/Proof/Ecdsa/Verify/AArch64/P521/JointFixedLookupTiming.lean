module
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedChecks
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedLookupTiming
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
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
