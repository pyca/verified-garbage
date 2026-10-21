module
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointFixedEntry
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointFixedChecks
import VerifiedGarbage.Proof.Ed25519.AArch64.Mem
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointRead9
@[expose] public section
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
