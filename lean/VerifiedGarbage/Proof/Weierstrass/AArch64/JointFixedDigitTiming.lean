module

public import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointEntryTiming
public import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeArithmetic
public import VerifiedGarbage.Impl.Weierstrass.AArch64.CachedJac
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionArithmetic
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Rotate
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.FoldOk
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedDigit
public import VerifiedGarbage.Proof.Weierstrass.MulContract
import VerifiedGarbage.Impl.Weierstrass.AArch64.CachedJac
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionArithmetic
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Rotate
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.FoldOk
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedDigit
import VerifiedGarbage.Proof.Weierstrass.MulContract
public import VerifiedGarbage.Impl.Mont.Mod
public import VerifiedGarbage.Impl.Weierstrass.AArch64.Comb
public import VerifiedGarbage.Impl.Weierstrass.AArch64.Joint
public import VerifiedGarbage.Impl.Weierstrass.Slots
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixed
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedTiming
public import VerifiedGarbage.Proof.Weierstrass.CombLay
public import VerifiedGarbage.Proof.Weierstrass.Env
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.TCB.AArch64.Isa

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (read_x)

local macro "jslots" : tactic => `(tactic| plain_simp_names (simp only [jointSlots,jointLive,jointWork,
                   jacWinSlots,nafLive,winRo,winOther,rcbW,rcbR,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; grind))

theorem jointFixedSum_relCT (certs : Forward.Arithmetic.Cases)
    {c : Joint.Cfg} {C : Curve} {base : Addr} {size : Nat} {E : Nat → Fe C}
    (hL : JointFixedLayout c size) (hm : UnitMod C.p (2^(64*c.K.M.n)))
    (hsize : 8192≤size) (hOne : c.K.one<C.p) (hc : JointFixedChecks c) :
    RelCT isa (FieldPair c.K.M base size C.p (·∈jointSlots c)
      ([c.K.E.x,c.K.E.y,c.K.E.z]++jointLive c) E)
      (.seq (Joint.mixedAdd c.K c.K.R c.K.E c.K.D) (.block (copyPt 4 c.K.R c.K.D)))
      (fun s t => ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E' s t) := by
  have sl : ∀ x∈rcbW c.K.S c.K.D++rcbR c.K.S c.K.R c.K.E,x∈jointSlots c := by intro x hx; jslots
  have vr : ∀ x∈rcbR c.K.S c.K.R c.K.E,x∈[c.K.E.x,c.K.E.y,c.K.E.z]++jointLive c := by intro x hx; jslots
  apply RelCT.seq (jointMixedAdd_relCT certs hL.layout.lay hL.layout.aligned (callOf_small (Nat.le_of_eq hL.layout.n)) hm hsize hL.addApart sl vr hOne hc.mixed)
  apply RelCT.exists_
  intro E'
  have cp := copyPoint_relCT (base:=base) (E:=E') hL.layout.lay hL.layout.aligned
    (o:=c.K.R) (q:=c.K.D) (by intro x hx; jslots)
    (V:=[c.K.D.x,c.K.D.y,c.K.D.z]++([c.K.E.x,c.K.E.y,c.K.E.z]++jointLive c))
    (by intro x hx; exact List.mem_append_left _ hx) (by rw [hL.layout.n]; exact hc.copy)
  rw [hL.layout.n] at cp
  exact cp.mono (fun _ _ h => h) (fun _ _ h => ⟨_,h.sub (fun x hx => by simp [hx])⟩)

theorem jointFixedDigit_relCT (certs : Forward.Arithmetic.Cases)
    {c : Joint.Cfg} {C : Curve} {base T : Addr} {size u v j : Nat}
    {G Q A : Point C} {E : Nat → Fe C} (hL : JointFixedLayout c size) (hC : Law C)
    (hm : UnitMod C.p (2^(64*c.K.M.n))) (hsize : 8192≤size)
    (hOne : c.K.one<C.p) (hj : j<257) (hc : JointFixedChecks c) :
    RelCT isa (fun s t =>
      FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E s t ∧
      JointCore c C base size Q u v (JointGenerator c C base size G T) A s ∧
      JointCore c C base size Q u v (JointGenerator c C base size G T) A t ∧
      s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j)
      (Joint.fixedDigit c (Joint.mixedAdd c.K c.K.R c.K.E c.K.D))
      (fun s t => ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E' s t) := by
  have hgl := hL.layout.stableBounds (c.gBits,jointGLen c) (by simp [jointStableRanges])
  have digit : RelCT isa (fun s t =>
      FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E s t ∧
      JointCore c C base size Q u v (JointGenerator c C base size G T) A s ∧
      JointCore c C base size Q u v (JointGenerator c C base size G T) A t ∧
      s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j)
      (.block (Joint.fixedRead c))
      (fun s t => FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E s t ∧
      JointCore c C base size Q u v (JointGenerator c C base size G T) A s ∧
      JointCore c C base size Q u v (JointGenerator c C base size G T) A t ∧
      s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j ∧
      s.gpr .x2=jointGCell c u j ∧ t.gpr .x2=jointGCell c u j ∧
      (c.gw=9 → s.gpr .x3=(FastNaf.wbyte u (2*j+1)).setWidth 64) ∧
      (c.gw=9 → t.gpr .x3=(FastNaf.wbyte u (2*j+1)).setWidth 64)) := by
    intro s t ts tt s' t' ⟨hp,cs,ct,ps,pt⟩ es et
    obtain ⟨_,_,xs,vs,_,v3s,ks⟩ := jointFixedRead_ok hp.left.scr hL.gBits hj hgl ps
      cs.stable.generator
    obtain ⟨_,_,xt,vt,_,v3t,kt⟩ := jointFixedRead_ok hp.right.scr hL.gBits hj hgl pt
      ct.stable.generator
    obtain ⟨_,rfl⟩ := Exec.det es xs
    obtain ⟨_,rfl⟩ := Exec.det et xt
    have pub : AArch64.Taint.Agree (Taint.ofRegs [.x0,.x19]) s t := by
      refine ⟨hp.sp,fun r hr => ?_⟩
      simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.left.scr.x0.trans hp.right.scr.x0.symm
      · exact ps.trans pt.symm
    have frame {a b : State} (hk : VG.Proof.Ed25519.AArch64.Keeps [.x2,.x3,.x16] a b) :
        ProgKeep c.K.M base [] a b := keeps_prog hk (by
      intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [clob])
    refine ⟨hc.read _ _ _ _ _ _ trivial trivial pub es et,
      ⟨hp.left.of_keeps ks (by decide),hp.right.of_keeps kt (by decide),ks.sp.trans (hp.sp.trans kt.sp.symm)⟩,
      cs.of_keeps ks (by decide) (cs.external.keep (frame ks) (Exec.syms es) (by simp) cs.field.mod.tmp),
      ct.of_keeps kt (by decide) (ct.external.keep (frame kt) (Exec.syms et) (by simp) ct.field.mod.tmp),
      (ks.gpr _ (by decide)).trans ps,(kt.gpr _ (by decide)).trans pt,vs,vt,v3s,v3t⟩
  rw [Joint.fixedDigit]
  apply RelCT.seq digit
  apply RelCT.ite
  · intro s t ⟨_,_,_,_,_,s2,t2,_,_⟩
    change some (s.read .x .x2 != 0)=some (t.read .x .x2 != 0)
    rw [read_x,read_x,s2,t2]
  · intro s t ts tt s' t' ⟨⟨hp,cs,ct,s19,t19,s2,t2,s3,t3⟩,hn⟩ es et
    have anz : FastNaf.magnitude c.gw u j≠0 := by
      intro hz
      have hb : jointGCell c u j=0 := (jointGCell_zero_iff hL.layout.gw u j).mpr hz
      change some (s.read .x .x2 != 0)=some true at hn
      rw [read_x,s2,hb] at hn
      contradiction
    have entry := jointEntry_relCT (base:=base) (T:=T) (G:=G) (Q:=Q) (A:=A) (E:=E) (v:=v) hL hC hm hj anz hc
    have sum := fun E' => jointFixedSum_relCT certs (base:=base) (E:=E') hL hm hsize hOne hc
    exact (RelCT.seq entry (RelCT.exists_ sum)) _ _ _ _ _ _ ⟨hp,cs,ct,s19,t19,s2,t2,s3,t3⟩ es et
  · exact RelCT.block_nil (fun _ _ h => ⟨_,h.1.1⟩)

end VG.Proof.Weierstrass.AArch64
