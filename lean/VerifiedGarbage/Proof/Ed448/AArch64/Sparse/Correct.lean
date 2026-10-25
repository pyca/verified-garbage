module

public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Joint
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Cross
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Normalize
import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Equation
import VerifiedGarbage.Proof.Ed448.AArch64.Window.Persist
import VerifiedGarbage.Proof.Ed448.AArch64.Window.Result
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.Ed448.WnafWide.Limit
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.X448.AArch64.Iter
import VerifiedGarbage.Proof.Ed448.WnafWide.Bits
public import Mathlib.Algebra.Group.Nat.Defs
public import VerifiedGarbage.Proof.Ed448.AArch64.Window.Front
public import VerifiedGarbage.Proof.Ed448.AArch64.Window.KLoop
public import VerifiedGarbage.Proof.Ed448.Ref
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.AArch64.Mem
public import VerifiedGarbage.Spec.Ed448.Contract
public import VerifiedGarbage.TCB.AArch64.Target

/-! Complete sparse verification: decoding, the unreduced joint equation,
cofactoring, canonical checks and restoration of every callee-saved register. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64 (RX RY CAN KB TAB)
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.Ed448.WnafWide (scalarLimit)
open VG.Impl.X448.AArch64 (slot ACC BITS)
open VG.Proof.X448.AArch64 (Scr Keeps Outside off ofs limbs)
open VG.Proof.X448.AArch64.Weak (Index)
open VG.Proof.Curve448.AArch64.Fast (Ib)
open VG.Proof.X448.AArch64.Base (pt)
open VG.Proof.Ed448.AArch64.Window (Persist slotPt wfront_ok wfinish_ok FV_of_limbs ib_of_limbs dbl2)
open VG.Spec.Ed448 (bytesAt decodeLE)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E
local notation "FV" => VG.Proof.X448.AArch64.Weak.F

private theorem bytes_len (m:Mem) (p:Addr) (n:Nat) : (bytesAt m p n).length=n:=by
  simp [bytesAt]

private theorem bytes_take (m:Mem) (p:Addr) : (bytesAt m p 114).take 57=bytesAt m p 57:=by
  simp [bytesAt,←List.map_take,List.take_range]

private theorem bytes_drop (m:Mem) (p:Addr) :
    (bytesAt m p 114).drop 57=bytesAt m (p+BitVec.ofNat 64 57) 57:=by
  refine List.ext_getElem (by simp [bytesAt]) fun i _ _ => ?_
  simp only [bytesAt,List.getElem_drop,List.getElem_map,List.getElem_range]
  rw [Offset.add_add]

private theorem byte_scalar_bound (m:Mem) (p:Addr) : decodeLE (bytesAt m p 57)<scalarLimit:=by
  have h:=VG.Proof.Ed448.decodeLE_lt' (bytesAt m p 57)
  rw [bytes_len,←WnafWide.scalarLimit_eq] at h
  exact h

theorem correct (hA:AffineOk) (hR:VG.Proof.Ed448.RecoverOk) {s:State} {base:Addr}
    (h3:s.gpr .x3=base) (hw:(⟨base,8192⟩:Region)∈s.wr) (hn:base.toNat+8192≤2^64)
    (rpk:∀ i<57,InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 i) 1)
    (rsg:∀ i<114,InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 i) 1)
    (rch:∀ i<57,InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 i) 1)
    (fpk:∀ i<57,8192≤ofs base (s.gpr .x0+BitVec.ofNat 64 i))
    (fsg:∀ i<114,8192≤ofs base (s.gpr .x1+BitVec.ofNat 64 i))
    (fch:∀ i<57,8192≤ofs base (s.gpr .x2+BitVec.ofNat 64 i))
    (hbt:BaseTableAt s base (s.syms baseSym)) :
    WP isa VG.Impl.Ed448.AArch64.Sparse.verifyEquation s fun t =>
      (∀ r∈preserved,t.gpr r=s.gpr r) ∧
      (∀ r∈preservedV,(t.v r).extractLsb' 0 64=(s.v r).extractLsb' 0 64) ∧
      t.gpr .x0=(if Spec.Ed448.verifyEquation (bytesAt s.mem (s.gpr .x0) 57)
        (bytesAt s.mem (s.gpr .x1) 114) (bytesAt s.mem (s.gpr .x2) 57) then 1 else 0):=by
  let S:=decodeLE (bytesAt s.mem (s.gpr .x1+BitVec.ofNat 64 57) 57)
  let K:=decodeLE (bytesAt s.mem (s.gpr .x2) 57)
  have hS:S<scalarLimit:=byte_scalar_bound _ _
  have hK:K<scalarLimit:=byte_scalar_bound _ _
  unfold VG.Impl.Ed448.AArch64.Sparse.verifyEquation
  refine WP.seq (WP.mono_syms (wfront_ok hR h3 hw hn rpk rsg rch fpk fsg fch) fun a F asy => ?_)
  have pa:Persist base s.gpr s.v (fun i => s.mem (s.gpr .x2+BitVec.ofNat 64 i)) a.mem:=
    ⟨F.saved,F.savedX,F.savedV,F.lrs,F.kb⟩
  refine WP.seq (WP.mono_syms (normalizeKey_ok F.scr F.bnd) fun b ⟨bk,bb,bx,bsm,bp⟩ bsy => ?_)
  have pb:=pa.outside2 bk.mem
  refine WP.seq (WP.mono_syms (oddTable_ok (bk.scr F.scr) bb bx) fun c T csy => ?_)
  have pc:Persist base s.gpr s.v (fun i => s.mem (s.gpr .x2+BitVec.ofNat 64 i)) c.mem:=
    pb.of_frame fun x hx => T.mem x (by omega) (by simp only [ACC];omega)
      (by simp only [RX];omega) (by simp only [RY,CAN];omega)
  have cbits:∀ i<456,c.mem (off base (BITS+i))=BitVec.ofNat 8 (WnafWide.bit S i):=by
    intro i hi
    have ho:ofs base (off base (BITS+i))=BITS+i:=VG.Proof.X448.AArch64.ofs_off' base (by simp only [BITS];omega)
    rw [T.mem _ (Or.inr (by rw [ho];simp only [BITS];omega))
      (Or.inl (by rw [ho];simp only [BITS,ACC];omega))
      (Or.inl (by rw [ho];simp only [BITS,RX];omega))
      (Or.inl (by rw [ho];simp only [BITS,RY,CAN];omega)),
      bk.mem _ (Or.inr (by rw [ho];simp only [BITS];omega))
        (Or.inl (by rw [ho];simp only [BITS,ACC];omega))]
    have hv:=F.bits i (by omega)
    rw [VG.Proof.X448.AArch64.Base.bit_eq] at hv
    exact hv
  have ckv:decodeLE (bytesAt c.mem (off base KB) 57)=K:=by
    congr 1
    unfold bytesAt
    apply List.map_congr_left
    intro i hi
    have hi':i<57:=List.mem_range.mp hi
    rw [Offset.add_add]
    exact pc.kb i hi'
  have cbt:BaseTableAt c base (c.syms baseSym):=by
    rw [csy,bsy,asy]
    apply hbt.of_far
    · rw [T.rd,T.wr,bk.regs.2.1,bk.regs.2.2,F.rd,F.wr]
    · intro x hx
      rw [T.mem x (Or.inr (by omega)) (Or.inr (by simp only [ACC];omega))
        (Or.inr (by simp only [RX];omega)) (Or.inr (by simp only [TAB];omega)),
        bk.mem x (Or.inr (by omega)) (Or.inr (by simp only [ACC];omega)),F.mem x (Or.inr hx)]
  refine WP.seq (WP.mono (joint_ok hA T.scr T.env T.tab T.xbound cbt hS hK cbits ckv) fun d J => ?_)
  have pd:Persist base s.gpr s.v (fun i => s.mem (s.gpr .x2+BitVec.ofNat 64 i)) d.mem:=
    pc.of_frame fun x hx => J.mem x (by omega) (by simp only [ACC];omega)
      (by simp only [GSAVE];omega) (by simp only [BITS];omega) (by simp only [SDIG];omega)
  have hrx:∀ i<8,limbs d.mem base RX i=limbs a.mem base (slot 8) i:=by
    intro i hi
    show (VG.Proof.X448.AArch64.word d.mem base (RX+8*i)).toNat=_
    rw [J.mem.word (Or.inr (by simp only [RX];omega)) (Or.inr (by simp only [RX,ACC];omega))
      (Or.inr (by simp only [RX,GSAVE];omega)) (Or.inr (by simp only [RX,BITS];omega))
      (Or.inr (by simp only [RX,SDIG];omega)) (by simp only [RX];omega)]
    change limbs c.mem base RX i=_
    rw [T.rx i hi]
    change limbs b.mem base (slot (8:Index).val) i=_
    exact bsm 8 (by decide) i hi
  have hry:∀ i<8,limbs d.mem base RY i=limbs a.mem base (slot 9) i:=by
    intro i hi
    show (VG.Proof.X448.AArch64.word d.mem base (RY+8*i)).toNat=_
    rw [J.mem.word (Or.inr (by simp only [RY,CAN];omega)) (Or.inr (by simp only [RY,CAN,ACC];omega))
      (Or.inl (by simp only [RY,CAN,GSAVE];omega)) (Or.inr (by simp only [RY,CAN,BITS];omega))
      (Or.inl (by simp only [RY,CAN,SDIG];omega)) (by simp only [RY,CAN];omega)]
    change limbs c.mem base RY i=_
    rw [T.ry i hi]
    change limbs b.mem base (slot (9:Index).val) i=_
    exact bsm 9 (by decide) i hi
  refine WP.seq (WP.mono (cross_ok J.core.scr J.core.env J.core.zbound J.core.one
    (ib_of_limbs hrx (F.bnd 8)) (ib_of_limbs hry (F.bnd 9)))
    fun e ⟨es,ek,em,eq,eb⟩ => ?_)
  have pe:=pd.outside2 em
  refine WP.mono (wfinish_ok es (fun i h1 h2 j hj => Nat.lt_trans (eb i h1 h2 j hj) (by decide))
    pe.saved pe.savedX pe.lrs pe.savedV) fun t ⟨t0,t19,t20,tx,tv,t30,_,_⟩ => ⟨?_,?_,?_⟩
  · intro r hr
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact t19
    · exact t20
    · exact tx 0 (by decide)
    · exact tx 1 (by decide)
    · exact tx 2 (by decide)
    · exact tx 3 (by decide)
    · exact tx 4 (by decide)
    · exact tx 5 (by decide)
    · exact tx 6 (by decide)
    · exact tx 7 (by decide)
    · exact t30
  · intro r hr
    simp only [preservedV, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact tv 0 (by decide)
    · exact tv 1 (by decide)
    · exact tv 2 (by decide)
    · exact tv 3 (by decide)
    · exact tv 4 (by decide)
    · exact tv 5 (by decide)
    · exact tv 6 (by decide)
    · exact tv 7 (by decide)
  · obtain ⟨c0,cA,cR,hflag,hc0,hcA,hcR⟩:=F.chk
    have heflag:e.gpr .x20=0|||c0|||cA|||cR:=by
      rw [ek.1 _ (by decide),J.chk,T.chk,bk.regs.1 _ (by decide),hflag]
    rw [t0]
    refine if_congr ?_ rfl rfl
    rw [heflag,VG.Proof.Ed448.AArch64.or_eq_zero64,VG.Proof.Ed448.AArch64.or_eq_zero64,
      VG.Proof.Ed448.AArch64.or_eq_zero64]
    cases ha:Spec.Ed448.decodePoint (bytesAt s.mem (s.gpr .x0) 57) with
    | none =>
      rw [VG.Proof.Ed448.verifyEquation_none (Or.inl ha)]
      exact ⟨fun h => absurd (hcA.mp h.1.1.2) (by rw [ha];decide),fun h => absurd h (by decide)⟩
    | some A =>
      cases hr:Spec.Ed448.decodePoint (bytesAt s.mem (s.gpr .x1) 57) with
      | none =>
        rw [VG.Proof.Ed448.verifyEquation_none (Or.inr (by rw [bytes_take];exact hr))]
        exact ⟨fun h => absurd (hcR.mp h.1.2) (by rw [hr];decide),fun h => absurd h (by decide)⟩
      | some R =>
        have cA0:cA=0:=hcA.mpr (by rw [ha];rfl)
        have cR0:cR=0:=hcR.mpr (by rw [hr];rfl)
        obtain ⟨rX,rY,rZ⟩:=F.rr R hr
        have hRpt:(⟨FV d.mem base RX,FV d.mem base RY,1⟩:Spec.Ed448.Point)=R:=by
          rw [FV_of_limbs hrx,FV_of_limbs hry]
          cases R
          simp only at rX rY rZ
          rw [←rX,←rY,←rZ]
          rfl
        have hq:∀ aA:VG.Proof.EdwardsLaw.EPoint VG.Proof.Ed448.dZ,VG.Proof.Ed448.Rep A aA →
            VG.Proof.Ed448.Rep (pt (EV d.mem base) 3 4 5)
              ((decodeLE ((bytesAt s.mem (s.gpr .x1) 114).drop 57):Int) • VG.Proof.Ed448.baseAff+
                (decodeLE (bytesAt s.mem (s.gpr .x2) 57):Int) • (-aA)):=by
          intro aA hA
          have hP:VG.Proof.Ed448.Rep (slotPt b.mem base) (-aA):=by
            rw [bp,F.na A ha]
            exact hA.neg
          have hq:=J.rep (-aA) hP
          rw [bytes_drop]
          exact hq
        rw [equation_eq (bytes_len _ _ _) (bytes_len _ _ _) (bytes_len _ _ _) ha
          (by rw [bytes_take];exact hr) hq,eq.c12,eq.c13,eq.c14,eq.c15,hRpt,cA0,cR0]
        simp only [dbl2,Spec.Ed448.pointEqual,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq,
          true_and,and_true,hc0]
        rw [bytes_drop]
        rfl

end VG.Proof.Ed448.AArch64.Sparse
