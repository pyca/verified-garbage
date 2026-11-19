module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Correct
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Local
public import VerifiedGarbage.Proof.Ed448.Ref
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Algebra.Group.Nat.Defs
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.Ed448.WnafWide.Limit
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.X448.AArch64.Main
public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse
import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.AffineSpec
public import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.X448.AArch64.Base.Add
import VerifiedGarbage.Proof.X448.AArch64.Base.AddDefs
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Joint
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Joint
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.X448.AArch64.Fast.Erase
import VerifiedGarbage.Proof.Ed448.AArch64.VerifyCT.Erase
meta import VerifiedGarbage.Impl.Ed448.AArch64.Sparse
meta import VerifiedGarbage.Proof.X448.AArch64.Fast.Erase
meta import VerifiedGarbage.Proof.Ed448.AArch64.VerifyCT.Erase
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintSymMono
meta import VerifiedGarbage.Impl.Ed448.WnafWide
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Normalize
import VerifiedGarbage.Proof.X448.AArch64.Iter
public import VerifiedGarbage.Proof.Ed448.WnafWide.Word
import VerifiedGarbage.Impl.Ed448.AArch64.VerifyWindow
import VerifiedGarbage.Proof.Framework.AArch64.TaintSymMono
import VerifiedGarbage.Proof.Framework.AArch64.TaintSplit
import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.TimingDigits
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.RecodePair
meta import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Joint
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.TimingAdd
import VerifiedGarbage.Proof.Framework.AArch64.TaintSym

/-! ### `Ed448.AArch64.Sparse.TimingPair`, which only this module used -/

section

/-! Scalar recoding has fixed work; the subsequent sparse loop uses only its public result. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse
open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.Ed448.AArch64 (KB)
open VG.Impl.Ed448.WnafWide (scalarLimit)
open VG.Impl.X448.AArch64 (BITS)
open VG.Proof.X448.AArch64 (Scr off)
open VG.Proof.X448.AArch64.Fast (BEnv)
open VG.Proof.Curve448.AArch64.Fast (Mb)

structure PairInput (base tbl:Addr) (S K:Nat) (s:State) : Prop where
  scr : Scr s base
  bnd : BEnv s.mem base
  tab : ∃ P:Spec.Ed448.Point,OddTabOk s.mem base P 8
  xb : ∀ e<8,∀ w<8,(Window.tw s.mem base e w).toNat<Mb
  bt : BaseTableAt s base tbl
  bits : ∀ i<456,s.mem (off base (BITS+i))=BitVec.ofNat 8 (WnafWide.bit S i)
  kv : Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (off base KB) 57)=K

private theorem pair_ctx {base tbl sp:Addr} {S K:Nat} {s:State} (hS:S<scalarLimit) (hK:K<scalarLimit)
    (h:Pinned sp tbl (PairInput base tbl S K) s) :
    WP isa recodePair s (Pinned sp tbl (DigitsCtx base tbl S K)):=by
  obtain ⟨P,hp⟩:=h.1.tab
  have bt:BaseTableAt s base (s.syms baseSym):=by rw [h.2.2];exact h.1.bt
  obtain ⟨tr,t,e,ht⟩:=recodePair_ok h.1.scr h.1.bnd hp h.1.xb bt hS hK h.1.bits h.1.kv
  refine ⟨tr,t,e,⟨ht.scr,ht.bnd,ht.sd,ht.kd,⟨P,ht.tab⟩,ht.xb,?_⟩,
    (Exec.sp e).trans h.2.1,by rw [Exec.syms e];exact h.2.2⟩
  have sy:t.syms baseSym=tbl:=by rw [Exec.syms e];exact h.2.2
  rw [←sy]
  exact ht.bt

private theorem pair_analysis : ∃ h,((taintS [baseSym]).check (Taint.ofRegs [.x3]) recodePair h).isSome=true:=by
  refine ⟨?h,?g⟩
  case g => taint_decide

theorem joint_ct (hA:AffineOk) (base tbl sp:Addr) (S K:Nat) (hS:S<scalarLimit) (hK:K<scalarLimit) :
    RelCT isa (fun s t => Pinned sp tbl (PairInput base tbl S K) s ∧
      Pinned sp tbl (PairInput base tbl S K) t) joint (fun _ _ => True):=by
  obtain ⟨ph,pa⟩:=pair_analysis
  have ha:∀ s t,Pinned sp tbl (PairInput base tbl S K) s ∧
      Pinned sp tbl (PairInput base tbl S K) t →
      Taint.AgreeS [baseSym] (Taint.ofRegs [.x3]) s t:=by
    intro s t h
    refine ⟨⟨h.1.2.1.trans h.2.2.1.symm,?_⟩,?_⟩
    · intro r hr
      obtain rfl:=List.mem_singleton.mp (Taint.mem_ofRegs.mp hr)
      exact h.1.1.scr.x3.trans h.2.1.scr.x3.symm
    · intro n hn;obtain rfl:=List.mem_singleton.mp hn
      exact h.1.2.2.trans h.2.2.2.symm
  exact seq_same (RelCT.taint (A:=taintS [baseSym]) (Taint.ofRegs [.x3]) ha pa)
    (fun _ h => pair_ctx hS hK h) (jointDigits_ct hA base tbl sp S K)

end VG.Proof.Ed448.AArch64.Sparse

end

end

/-! ### `Ed448.AArch64.Sparse.Timing`, which only this module used -/

section

/-! ### `Ed448.AArch64.Sparse.TimingPrepare`, which only this module used -/

section

/-! The decoding/table prefix supplies the two public scalar values to recoding. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse
open VG VG.AArch64
open VG.Impl.Ed448.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.X448.AArch64 (BITS ACC)
open VG.Proof.X448.AArch64 (off ofs)
open VG.Proof.Ed448.AArch64.Window (Persist wfront_ok)
open VG.Spec.Ed448 (bytesAt decodeLE)

structure PrepareInput (base:Addr) (S K:Nat) (s:State) : Prop where
  h3 : s.gpr .x3=base
  hw : (⟨base,8192⟩:Region)∈s.wr
  hn : base.toNat+8192≤2^64
  rpk : ∀ i<57,InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 i) 1
  rsg : ∀ i<114,InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 i) 1
  rch : ∀ i<57,InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 i) 1
  fpk : ∀ i<57,8192≤ofs base (s.gpr .x0+BitVec.ofNat 64 i)
  fsg : ∀ i<114,8192≤ofs base (s.gpr .x1+BitVec.ofNat 64 i)
  fch : ∀ i<57,8192≤ofs base (s.gpr .x2+BitVec.ofNat 64 i)
  bt : BaseTableAt s base (s.syms baseSym)
  svalue : S=decodeLE (bytesAt s.mem (s.gpr .x1+BitVec.ofNat 64 57) 57)
  kvalue : K=decodeLE (bytesAt s.mem (s.gpr .x2) 57)

theorem prepare_ok (hR:VG.Proof.Ed448.RecoverOk) {s:State} {base:Addr} {S K:Nat}
    (h:PrepareInput base S K s) :
    WP isa prepare s fun t => PairInput base (t.syms baseSym) S K t:=by
  unfold prepare
  apply WP.assoc'
  refine WP.seq (WP.mono_syms (wfront_ok hR h.h3 h.hw h.hn h.rpk h.rsg h.rch h.fpk h.fsg h.fch) fun a F asy => ?_)
  have pa:Persist base s.gpr s.v (fun i => s.mem (s.gpr .x2+BitVec.ofNat 64 i)) a.mem:=
    ⟨F.saved,F.savedX,F.savedV,F.lrs,F.kb⟩
  refine WP.seq (WP.mono_syms (normalizeKey_ok F.scr F.bnd) fun b ⟨bk,bb,bx,bsm,bp⟩ bsy => ?_)
  have pb:=pa.outside2 bk.mem
  refine WP.mono_syms (oddTable_ok (bk.scr F.scr) bb bx) fun c T csy => ?_
  have pc:Persist base s.gpr s.v (fun i => s.mem (s.gpr .x2+BitVec.ofNat 64 i)) c.mem:=
    pb.of_frame fun x hx => T.mem x (by omega_using [hx]) (by simp only [ACC];omega_using [hx])
      (by simp only [RX];omega_using [hx]) (by simp only [RY,CAN];omega_using [hx])
  have cbits:∀ i<456,c.mem (off base (BITS+i))=BitVec.ofNat 8 (WnafWide.bit S i):=by
    intro i hi
    have ho:ofs base (off base (BITS+i))=BITS+i:=VG.Proof.X448.AArch64.ofs_off' base (by simp only [BITS];omega_using [hi])
    rw [T.mem _ (Or.inr (by rw [ho];simp only [BITS];omega_using []))
      (Or.inl (by rw [ho];simp only [BITS,ACC];omega_using [hi]))
      (Or.inl (by rw [ho];simp only [BITS,RX];omega_using [hi]))
      (Or.inl (by rw [ho];simp only [BITS,RY,CAN];omega_using [hi])),
      bk.mem _ (Or.inr (by rw [ho];simp only [BITS];omega_using []))
        (Or.inl (by rw [ho];simp only [BITS,ACC];omega_using [hi]))]
    have hv:=F.bits i (by omega_using [hi])
    rw [VG.Proof.X448.AArch64.Base.bit_eq,←h.svalue] at hv
    exact hv
  have cbytes:bytesAt c.mem (off base KB) 57=bytesAt s.mem (s.gpr .x2) 57:=by
    unfold bytesAt
    apply List.map_congr_left
    intro i hi
    have hi':i<57:=List.mem_range.mp hi
    rw [Offset.add_add]
    exact pc.kb i hi'
  have cbt:BaseTableAt c base (c.syms baseSym):=by
    rw [csy,bsy,asy]
    apply h.bt.of_far
    · rw [T.rd,T.wr,bk.regs.2.1,bk.regs.2.2,F.rd,F.wr]
    · intro x hx
      rw [T.mem x (Or.inr (by omega_using [hx])) (Or.inr (by simp only [ACC];omega_using [hx]))
        (Or.inr (by simp only [RX];omega_using [hx])) (Or.inr (by simp only [TAB];omega_using [hx])),
        bk.mem x (Or.inr (by omega_using [hx])) (Or.inr (by simp only [ACC];omega_using [hx])),F.mem x (Or.inr hx)]
  exact ⟨T.scr,T.env,⟨_,T.tab⟩,T.xbound,cbt,cbits,by rw [cbytes];exact h.kvalue.symm⟩

private theorem prepare_analysis : ∃ h,((taintS [baseSym]).check
    (Taint.ofRegs [.x0,.x1,.x2,.x3]) prepare h).isSome=true:=by
  apply exists_isSome_of_eraseT
  simp only [Code.eraseT,prepare,wfront,ventry,bitsAt,decodes,negA,decode,Point56.powCall,
    fnCall,Point56.powFn,asFn,root,ops_eraseT,sqn_eraseT,List.map_append,eqSlots_eraseT,
    normalizeKey,oddTable,tableBody,Point56.addCall,Point56.addFn,Point56.doubleCall,Point56.doubleFn]
  refine ⟨?h,?g⟩
  case g => taint_decide

structure Entry (base pk sig ch:Addr) (S K:Nat) (s:State) : Prop where
  pre : PrepareInput base S K s
  pk : s.gpr .x0=pk
  sig : s.gpr .x1=sig
  ch : s.gpr .x2=ch

theorem prepare_ct (hR:VG.Proof.Ed448.RecoverOk) (base pk sig ch sp tbl:Addr) (S K:Nat) :
    RelCT isa (fun s t => Pinned sp tbl (Entry base pk sig ch S K) s ∧
      Pinned sp tbl (Entry base pk sig ch S K) t) prepare
      (fun s t => Pinned sp tbl (PairInput base tbl S K) s ∧
        Pinned sp tbl (PairInput base tbl S K) t):=by
  obtain ⟨ph,pa⟩:=prepare_analysis
  have ha:∀ s t,Pinned sp tbl (Entry base pk sig ch S K) s ∧
      Pinned sp tbl (Entry base pk sig ch S K) t →
      Taint.AgreeS [baseSym] (Taint.ofRegs [.x0,.x1,.x2,.x3]) s t:=by
    intro s t h
    refine ⟨⟨h.1.2.1.trans h.2.2.1.symm,?_⟩,?_⟩
    · intro r hr
      simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h.1.1.pk.trans h.2.1.pk.symm
      · exact h.1.1.sig.trans h.2.1.sig.symm
      · exact h.1.1.ch.trans h.2.1.ch.symm
      · exact h.1.1.pre.h3.trans h.2.1.pre.h3.symm
    · intro n hn;obtain rfl:=List.mem_singleton.mp hn
      exact h.1.2.2.trans h.2.2.2.symm
  have hw:∀ s,Pinned sp tbl (Entry base pk sig ch S K) s →
      WP isa prepare s (Pinned sp tbl (PairInput base tbl S K)):=by
    intro s h
    obtain ⟨tr,t,e,ht⟩:=prepare_ok hR h.1.pre
    have sy:t.syms baseSym=tbl:=by rw [Exec.syms e];exact h.2.2
    exact ⟨tr,t,e,sy ▸ ht,(Exec.sp e).trans h.2.1,sy⟩
  exact ((RelCT.taint (A:=taintS [baseSym]) (Taint.ofRegs [.x0,.x1,.x2,.x3]) ha pa).wp
    (fun s t h => ⟨hw s h.1,hw t h.2⟩)).mono (fun _ _ h => h) (fun _ _ h => h.2)

end VG.Proof.Ed448.AArch64.Sparse

end

end

/-! Full sparse verification timing depends only on public scalar values and addresses. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse
open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.Ed448.AArch64 (wfinish wcmp wresult fnCall asFn)
open VG.Impl.Ed448.WnafWide (scalarLimit)

private theorem tail_analysis : ∃ h,((taintS [baseSym]).check (Taint.ofRegs [.x3])
    (.seq cross wfinish) h).isSome=true:=by
  apply exists_isSome_of_eraseT
  simp only [Code.eraseT,cross,wfinish,wcmp,wresult,VG.Impl.Ed448.AArch64.Point56.doubleCall,
    fnCall,VG.Impl.Ed448.AArch64.Point56.doubleFn,asFn,ops_eraseT,List.map_append,eqSlots_eraseT]
  refine ⟨?h,?g⟩
  case g => taint_decide

private theorem joint_tail_ctx (hA:AffineOk) {base sp tbl:Addr} {S K:Nat} {s:State}
    (hS:S<scalarLimit) (hK:K<scalarLimit) (h:Pinned sp tbl (PairInput base tbl S K) s) :
    WP isa joint s (Pinned sp tbl (fun t => t.gpr .x3=base)):=by
  obtain ⟨P,hp⟩:=h.1.tab
  have bt:BaseTableAt s base (s.syms baseSym):=by rw [h.2.2];exact h.1.bt
  obtain ⟨tr,t,e,ht⟩:=joint_ok hA h.1.scr h.1.bnd hp h.1.xb bt hS hK h.1.bits h.1.kv
  exact ⟨tr,t,e,ht.core.scr.x3,(Exec.sp e).trans h.2.1,by rw [Exec.syms e];exact h.2.2⟩

theorem verifyEquation_ct (hA:AffineOk) (hR:VG.Proof.Ed448.RecoverOk) (base pk sig ch sp tbl:Addr)
    (S K:Nat) (hS:S<scalarLimit) (hK:K<scalarLimit) :
    RelCT isa (fun s t => Pinned sp tbl (Entry base pk sig ch S K) s ∧
      Pinned sp tbl (Entry base pk sig ch S K) t)
      VG.Impl.Ed448.AArch64.Sparse.verifyEquation (fun _ _ => True):=by
  have ht:RelCT isa (fun s t => Pinned sp tbl (fun u => u.gpr .x3=base) s ∧
      Pinned sp tbl (fun u => u.gpr .x3=base) t) (.seq cross wfinish) (fun _ _ => True):=by
    obtain ⟨th,ta⟩:=tail_analysis
    apply RelCT.taint (A:=taintS [baseSym]) (Taint.ofRegs [.x3]) _ ta
    intro s t h
    refine ⟨⟨h.1.2.1.trans h.2.2.1.symm,?_⟩,?_⟩
    · intro r hr
      obtain rfl:=List.mem_singleton.mp (Taint.mem_ofRegs.mp hr)
      exact h.1.1.trans h.2.1.symm
    · intro n hn;obtain rfl:=List.mem_singleton.mp hn
      exact h.1.2.2.trans h.2.2.2.symm
  have hh:RelCT isa (fun s t => Pinned sp tbl (Entry base pk sig ch S K) s ∧
      Pinned sp tbl (Entry base pk sig ch S K) t)
      (.seq prepare (.seq joint (.seq cross wfinish))) (fun _ _ => True):=
    (prepare_ct hR base pk sig ch sp tbl S K).seq
      (seq_same (joint_ct hA base tbl sp S K hS hK) (fun _ h => joint_tail_ctx hA hS hK h) ht)
  exact hh.assoc.assoc

end VG.Proof.Ed448.AArch64.Sparse

end

end

/-! Correctness and timing against the unchanged reviewed Ed448 equation contract. -/

-- Formerly `VerifiedGarbage/Proof/Ed448/AArch64/Sparse/LocalCorrect.lean`, which only this module imported.
section

/-! The sparse equation meets the local correctness, ABI and timing interface. -/

section

namespace VG.Proof.Ed448.AArch64.Sparse
open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Proof.X448.AArch64 (ofs far)
open VG.Impl.Ed448.WnafWide (scalarLimit)

private theorem prepare_pre {s:State} (h:verifyEquationLocal.pre s) :
    PrepareInput (s.gpr .x3) (signatureScalar s) (challengeScalar s) s:=by
  obtain ⟨hr,hw,hpk,hsg,hch,hn,hb⟩:=h
  refine ⟨rfl,by rw [hw];simp,hn,?_,?_,?_,?_,?_,?_,held_baseTable hb ?_,rfl,rfl⟩
  · intro i hi
    exact ⟨⟨s.gpr .x0,57⟩,by rw [hr];simp,Offset.contains_base _ hi (by omega)⟩
  · intro i hi
    exact ⟨⟨s.gpr .x1,114⟩,by rw [hr];simp,Offset.contains_base _ hi (by omega)⟩
  · intro i hi
    exact ⟨⟨s.gpr .x2,57⟩,by rw [hr];simp,Offset.contains_base _ hi (by omega)⟩
  · intro i hi;exact far hpk hi (by decide)
  · intro i hi;exact far hsg hi (by decide)
  · intro i hi;exact far hch hi (by decide)
  · rw [hr,baseWords_length];simp

private theorem scalar_bound (m:Mem) (p:Addr) :
    Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m p 57)<scalarLimit:=by
  have h:=VG.Proof.Ed448.decodeLE_lt' (Spec.Ed448.bytesAt m p 57)
  have hl:(Spec.Ed448.bytesAt m p 57).length=57:=by simp [Spec.Ed448.bytesAt]
  rwa [hl,←WnafWide.scalarLimit_eq] at h

theorem equation_ok (hA:AffineOk) (hR:VG.Proof.Ed448.RecoverOk) (s:State) (h:verifyEquationLocal.pre s) :
    ∃ tr t,Exec isa VG.Impl.Ed448.AArch64.Sparse.verifyEquation s tr t ∧
      abiPreserved s t ∧ verifyEquationLocal.post s t:=by
  have p:=prepare_pre h
  obtain ⟨tr,t,e,hg,hv,hr⟩:=correct hA hR p.h3 p.hw p.hn p.rpk p.rsg p.rch p.fpk p.fsg p.fch p.bt
  exact ⟨tr,t,e,⟨hg,Exec.sp e,hv⟩,hr⟩

theorem equation_ct (hA:AffineOk) (hR:VG.Proof.Ed448.RecoverOk) :
    ConstantTime isa verifyEquationLocal.pre verifyEquationLocal.pub VG.Impl.Ed448.AArch64.Sparse.verifyEquation:=by
  intro s t tr tr' u v hs ht hp es et
  obtain ⟨hsp,h0,h1,h2,h3,hsy,hS,hK⟩:=hp
  have hd:=verifyEquation_ct hA hR (s.gpr .x3) (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) s.sp
    (s.syms baseSym) (signatureScalar s) (challengeScalar s)
    (scalar_bound _ _) (scalar_bound _ _)
  apply (hd s t tr tr' u v ?_ es et).1
  refine ⟨⟨⟨prepare_pre hs,rfl,rfl,rfl⟩,rfl,rfl⟩,⟨?_,hsp.symm,hsy.symm⟩⟩
  rw [h3,hS,hK]
  exact ⟨prepare_pre ht,h0.symm,h1.symm,h2.symm⟩

theorem equation_eqOk (hA:AffineOk) (hR:VG.Proof.Ed448.RecoverOk) : EqOk:=⟨equation_ok hA hR,equation_ct hA hR⟩

end VG.Proof.Ed448.AArch64.Sparse
end

end

-- Formerly `VerifiedGarbage/Proof/Ed448/AArch64/Sparse/Affine.lean`, which only this module imported.
section

/-! Inline affine addition with the existing verified interleaved field formula. -/

section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.X448.AArch64 (slot ACC)
open VG.Impl.X448.AArch64.Fast (saved)
open VG.Proof.X448.AArch64 (Scr Keeps Outside Outside2 ofs)
open VG.Proof.X448.AArch64.Weak (Index)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd Same fclob indeps_ops_mul2)
open VG.Proof.X448.AArch64.Base (affEnv)
open VG.Proof.Curve448.AArch64.Fast (Mb)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

private theorem mask_ok {s:State} {base:Addr} (hs:Scr s base) :
    WP isa (.block [.movz .x .x12 0xffff 0,.movk .x .x12 0x0fff 1]) s fun t =>
      Keeps [] s t ∧ t.mem=s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,State.read,Size.bits,Nat.reduceMul,
    Nat.reduceLT,ite_true,RegUpd.gpr_write,BitVec.setWidth_eq,Option.some.injEq,exists_eq_left']
  refine ⟨⟨fun r _ => ?_,rfl,rfl⟩,rfl⟩
  by_cases h:r= .x12
  · subst r
    simp only [RegUpd.gpr_write,ite_true,hs.mask]
    rfl
  · simp only [RegUpd.gpr_write,h,ite_false]

theorem addAffine_ok {s:State} {base:Addr} (hs:Scr s base) (hb:BEnv s.mem base)
    (hz:Bnd Mb s.mem base (slot 19)) :
    WP isa VG.Impl.Ed448.AArch64.Sparse.addAffine s fun t =>
      AffineKeep base s t ∧ BEnv t.mem base ∧
      Same base (VG.Proof.X448.AArch64.Base.temps++[5,3,4]) s.mem t.mem ∧
      Bnd Mb t.mem base (slot 3) ∧ Bnd Mb t.mem base (slot 4) ∧ Bnd Mb t.mem base (slot 5) ∧
      EV t.mem base=affEnv 3 4 5 6 7 (EV s.mem base) := by
  unfold VG.Impl.Ed448.AArch64.Sparse.addAffine
  rw [WP.seq_iff,List.append_assoc,WP.block_append_iff]
  refine WP.mono (save_ok hs) fun a ⟨sv,fo,ag,ar,aw⟩ => ?_
  have ak:Keeps [] s a:=⟨fun _ _ => congrFun ag _,ar,aw⟩
  have ha:Scr a base:=hs.of_keeps ak (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mask_ok ha) fun b ⟨bk,bm⟩ => ?_
  have hb':Scr b base:=ha.of_keeps bk (by decide)
  have bb:BEnv b.mem base:=by rw [bm];exact save_bounds fo hb
  have bz:Bnd Mb b.mem base (slot 19):=by
    rw [bm]
    intro j hj
    rw [fo.limbs (Or.inl (by decide)) (by decide) (by omega)]
    exact hz j hj
  refine WP.mono (VG.Proof.X448.AArch64.Base.addAffine_ok 3 4 5 6 7
    (by decide) (by decide) (by decide) hb' bb bz
    (indeps_ops_mul2 _ _ _ _ _ _ _ (by decide +kernel))
    (indeps_ops_mul2 _ _ _ _ _ _ _ (by decide +kernel))
    (indeps_ops_mul2 _ _ _ _ _ _ _ (by decide +kernel))
    (indeps_ops_mul2 _ _ _ _ _ _ _ (by decide +kernel)))
    fun c ⟨ck,cb,cs,cx,cy,cz,ce⟩ => ?_
  have hsv:Saved base s.gpr c.mem:=fun i hi => by
    rw [ck.mem.word (Or.inr (by simp only [GSAVE];omega)) (Or.inr (by simp only [ACC,GSAVE];omega)) (by simp only [GSAVE];omega),bm]
    exact sv i hi
  refine WP.mono (restore_ok (ck.scr hb') hsv) fun t ⟨tg,tm,tk⟩ => ?_
  refine ⟨⟨?_,tg,?_⟩,?_,?_,?_,?_,?_,?_⟩
  · exact ((ak.mono (by decide)).trans (bk.mono (by decide))).trans
      (ck.regs.trans (tk.mono (by decide)))
  · intro x hx hy hz
    rw [tm,ck.mem x hx hy,bm,fo x hz]
  · rw [tm]
    exact cb
  · intro i hi j hj
    rw [tm,cs i hi j hj,bm]
    have h:=i.isLt
    exact fo.limbs (Or.inl (by simp only [slot,GSAVE];omega)) (by simp only [slot];omega) (by omega)
  · rw [tm]
    exact cx
  · rw [tm]
    exact cy
  · rw [tm]
    exact cz
  · rw [tm,ce,bm,save_env fo]

theorem affine_ok : AffineOk:=⟨fun hs hb hz => addAffine_ok hs hb hz⟩

end VG.Proof.Ed448.AArch64.Sparse
end

end

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse
open VG VG.AArch64 VG.Impl.Ed448.AArch64.Sparse

theorem verified_eqOk (hR:VG.Proof.Ed448.RecoverOk) : EqOk:=equation_eqOk affine_ok hR

end VG.Proof.Ed448.AArch64.Sparse
