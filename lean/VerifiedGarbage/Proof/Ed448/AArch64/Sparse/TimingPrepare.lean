module

public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.TimingPair
public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse
import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Normalize
import VerifiedGarbage.Proof.Ed448.AArch64.Window.Persist
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ed448.AArch64.VerifyCT.Front
meta import VerifiedGarbage.Impl.Ed448.AArch64.Sparse
meta import VerifiedGarbage.Proof.Ed448.AArch64.VerifyCT.Erase
meta import VerifiedGarbage.Proof.X448.AArch64.Fast.Erase
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintSymMono
import VerifiedGarbage.Proof.X448.AArch64.Iter
import VerifiedGarbage.Proof.Ed448.WnafWide.Bits

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
      rw [T.mem x (Or.inr (by omega)) (Or.inr (by simp only [ACC];omega))
        (Or.inr (by simp only [RX];omega)) (Or.inr (by simp only [TAB];omega)),
        bk.mem x (Or.inr (by omega)) (Or.inr (by simp only [ACC];omega)),F.mem x (Or.inr hx)]
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
