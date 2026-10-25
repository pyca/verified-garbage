module

public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.TimingPrepare
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Joint
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.X448.AArch64.Fast.Erase
import VerifiedGarbage.Proof.Ed448.AArch64.VerifyCT.Erase
meta import VerifiedGarbage.Impl.Ed448.AArch64.Sparse
meta import VerifiedGarbage.Proof.X448.AArch64.Fast.Erase
meta import VerifiedGarbage.Proof.Ed448.AArch64.VerifyCT.Erase
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintSymMono
meta import VerifiedGarbage.Impl.Ed448.WnafWide
import VerifiedGarbage.Proof.Framework.RelCTAssoc

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
