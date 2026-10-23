module

public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.TimingDigits
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.RecodePair
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Joint
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintSymMono
meta import VerifiedGarbage.Impl.Ed448.WnafWide
public import VerifiedGarbage.Proof.Ed448.WnafWide.Bits

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
