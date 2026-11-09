module

-- separate module: The full doubleFn instruction/vector-ABI replay costs more than its imports; window-call changes reuse this checked callee contract.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.DoubleOutput
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.DoubleBlocks
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointEntry
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointExit
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeLayout
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontSaves
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Impl.Mont.AArch64.P521Field

def doubleWrittenV : List VReg := [.v16,.v17,.v18,.v19,.v20,.v25]

theorem double_no_other_vectors (r : VReg) (hr : r∉doubleWrittenV) :
    ∀i∈doubleFnBlocks.flatten,vdstOf i≠some r := by
  have check : doubleFnBlocks.flatten.all (fun i => match vdstOf i with
    | none => true
    | some v => decide (v∈doubleWrittenV))=true := by lit_decide
  rw [List.all_eq_true] at check
  intro i hi he
  have e := check i hi
  rw [he] at e
  simp only [decide_eq_true_eq] at e
  exact hr e

theorem double_fn_vectors {s : State} {Q : State → Prop} (h : WP isa doubleFn s Q) :
    WP isa doubleFn s fun t => Q t ∧ ∀r,r∉doubleWrittenV → t.v r=s.v r := by
  obtain ⟨trace,t,exec,q⟩ := h
  exact ⟨trace,t,exec,q,fun r hr => Exec.vec (c:=doubleFn) (r:=r) (by simpa only [doubleFn,instrs] using double_no_other_vectors r hr) exec⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime lane)
open VG.Proof.Weierstrass (dblJF)

structure DoublePre (s : State) (W a o : Nat) : Prop where
  workspace : Scr s (s.gpr .x0) W
  room : 4584≤W
  layout : DoubleLayout a o
  argO : s.gpr .x1=BitVec.ofNat 64 o
  argA : s.gpr .x2=BitVec.ofNat 64 a

theorem double_fn_source : doubleFnBlocks.flatten=
    doubleFnBlocks.flatten.take 14++(doubleArithmeticCode++doubleExit) := by lit_decide

theorem double_fn_arithmetic_ok {s : State} {W a o : Nat} (pre : DoublePre s W a o)
    (bound : canonicalPoint s.mem (s.gpr .x0) a) :
    WP isa doubleFn s fun t =>
      canonicalPoint t.mem (s.gpr .x0) o ∧
      ordinaryPoint t.mem (s.gpr .x0) o=
        dblJF (ordinaryPoint s.mem (s.gpr .x0) a).1 (ordinaryPoint s.mem (s.gpr .x0) a).2.1
          (ordinaryPoint s.mem (s.gpr .x0) a).2.2 ∧
      (∀r∈preserved,t.gpr r=s.gpr r) ∧ t.sp=s.sp ∧
      DoubleFrame (s.gpr .x0) o s.mem t.mem ∧
      t.gpr .x0=s.gpr .x0 ∧ t.rd=s.rd ∧ t.wr=s.wr := by
  rw [doubleFn,double_fn_source,WP.block_append_iff]
  refine WP.mono (double_entry_ok s) fun u ⟨go,ga,gw,workspace,lanes,ku,_⟩ => ?_
  have gpo : u.gpr .x26=off (s.gpr .x0) o := by rw [go,pre.argO]
  have gpa : u.gpr .x27=off (s.gpr .x0) a := by rw [ga,pre.argA]
  have gpw : u.gpr .x28=off (s.gpr .x0) 4080 := gw
  have ctx : DoubleContext (s.gpr .x0) a o u :=
    ⟨workspace_ptr pre.workspace (by have h:=pre.layout.inputLow; have k:=pre.room; omega_arith) gpa ku.rd ku.wr,
     workspace_ptr pre.workspace (by have k:=pre.room; omega_arith) gpw ku.rd ku.wr,
     workspace_ptrW pre.workspace (by have k:=pre.room; omega_arith) (by decide) gpw ku.wr,
     workspace_ptrW pre.workspace (by have h:=pre.layout.outputLow; have k:=pre.room; omega_arith) (by decide) gpo ku.wr⟩
  have inv := double_input_inv (o:=o) ku.mem bound
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Weierstrass.AArch64.Mont.WP.block_novec double_arithmetic_novec
    (double_body_ok pre.layout ctx inv)) fun v ⟨⟨iv,_,kv,frame⟩,vv⟩ => ?_
  have output := double_output iv
  refine WP.mono (double_exit_ok v) fun t ⟨reset,restored,kt,_⟩ => ?_
  have saved : ∀r∈nativeSaved,t.gpr r=s.gpr r := by
    intro r hr
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hr
    rw [restored i hi,vv]
    exact lanes i hi
  have link : t.gpr .x30=s.gpr .x30 :=
    (kt.gpr .x30 (by decide)).trans ((kv.gpr .x30 (by decide)).trans (ku.gpr .x30 (by decide)))
  refine ⟨?_,?_,?_,kt.sp.trans (kv.sp.trans ku.sp),?_,?_,kt.rd.trans (kv.rd.trans ku.rd),kt.wr.trans (kv.wr.trans ku.wr)⟩
  · rw [kt.mem]
    exact output.1
  · rw [kt.mem]
    exact output.2
  · intro r hr
    have hpres : preserved=nativeSaved++[.x30] := by decide
    rw [hpres,List.mem_append] at hr
    rcases hr with hr|hr
    · exact saved r hr
    · have he : r=.x30 := List.mem_singleton.mp hr
      rw [he]; exact link
  · rw [ku.mem] at frame
    simpa only [kt.mem] using frame
  · rw [reset,vv,workspace]

theorem double_fn_ok {s : State} {W a o : Nat} (pre : DoublePre s W a o)
    (bound : canonicalPoint s.mem (s.gpr .x0) a) :
    WP isa doubleFn s fun t =>
      abiPreserved s t ∧ canonicalPoint t.mem (s.gpr .x0) o ∧
      ordinaryPoint t.mem (s.gpr .x0) o=
        dblJF (ordinaryPoint s.mem (s.gpr .x0) a).1 (ordinaryPoint s.mem (s.gpr .x0) a).2.1
          (ordinaryPoint s.mem (s.gpr .x0) a).2.2 ∧
      DoubleFrame (s.gpr .x0) o s.mem t.mem ∧ t.gpr .x0=s.gpr .x0 ∧ t.rd=s.rd ∧ t.wr=s.wr ∧
      (∀r,r∉doubleWrittenV → t.v r=s.v r) := by
  refine WP.mono (double_fn_vectors (double_fn_arithmetic_ok pre bound))
    fun t ⟨⟨b,p,g,sp,f,z,r,w⟩,v⟩ => ?_
  have hp : ∀d∈preservedV,d∉doubleWrittenV := by decide
  exact ⟨⟨g,sp,fun d hd => by rw [v d (hp d hd)]⟩,b,p,f,z,r,w,v⟩

end VG.Proof.Mont.AArch64.P521Field
