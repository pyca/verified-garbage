module

public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.JointStep
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.X448.AArch64.Fast.Erase
import VerifiedGarbage.Proof.Framework.AArch64.TaintSymMono
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Joint
meta import VerifiedGarbage.Proof.Ed448.AArch64.VerifyCT.Erase
meta import VerifiedGarbage.Proof.X448.AArch64.Fast.Erase
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintSymMono
meta import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Recode
public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Recode
import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.DigitLoads
import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Magnitude
public import VerifiedGarbage.Proof.Framework.RelCT

/-! Sparse additions reveal only the public signed digit, never point coordinates. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse
open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Proof.X448.AArch64 (Scr off)
open VG.Impl.X448.AArch64 (BITS)
open VG.Impl.Ed448.AArch64 (fnCall asFn)

def DigitInput (base:Addr) (i o:Nat) (d:Int) (s:State) : Prop :=
  Scr s base ∧ s.gpr .x19=BitVec.ofNat 64 i ∧
    s.mem (off base (o+i))=BitVec.ofInt 8 d

def DigitPicked (base:Addr) (d:Int) (s:State) : Prop :=
  Scr s base ∧ s.gpr .x11=(BitVec.ofInt 8 d).setWidth 64

/-- The stack and static addresses do not change in either run. -/
def Pinned (sp tbl:Addr) (A:State → Prop) (s:State) : Prop :=
  A s ∧ s.sp=sp ∧ s.syms baseSym=tbl

theorem wp_pinned {sp tbl:Addr} {A B:State → Prop} {p:Prog isa}
    (hw:∀ s,A s → WP isa p s B) {s:State} (h:Pinned sp tbl A s) :
    WP isa p s (Pinned sp tbl B):=by
  obtain ⟨t,u,e,hb⟩:=hw s h.1
  exact ⟨t,u,e,hb,(Exec.sp e).trans h.2.1,by rw [Exec.syms e];exact h.2.2⟩

theorem seq_same {A B:State → Prop} {p q:Prog isa}
    (hp:RelCT isa (fun s t => A s ∧ A t) p (fun _ _ => True))
    (hw:∀ s,A s → WP isa p s B)
    (hq:RelCT isa (fun s t => B s ∧ B t) q (fun _ _ => True)) :
    RelCT isa (fun s t => A s ∧ A t) (.seq p q) (fun _ _ => True):=
  (hp.wp (fun s t h => ⟨hw s h.1,hw t h.2⟩)).seq
    (hq.mono (fun _ _ h => h.2) (fun _ _ h => h))

private theorem picked_agree {base sp tbl:Addr} {d:Int} {s t:State}
    (h:Pinned sp tbl (DigitPicked base d) s ∧ Pinned sp tbl (DigitPicked base d) t) :
    Taint.AgreeS [baseSym] (Taint.ofRegs [.x3,.x11]) s t:=by
  refine ⟨⟨h.1.2.1.trans h.2.2.1.symm,?_⟩,?_⟩
  · intro r hr
    simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.1.x3.trans h.2.1.1.x3.symm
    · exact h.1.1.2.trans h.2.1.2.symm
  · intro n hn
    obtain rfl:=List.mem_singleton.mp hn
    exact h.1.2.2.trans h.2.2.2.symm

private theorem input_agree {base sp tbl:Addr} {i o:Nat} {d:Int} {s t:State}
    (h:Pinned sp tbl (DigitInput base i o d) s ∧ Pinned sp tbl (DigitInput base i o d) t) :
    Taint.AgreeS [baseSym] (Taint.ofRegs [.x3,.x19]) s t:=by
  refine ⟨⟨h.1.2.1.trans h.2.2.1.symm,?_⟩,?_⟩
  · intro r hr
    simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.1.x3.trans h.2.1.1.x3.symm
    · exact h.1.1.2.1.trans h.2.1.2.1.symm
  · intro n hn
    obtain rfl:=List.mem_singleton.mp hn
    exact h.1.2.2.trans h.2.2.2.symm

private theorem key_body_analysis : ∃ h,((taintS [baseSym]).check (Taint.ofRegs [.x3,.x11,.x21])
    (.seq (.block selectKey)
      (.seq (.ite (.nonzero .x .x21) negateSelected (.block [])) VG.Impl.Ed448.AArch64.Point56.addCall)) h).isSome=true:=by
  apply exists_isSome_of_eraseT
  simp only [Code.eraseT,VG.Impl.Ed448.AArch64.Point56.addCall,fnCall,
    VG.Impl.Ed448.AArch64.Point56.addFn,asFn,ops_eraseT]
  refine ⟨?h,?g⟩
  case g => taint_decide

private theorem base_body_analysis : ∃ h,((taintS [baseSym]).check (Taint.ofRegs [.x3,.x11,.x21])
    (.seq (.block selectBase)
      (.seq (.ite (.nonzero .x .x21) negateSelected (.block [])) addAffine)) h).isSome=true:=by
  refine ⟨?h,?g⟩
  case g => taint_decide

def MagnitudePicked (base:Addr) (d:Int) (s:State) : Prop :=
  Scr s base ∧ s.gpr .x11=BitVec.ofNat 64 d.natAbs ∧
    s.gpr .x21=BitVec.ofNat 64 (if d<0 then 1 else 0)

private theorem mag_agree {base sp tbl:Addr} {d:Int} {s t:State}
    (h:Pinned sp tbl (MagnitudePicked base d) s ∧ Pinned sp tbl (MagnitudePicked base d) t) :
    Taint.AgreeS [baseSym] (Taint.ofRegs [.x3,.x11,.x21]) s t:=by
  refine ⟨⟨h.1.2.1.trans h.2.2.1.symm,?_⟩,?_⟩
  · intro r hr
    simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.1.1.1.x3.trans h.2.1.1.x3.symm
    · exact h.1.1.2.1.trans h.2.1.2.1.symm
    · exact h.1.1.2.2.trans h.2.1.2.2.symm
  · intro n hn
    obtain rfl:=List.mem_singleton.mp hn
    exact h.1.2.2.trans h.2.2.2.symm

private theorem conditional_ct (base sp tbl:Addr) (i o:Nat) (d:Int) (head:List Instr) (p:Prog isa)
    (hd:-127≤d ∧ d≤127)
    (load:∀ s,DigitInput base i o d s → WP isa (.block head) s (DigitPicked base d))
    (ha:∃ h,((taintS [baseSym]).check (Taint.ofRegs [.x3,.x19]) (.block head) h).isSome=true)
    (pa:∃ h,((taintS [baseSym]).check (Taint.ofRegs [.x3,.x11,.x21]) p h).isSome=true) :
    RelCT isa (fun s t => Pinned sp tbl (DigitInput base i o d) s ∧
      Pinned sp tbl (DigitInput base i o d) t)
      (.seq (.block head) (.ite (.nonzero .x .x11) (.seq (.block magnitude) p) (.block [])))
      (fun _ _ => True):=by
  obtain ⟨hh,hha⟩:=ha
  obtain ⟨ph,ppa⟩:=pa
  apply seq_same (RelCT.taint (A:=taintS [baseSym]) (Taint.ofRegs [.x3,.x19])
    (fun _ _ h => input_agree h) hha) (fun _ h => wp_pinned load h)
  apply RelCT.ite
  · intro s t h
    simp only [eval,State.read,BitVec.setWidth_eq,h.1.1.2,h.2.1.2]
  · apply seq_same (A:=Pinned sp tbl (DigitPicked base d))
      (RelCT.taint (A:=taintS [baseSym]) (Taint.ofRegs [.x3,.x11])
        (fun _ _ h => picked_agree h) (by taint_decide))
      (fun _ h => wp_pinned (fun s hs => WP.mono (magnitude_ok hd hs.2)
        fun t ⟨t21,t11,tk,_⟩ => ⟨hs.1.of_keeps tk (by decide),t11,t21⟩) h)
      (RelCT.taint (A:=taintS [baseSym]) (Taint.ofRegs [.x3,.x11,.x21])
        (fun _ _ h => mag_agree h) ppa) |>.mono (fun _ _ h => h.1) (fun _ _ h => h)
  · exact RelCT.block_nil (fun _ _ _ => trivial)

theorem addKey_ct (base sp tbl:Addr) (i:Nat) (hi:i<464) (d:Int) (hd:-127≤d ∧ d≤127) :
    RelCT isa (fun s t => Pinned sp tbl (DigitInput base i BITS d) s ∧
      Pinned sp tbl (DigitInput base i BITS d) t) addKey (fun _ _ => True):=by
  unfold addKey
  exact conditional_ct base sp tbl i BITS d keyDigit _ hd
    (fun _ h => WP.mono (keyDigit_ok h.1 hi h.2.1) fun _ ⟨t11,tk,_⟩ =>
      ⟨h.1.of_keeps tk (by decide),by rw [t11,h.2.2]⟩)
    ⟨_,by taint_decide⟩ key_body_analysis

theorem addBase_ct (base sp tbl:Addr) (i:Nat) (hi:i<464) (d:Int) (hd:-127≤d ∧ d≤127) :
    RelCT isa (fun s t => Pinned sp tbl (DigitInput base i SDIG d) s ∧
      Pinned sp tbl (DigitInput base i SDIG d) t) addBase (fun _ _ => True):=by
  unfold addBase
  exact conditional_ct base sp tbl i SDIG d baseDigit _ hd
    (fun _ h => WP.mono (baseDigit_ok h.1 hi h.2.1) fun _ ⟨t11,tk,_⟩ =>
      ⟨h.1.of_keeps tk (by decide),by rw [t11,h.2.2]⟩)
    ⟨_,by taint_decide⟩ base_body_analysis

end VG.Proof.Ed448.AArch64.Sparse
