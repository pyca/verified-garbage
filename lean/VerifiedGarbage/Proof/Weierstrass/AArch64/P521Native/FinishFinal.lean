module

-- separate module: checked API serialization is isolated from the final-window composition and its field/table invariants

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishFinalize
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishChecks
import VerifiedGarbage.Proof.Ecdsa.AArch64.Finish
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Block

/-! From an arbitrary canonical final projective sum to checked API output. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64.P521Field (toMontValue_zero_iff)
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Impl.Weierstrass.AArch64.P521Native (config)

def finishFinal : Prog isa := .seq finalizeCore (.block
  (config.checkRange (config.sl D)++config.checkNonzero (config.sl RZ)++VG.Impl.Ecdh.AArch64.Cfg.finish config))

def finishAccept (base : Addr) (s : State) (V : Prop) [Decidable V] : Bool :=
  decide ((V ∧ 0<wordsVal s.mem base 2368 9 ∧ wordsVal s.mem base 2368 9<config.C.n) ∧
    wordsVal s.mem base 1432 9≠0)

theorem finish_final_ok (hc : BaseCfgOk config) {base : Addr} {s : State}
    (hs : Scr s base 8192) (hM : ModOkA config.MP' 8192 config.C.p s.mem base)
    (bounds : ∀d∈[1288,1360,1432,352],wordsVal s.mem base d 9<fieldPrime)
    {g : Reg → BitVec 64} (saved : Spill.Saved base g Cfg.saved s.mem)
    (mn : wordsVal s.mem base 136 9=config.C.n)
    {V : Prop} [Decidable V] (flag : word s.mem base 3232=mask V) {out : Addr}
    (outReg : s.gpr .x20=out) (outFit : out.toNat+66≤2^64)
    (outW : (⟨out,66⟩ : Region)∈s.wr) (outApart : Region.Disjoint ⟨out,66⟩ ⟨base,8192⟩) :
    WP isa finishFinal s fun t => ∃xv,xv<fieldPrime ∧
      Fin.ofNat fieldPrime xv=
        Fin.ofNat fieldPrime (wordsVal s.mem base 1288 9)*
        Fin.ofNat fieldPrime (wordsVal s.mem base 1432 9)^(fieldPrime-2)*
        Fin.ofNat fieldPrime (wordsVal s.mem base 352 9) ∧
      VG.Spec.Ecdsa.bytesAt t.mem out 66=(if finishAccept base s V then VG.Spec.Weierstrass.toBytes 66 xv else List.replicate 66 0) ∧
      (t.gpr .x0).setWidth 32=(if finishAccept base s V then 1 else 0) ∧
      (∀r∈Cfg.saved.map Prod.fst,t.gpr r=g r) ∧
      t.rd=s.rd ∧ t.wr=s.wr ∧ t.sp=s.sp ∧ t.gpr .x27=s.gpr .x27 ∧ t.gpr .x28=s.gpr .x28 ∧ t.v .v31=s.v .v31 := by
  rw [finishFinal,WP.seq_iff]
  refine WP.mono (finalize_core_ok hc hs hM bounds)
    fun u ⟨hu,bound,value,converted,frame,zero,rd,wr,sp,g20,g26,g30,g27,g28,v31⟩ => ?_
  have mnu : wordsVal u.mem base 136 9=config.C.n := by
    rw [frame.wordsVal (by decide) (by decide)]; exact mn
  have savedU := Saved.unch saved (W:=finalizeWrites) (by decide) frame
  have flagU : word u.mem base 3232=mask V := by
    rw [frame.word (by decide) (by decide)]; exact flag
  have outU : u.gpr .x20=out := g20.trans outReg
  have wrU : (⟨out,66⟩ : Region)∈u.wr := by rw [wr]; exact outW
  have dSame : wordsVal u.mem base 2368 9=wordsVal s.mem base 2368 9 := frame.wordsVal (by decide) (by decide)
  have accept : VG.Proof.Ecdh.AArch64.ok config base u V=finishAccept base s V := by
    simp only [VG.Proof.Ecdh.AArch64.ok,sv,finishAccept,
      (show config.n=9 from rfl),(show config.sl D=2368 from rfl),(show config.sl RZ=1216 from rfl)]
    rw [dSame,converted]
    simp only [ne_eq,toMontValue_zero_iff (bounds 1432 (by simp))]
  obtain ⟨trace,t,exec,bytes,ret,restored⟩ := checked_finish_ok hc hu mnu savedU flagU outU outFit wrU outApart
  let code : List Instr := config.checkRange (config.sl D)++config.checkNonzero (config.sl RZ)++VG.Impl.Ecdh.AArch64.Cfg.finish config
  have check27 : code.all (fun i => decide (clobbers i .x27=false))=true := by lit_decide
  have check28 : code.all (fun i => decide (clobbers i .x28=false))=true := by lit_decide
  have checkV : code.all (fun i => decide (vdstOf i≠some .v31))=true := by lit_decide
  have hc27 : ∀i∈instrs (.block code : Prog isa),clobbers i .x27=false := by
    simpa only [instrs,List.all_eq_true,decide_eq_true_eq] using check27
  have hc28 : ∀i∈instrs (.block code : Prog isa),clobbers i .x28=false := by
    simpa only [instrs,List.all_eq_true,decide_eq_true_eq] using check28
  have hcV : ∀i∈instrs (.block code : Prog isa),vdstOf i≠some .v31 := by
    simpa only [instrs,List.all_eq_true,decide_eq_true_eq] using checkV
  have regions := Exec.rdwr exec
  refine ⟨trace,t,exec,_,bound,value,?_,?_,restored,regions.1.trans rd,regions.2.1.trans wr,regions.2.2.trans sp,
    (Exec.gpr hc27 exec).trans g27,(Exec.gpr hc28 exec).trans g28,(Exec.vec hcV exec).trans v31⟩
  · simpa only [(show config.C.len=66 from rfl),sv,(show config.n=9 from rfl),
      (show config.sl X=2584 from rfl),accept] using bytes
  · rw [ret,accept]

end VG.Proof.Weierstrass.AArch64.P521Native
