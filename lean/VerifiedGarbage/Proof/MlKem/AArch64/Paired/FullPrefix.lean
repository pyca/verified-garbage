module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.LastStart
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.SqueezeTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Output
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import Std.Tactic.BVDecide.Normalize.Prop
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.LastStart
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.SqueezeTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Output
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import Std.Tactic.BVDecide.Normalize.Prop
meta import VerifiedGarbage.TCB.Axioms

/-! # Complete singleton stream and vector parser entry for relational timing -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Proof.MlKem

structure LastInput (sb ss off : Nat) (p seed out table : Addr) (s : State) : Prop where
 ptr : s.gpr .x28+BitVec.ofNat 64 ss=p
 seedPtr : s.gpr .x28+BitVec.ofNat 64 sb=seed
 outPtr : s.gpr .x28+BitVec.ofNat 64 off=out
 readable : ∀j<4,InRegions (s.rd++s.wr) (seed+BitVec.ofNat 64 (8*j)) 8
 separate : (Region.mk seed 32).Disjoint ⟨p,2048⟩
 context : SingleContext p out table s
 symbol : s.syms "VG_MLKEM_REJ_SHUFFLE"=table

def fullPrefix (sb ss off a k : Nat) : Prog isa :=
 .seq (.seq (.block (Impl.MlKem.AArch64.Paired.fullInit sb ss a k))
   (.loop singleBody (.nonzero .x .x22))) (.block (fullPrep off))
def fullPrefixRegs : List Reg := fullStartRegs++prepRegs

structure FullPrefixPostW (w16 : Bool) (B : Nat→Byte) (p out : Addr) (s t : State) : Prop where
 keep : Keep fullPrefixRegs s t
 entry : Rej8.EntryW w16 [] 280 B (p+400) out t
 pointer : t.gpr .x19=p
 tablePtr : t.gpr .x16=s.syms "VG_MLKEM_REJ_SHUFFLE"

theorem fullPrefix_ok {w16 : Bool} {s initial : State} {p seed out table : Addr} {sb ss off a k : Nat}
    (hss : ss<4096) (hsb : sb+32≤32768) (h8 : sb%8=0) (hoff : off<65536)
    (hk : 0<k) (hk256 : k≤256)
    (h : LastInput sb ss off p seed out table s) (hp : s.gpr .x19=p)
    (sv : Noise.Saved p initial s.mem) :
    WP isa (fullPrefix sb ss off a k) s (FullPrefixPostW w16 (xofByte (seedBytes s.mem seed a k)) p out s) := by
  refine WP.seq (WP.mono_syms (fullStart_ok (a:=a) (k:=k) hss hsb h8 hp h.ptr h.seedPtr h.readable h.context.scratch h.separate sv)
    fun u ⟨ku,fu,_,_,u19,_,_,bu⟩ sy => ?_)
  have cu := h.context.frame ku.rd ku.wr (fu.mono (by simp [fullWrites]))
  refine WP.mono (fullPrep_ok (w16 := w16) hoff u19 (by rw [ku.get .x28]; exact h.outPtr)
    cu.scratch cu.output cu.apart (fun i hi => bu.xof hk hk256 hi)
    (by rw [sy,h.symbol]; exact cu.artifact) (by rw [sy,h.symbol]; exact cu.readable)
    (by rw [sy,h.symbol]; exact cu.tableScratch) (by rw [sy,h.symbol]; exact cu.tableOut)) fun t ⟨kt,_,et,tablePtr⟩ => ?_
  exact ⟨ku.trans kt,et,(kt.get .x19).trans u19,by rw [tablePtr,sy]⟩

theorem fullPrefix_ct {sb ss off a k : Nat} (hss : ss<4096) : ConstantTime isa (fun _=>True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x19,.x28])) (fullPrefix sb ss off a k) := by
  by_cases ho : off<4096
  · apply ct_eraseOff_eq [.x19,.x28]
      (d := Code.eraseOff (fullPrefix 0 0 0 0 1))
      (by simp only [fullPrefix,fullInit_eq hss,fullInit_eq (by decide : 0<4096),fullPrep,fullEntry,
        Impl.MlKem.AArch64.ptrTo,ite_eq_left hss,ite_eq_left ho]; rfl)
    taint_decide
  · apply ct_eraseOff_eq [.x19,.x28]
      (d := Code.eraseOff (fullPrefix 0 0 4096 0 1))
      (by simp only [fullPrefix,fullInit_eq hss,fullInit_eq (by decide : 0<4096),fullPrep,fullEntry,
        Impl.MlKem.AArch64.ptrTo,ite_eq_left hss,ite_eq_right ho]; rfl)
    taint_decide

end VG.Proof.MlKem.AArch64.Paired
