module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishFrontReady
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishSelectedSum
import VerifiedGarbage.Proof.Framework.Block

/-! The entire final arithmetic front, including the signed zero digit. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass
open VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

def finishFront : Prog isa := .seq finishFrontReady finishSelectedSum
def finishAllFrontWrites := finishFrontWrites++finishSelectedWrites

def finishSum (m : Mem) (base table : Addr) (k : Nat) :=
  let P := finishHomogeneous (finishDbl5 (ordinaryPoint m base 1072))
  let Q := windowAffine m table k 0
  rcbAdd3 (Fin.ofNat fieldPrime (wordsVal m base 568 9)) P.1 P.2.1 P.2.2 Q.1 Q.2.1 Q.2.2

theorem finish_front_ok {s : State} {table : Addr} {k : Nat}
    (hs : Scr s (s.gpr .x0) 8192) (bound : canonicalPoint s.mem (s.gpr .x0) 1072)
    (counter : s.gpr .x19=1#64) (zero : wordsVal s.mem (s.gpr .x0) 280 9=0)
    (bb : wordsVal s.mem (s.gpr .x0) 568 9<fieldPrime) (oneBound : 1<fieldPrime)
    (apart : TableWorkspaceApart (s.gpr .x0) table 8192) (tableRead : LookupTableReadable s table)
    (canonical : WindowTableCanonical s.mem table)
    (bits : ∀i<525,s.mem (off (s.gpr .x0) (3304+i))=if k.testBit i then 1 else 0) :
    WP isa finishFront s fun t =>
      canonicalPoint t.mem (s.gpr .x0) 1288 ∧
      ordinaryPoint t.mem (s.gpr .x0) 1288=finishSum s.mem (s.gpr .x0) table k ∧
      Scr t (s.gpr .x0) 8192 ∧ Unch (s.gpr .x0) finishAllFrontWrites s.mem t.mem ∧
      t.rd=s.rd ∧ t.wr=s.wr ∧ t.sp=s.sp ∧ t.gpr .x20=s.gpr .x20 ∧ t.gpr .x26=s.gpr .x26 ∧
      t.gpr .x27=s.gpr .x27 ∧ t.gpr .x28=s.gpr .x28 ∧ t.v .v31=s.v .v31 := by
  rw [finishFront,WP.seq_iff]
  refine WP.mono (finish_front_ready_ok hs bound counter zero bb oneBound apart tableRead canonical bits)
    fun u ⟨bp,pv,hu,rt,ct,bt,zu,bu,cu,g20,g26,uf,rd,wr,sp,g27,g28,v31⟩ => ?_
  have tableSame := finish_affine_keep apart uf (by decide) k 0
  have bSame : wordsVal u.mem (s.gpr .x0) 568 9=wordsVal s.mem (s.gpr .x0) 568 9 := uf.wordsVal (by decide) (by decide)
  refine WP.mono (finish_selected_sum_ok hu bp bu rt zu ct cu bt) fun t ⟨boundT,value,ht,kt,ut⟩ => ?_
  rw [pv,tableSame,bSame] at value
  refine ⟨boundT,value,ht,uf.trans ut,kt.rd.trans rd,kt.wr.trans wr,kt.sp.trans sp,?_,?_,?_,?_,kt.v31.trans v31⟩
  · exact (kt.gpr .x20 (by decide)).trans g20
  · exact (kt.gpr .x26 (by decide)).trans g26
  · exact (kt.gpr .x27 (by decide)).trans g27
  · exact (kt.gpr .x28 (by decide)).trans g28

end VG.Proof.Weierstrass.AArch64.P521Native
