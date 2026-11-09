module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishAddCode
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishFrames
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.DoubleOutput
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishLookup
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowLookupPoint
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishFrontReady

/-! Adjacent stages of the final P-521 window, sharing their machine-state interface. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass
open VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

theorem finish_add_points_ok {base : Addr} {s : State} (hs : Scr s base 8192)
    (bp : canonicalPoint s.mem base 1072) (bq : canonicalPoint s.mem base 1504)
    (bb : wordsVal s.mem base 568 9<fieldPrime) :
    WP isa finishAddMachine s fun t =>
      canonicalPoint t.mem base 1288 ∧
      ordinaryPoint t.mem base 1288=rcbAdd3 (Fin.ofNat fieldPrime (wordsVal s.mem base 568 9))
        (ordinaryPoint s.mem base 1072).1 (ordinaryPoint s.mem base 1072).2.1 (ordinaryPoint s.mem base 1072).2.2
        (ordinaryPoint s.mem base 1504).1 (ordinaryPoint s.mem base 1504).2.1 (ordinaryPoint s.mem base 1504).2.2 ∧
      Scr t base 8192 ∧ FieldPublic s t ∧ Unch base (fieldProgramWrites id finishAddOps) s.mem t.mem := by
  let E : Nat → Fin fieldPrime := fun d => Fin.ofNat fieldPrime (wordsVal s.mem base d 9)
  have inv : OrdinaryInv base fieldPrime id [1072,1144,1216,1504,1576,1648,568] E (fun _ => 1) s := by
    constructor
    · intro d hd
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
      rcases hd with rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · simpa only [id_eq,Nat.one_mul] using bp.1
      · simpa only [id_eq,Nat.one_mul] using bp.2.1
      · simpa only [id_eq,Nat.one_mul] using bp.2.2
      · simpa only [id_eq,Nat.one_mul] using bq.1
      · simpa only [id_eq,Nat.one_mul] using bq.2.1
      · simpa only [id_eq,Nat.one_mul] using bq.2.2
      · simpa only [id_eq,Nat.one_mul] using bb
    · intro d _; rfl
  refine WP.mono (finish_add_machine_ok hs inv) fun t ⟨it,ht,kt,ft⟩ => ?_
  have xb := it.bound 1288 (by decide)
  have yb := it.bound 1360 (by decide)
  have zb := it.bound 1432 (by decide)
  have xv := it.value 1288 (by decide)
  have yv := it.value 1360 (by decide)
  have zv := it.value 1432 (by decide)
  change Fin.ofNat fieldPrime (wordsVal t.mem base 1288 9)=pointRun finishAddOps E 1288 at xv
  change Fin.ofNat fieldPrime (wordsVal t.mem base 1360 9)=pointRun finishAddOps E 1360 at yv
  change Fin.ofNat fieldPrime (wordsVal t.mem base 1432 9)=pointRun finishAddOps E 1432 at zv
  refine ⟨⟨by simpa only [id_eq,Nat.one_mul] using xb,
    by simpa only [id_eq,Nat.one_mul] using yb,by simpa only [id_eq,Nat.one_mul] using zb⟩,?_,ht,kt,field_program_frame_unch ft⟩
  change (Fin.ofNat fieldPrime (wordsVal t.mem base 1288 9),Fin.ofNat fieldPrime (wordsVal t.mem base 1360 9),
    Fin.ofNat fieldPrime (wordsVal t.mem base 1432 9))=_
  rw [xv,yv,zv,finishAdd_value]
  rfl

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass
open VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

def finishSelectedSum : Prog isa := .seq (.block finishLookupCode) finishAddMachine
def finishSelectedWrites : List (Nat × Nat) :=
  [(1504,216),(2224,72)]++fieldProgramWrites id finishAddOps

theorem finish_selected_sum_ok {base table : Addr} {s : State} {k : Nat}
    (hs : Scr s base 8192) (bp : canonicalPoint s.mem base 1072)
    (bb : wordsVal s.mem base 568 9<fieldPrime)
    (ht : LookupTableReadable s table) (zero : wordsVal s.mem base 280 9=0)
    (canonical : WindowTableCanonical s.mem table) (counter : s.gpr .x19=0#64)
    (bits : ∀t<525,s.mem (off base (3304+t))=if k.testBit t then 1 else 0) :
    WP isa finishSelectedSum s fun t =>
      canonicalPoint t.mem base 1288 ∧
      ordinaryPoint t.mem base 1288=rcbAdd3 (Fin.ofNat fieldPrime (wordsVal s.mem base 568 9))
        (ordinaryPoint s.mem base 1072).1 (ordinaryPoint s.mem base 1072).2.1 (ordinaryPoint s.mem base 1072).2.2
        (windowAffine s.mem table k 0).1 (windowAffine s.mem table k 0).2.1 (windowAffine s.mem table k 0).2.2 ∧
      Scr t base 8192 ∧ FieldPublic s t ∧ Unch base finishSelectedWrites s.mem t.mem := by
  rw [finishSelectedSum,WP.seq_iff,finish_lookup_source,window_lookup_source]
  refine WP.mono (window_lookup_point_ok hs (by decide) (by decide : 0<105) ht zero canonical counter bits)
    fun u ⟨bq,qv,hu,ku,_,fu,_⟩ => ?_
  have pSame : ordinaryPoint u.mem base 1072=ordinaryPoint s.mem base 1072 := by
    simp only [ordinaryPoint]
    rw [fu.wordsVal (by decide) (by decide) (by decide),fu.wordsVal (by decide) (by decide) (by decide),
      fu.wordsVal (by decide) (by decide) (by decide)]
  have bpu : canonicalPoint u.mem base 1072 := by
    change wordsVal u.mem base 1072 9<fieldPrime ∧ wordsVal u.mem base 1144 9<fieldPrime ∧ wordsVal u.mem base 1216 9<fieldPrime
    rw [fu.wordsVal (by decide) (by decide) (by decide),fu.wordsVal (by decide) (by decide) (by decide),
      fu.wordsVal (by decide) (by decide) (by decide)]
    exact bp
  have bSame : wordsVal u.mem base 568 9=wordsVal s.mem base 568 9 := fu.wordsVal (by decide) (by decide) (by decide)
  have bbu : wordsVal u.mem base 568 9<fieldPrime := by rw [bSame]; exact bb
  have uf : Unch base [(1504,216),(2224,72)] s.mem u.mem := by
    intro x hx
    exact fu x (hx (1504,216) (by simp)) (hx (2224,72) (by simp))
  refine WP.mono (finish_add_points_ok hu bpu bq bbu) fun t ⟨bt,pt,ht,kt,ut⟩ => ?_
  rw [pSame,qv,bSame] at pt
  exact ⟨bt,pt,ht,ku.trans kt,uf.trans ut⟩

end VG.Proof.Weierstrass.AArch64.P521Native

end

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

end
