module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishReadonly
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishProjectiveState
import VerifiedGarbage.Proof.Framework.Block

/-! Five doubles and canonical homogeneous conversion leave final lookup ready. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass
open VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Impl.Weierstrass.AArch64.P521Native (outerBlock144)

def finishDbl5 (P : Fin fieldPrime×Fin fieldPrime×Fin fieldPrime) :=
  windowDbl (windowDbl (windowDbl (windowDbl (windowDbl P))))
def finishHomogeneous (P : Fin fieldPrime×Fin fieldPrime×Fin fieldPrime) :=
  (P.1*P.2.2,(if P.2.2*P.2.2*P.2.2=0 then Fin.ofNat fieldPrime 1 else P.2.1),P.2.2*P.2.2*P.2.2)
def finishFrontReady : Prog isa :=
  .seq (.seq (.block outerBlock144) finishFiveDoubles) finishProjectivePrepare
def finishFrontWrites : List (Nat × Nat) := [(1072,432),(4080,504)]++finishProjectiveWrites

theorem finish_front_ready_ok {s : State} {table : Addr} {k : Nat}
    (hs : Scr s (s.gpr .x0) 8192) (bound : canonicalPoint s.mem (s.gpr .x0) 1072)
    (counter : s.gpr .x19=1#64) (zero : wordsVal s.mem (s.gpr .x0) 280 9=0)
    (bb : wordsVal s.mem (s.gpr .x0) 568 9<fieldPrime) (oneBound : 1<fieldPrime)
    (apart : TableWorkspaceApart (s.gpr .x0) table 8192) (tableRead : LookupTableReadable s table)
    (canonical : WindowTableCanonical s.mem table)
    (bits : ∀i<525,s.mem (off (s.gpr .x0) (3304+i))=if k.testBit i then 1 else 0) :
    WP isa finishFrontReady s fun t =>
      canonicalPoint t.mem (s.gpr .x0) 1072 ∧
      ordinaryPoint t.mem (s.gpr .x0) 1072=finishHomogeneous (finishDbl5 (ordinaryPoint s.mem (s.gpr .x0) 1072)) ∧
      Scr t (s.gpr .x0) 8192 ∧ LookupTableReadable t table ∧ WindowTableCanonical t.mem table ∧
      (∀i<525,t.mem (off (s.gpr .x0) (3304+i))=if k.testBit i then 1 else 0) ∧
      wordsVal t.mem (s.gpr .x0) 280 9=0 ∧ wordsVal t.mem (s.gpr .x0) 568 9<fieldPrime ∧
      t.gpr .x19=0#64 ∧ t.gpr .x20=s.gpr .x20 ∧ t.gpr .x26=s.gpr .x26 ∧
      Unch (s.gpr .x0) finishFrontWrites s.mem t.mem ∧
      t.rd=s.rd ∧ t.wr=s.wr ∧ t.sp=s.sp ∧ t.gpr .x27=s.gpr .x27 ∧ t.gpr .x28=s.gpr .x28 ∧ t.v .v31=s.v .v31 := by
  rw [finishFrontReady,WP.seq_iff]
  refine WP.mono (finish_five_doubles_ok hs (by decide) bound counter)
    fun u ⟨bu,pu,fu,ku,cu⟩ => ?_
  have uf := finish_double_frame_unch fu
  have hu : Scr u (s.gpr .x0) 8192 := by rw [←ku.base]; exact ku.scr hs
  have zeroU : wordsVal u.mem (s.gpr .x0) 280 9=0 := by rw [uf.wordsVal (by decide) (by decide),zero]
  refine WP.mono (finish_projective_prepare_ok hu bu zeroU oneBound)
    fun t ⟨E,ep,bt,xv,yv,zv,ez,ht,ut,c19,c20,c26,pub⟩ => ?_
  have allU : Unch (s.gpr .x0) finishFrontWrites s.mem t.mem := uf.trans ut
  have fits : ∀w∈finishFrontWrites,w.1+w.2≤8192 := by decide
  have point : ordinaryPoint t.mem (s.gpr .x0) 1072=finishHomogeneous (finishDbl5 (ordinaryPoint s.mem (s.gpr .x0) 1072)) := by
    have coords := ep.trans pu
    change (E 1072,E 1144,E 1216)=finishDbl5 (ordinaryPoint s.mem (s.gpr .x0) 1072) at coords
    rw [←coords]
    have eval := finish_projective_value E ez
    have ex := congrArg Prod.fst eval
    have ey := congrArg (fun P => P.2.1) eval
    have ezz := congrArg (fun P => P.2.2) eval
    dsimp only at ex ey ezz
    change (Fin.ofNat fieldPrime (wordsVal t.mem (s.gpr .x0) 1072 9),
      Fin.ofNat fieldPrime (wordsVal t.mem (s.gpr .x0) 1144 9),
      Fin.ofNat fieldPrime (wordsVal t.mem (s.gpr .x0) 1216 9))=_
    rw [xv,yv,zv,ex,ey,ezz]
    rfl
  have readT : LookupTableReadable t table := by
    constructor
    · exact c26.trans ((ku.gp .x26 (by decide) (by decide) (by decide)).trans tableRead.reg)
    · intro d hd
      rw [pub.rd,pub.wr,ku.rd,ku.wr]
      exact tableRead.read d hd
  refine ⟨bt,point,ht,readT,finish_table_canonical_keep apart allU fits canonical,
    finish_bits_keep allU (by decide) bits,?_,?_,c19.trans cu,?_,?_,allU,pub.rd.trans ku.rd,pub.wr.trans ku.wr,pub.sp.trans ku.sp,?_,?_,?_⟩
  · rw [allU.wordsVal (by decide) (by decide),zero]
  · rw [allU.wordsVal (by decide) (by decide)]; exact bb
  · exact c20.trans (ku.gp .x20 (by decide) (by decide) (by decide))
  · exact c26.trans (ku.gp .x26 (by decide) (by decide) (by decide))

  · exact (pub.gpr .x27 (by decide)).trans (ku.gp .x27 (by decide) (by decide) (by decide))
  · exact (pub.gpr .x28 (by decide)).trans (ku.gp .x28 (by decide) (by decide) (by decide))
  · exact pub.v31.trans ku.v31

end VG.Proof.Weierstrass.AArch64.P521Native
