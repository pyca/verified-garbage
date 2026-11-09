module

-- separate module: the selector write frame is reconciled with the field-interpreter invariant before composing the full final window

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishAddPoints
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishLookup
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowLookupPoint
import VerifiedGarbage.Proof.Framework.Block

/-! Final signed digit selection followed by the complete addition. -/

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
