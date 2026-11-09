module

-- separate module: the canonical coordinate contract is independent of signed digit selection and keeps the field-interpreter invariant local

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishAddCode
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishFrames
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.DoubleOutput
import VerifiedGarbage.Proof.Framework.Omega

/-! Complete final addition on canonical ordinary point coordinates. -/

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
