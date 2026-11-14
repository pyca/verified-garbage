module

-- separate module: canonical projective infinity correction is independent of signed table lookup and complete addition

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishProjective
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishCopy
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishFixY
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishFrames
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.DoubleOutput
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontSaves
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-! Canonical projective preparation preserves infinity, including Z=0. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass
open VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

def finishProjectivePrepare : Prog isa := .seq (.block finishCopyPoint)
  (.seq finishProjectiveMachine (.seq (.block finishCopyPoint) (.block finishFixYCode)))

def finishProjectiveWrites : List (Nat × Nat) :=
  [(1072,72),(1144,72),(1216,72)]++fieldProgramWrites id finishProjectiveOps++
    [(1072,72),(1144,72),(1216,72),(1144,72)]

theorem canonical_fin_zero {p a : Nat} [NeZero p] (bound : a<p) :
    Fin.ofNat p a=0 ↔ a=0 := by
  constructor
  · intro h
    have value := congrArg Fin.val h
    change a%p=0 at value
    rwa [Nat.mod_eq_of_lt bound] at value
  · rintro rfl; rfl

/-- Exact field environment before the ordinate correction, followed by its
canonical zero/infinity correction and the complete memory write frame. -/
theorem finish_projective_prepare_ok {base : Addr} {s : State} (hs : Scr s base 8192)
    (bound : canonicalPoint s.mem base 1288) (zero : wordsVal s.mem base 280 9=0)
    (oneBound : 1<fieldPrime) :
    WP isa finishProjectivePrepare s fun t => ∃E : Nat → Fin fieldPrime,
      (E 1072,E 1144,E 1216)=ordinaryPoint s.mem base 1288 ∧
      canonicalPoint t.mem base 1072 ∧
      Fin.ofNat fieldPrime (wordsVal t.mem base 1072 9)=pointRun finishProjectiveOps E 1288 ∧
      Fin.ofNat fieldPrime (wordsVal t.mem base 1144 9)=
        (if pointRun finishProjectiveOps E 1432=0 then Fin.ofNat fieldPrime 1 else pointRun finishProjectiveOps E 1360) ∧
      Fin.ofNat fieldPrime (wordsVal t.mem base 1216 9)=pointRun finishProjectiveOps E 1432 ∧
      E 280=0 ∧ Scr t base 8192 ∧
      Unch base finishProjectiveWrites s.mem t.mem ∧
      t.gpr .x19=s.gpr .x19 ∧ t.gpr .x20=s.gpr .x20 ∧ t.gpr .x26=s.gpr .x26 ∧
      FieldPublic s t := by
  rw [finishProjectivePrepare,WP.seq_iff]
  refine WP.mono (VG.Proof.Weierstrass.AArch64.Mont.WP.block_novec (by decide)
    (finish_copy_point_ok hs)) fun u ⟨⟨xu,yu,zu,ku,uc⟩,vu⟩ => ?_
  have hu := hs.of_keepRegs ku (by decide)
  let E : Nat → Fin fieldPrime := fun d => Fin.ofNat fieldPrime (wordsVal u.mem base d 9)
  have zeroU : wordsVal u.mem base 280 9=0 := by rw [uc.wordsVal (by decide) (by decide),zero]
  have env : OrdinaryInv base fieldPrime id [1072,1144,1216,280] E (fun _ => 1) u := by
    constructor
    · intro d hd
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
      rcases hd with rfl|rfl|rfl|rfl
      · simpa only [id_eq,Nat.one_mul,xu] using bound.1
      · simpa only [id_eq,Nat.one_mul,yu] using bound.2.1
      · simpa only [id_eq,Nat.one_mul,zu] using bound.2.2
      · simpa only [id_eq,Nat.one_mul,zeroU] using (Nat.lt_trans (by decide : 0<1) oneBound)
    · intro d _; rfl
  have core := field_program_ok (by decide) (by decide) build_field_layout finishProjectiveOps hu env
    (by simp [buildSlot])
    (by simp [finishProjectiveOps,PointOp.out,PointOp.ins,buildSlot])
    (by decide) (by simp [finishProjectiveOps,fieldCoeffs])
  rw [WP.seq_iff]
  refine WP.mono (finish_projective_machine_wp.mpr core) fun v ⟨iv,hv,kv,fv⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (VG.Proof.Weierstrass.AArch64.Mont.WP.block_novec (by decide)
    (finish_copy_point_ok hv)) fun w ⟨⟨xw,yw,zw,kw,vw⟩,vvec⟩ => ?_
  have hw := hv.of_keepRegs kw (by decide)
  refine WP.mono (VG.Proof.Weierstrass.AArch64.Mont.WP.block_novec (by decide)
    (finish_fix_y_ok hw)) fun t ⟨⟨yt,kt,wt⟩,tvec⟩ => ?_
  have xBound := iv.bound 1288 (by decide)
  have yBound := iv.bound 1360 (by decide)
  have zBound := iv.bound 1432 (by decide)
  have xValue := iv.value 1288 (by decide)
  have yValue := iv.value 1360 (by decide)
  have zValue := iv.value 1432 (by decide)
  change Fin.ofNat fieldPrime (wordsVal v.mem base 1288 9)=pointRun finishProjectiveOps E 1288 at xValue
  change Fin.ofNat fieldPrime (wordsVal v.mem base 1360 9)=pointRun finishProjectiveOps E 1360 at yValue
  change Fin.ofNat fieldPrime (wordsVal v.mem base 1432 9)=pointRun finishProjectiveOps E 1432 at zValue
  have zWBound : wordsVal w.mem base 1216 9<fieldPrime := by rw [zw]; simpa only [id_eq,Nat.one_mul] using zBound
  have zEq : wordsVal w.mem base 1216 9=0 ↔ pointRun finishProjectiveOps E 1432=0 := by
    rw [←canonical_fin_zero zWBound,zw,zValue]
  have allU : Unch base finishProjectiveWrites s.mem t.mem :=
    uc.trans ((field_program_frame_unch fv).trans (vw.trans wt.unch))
  refine ⟨E,?_,?_,?_,?_,?_,?_,hw.of_keepRegs kt (by decide),allU,?_,?_,?_,?_⟩
  · change (Fin.ofNat fieldPrime (wordsVal u.mem base 1072 9),Fin.ofNat fieldPrime (wordsVal u.mem base 1144 9),
      Fin.ofNat fieldPrime (wordsVal u.mem base 1216 9))=_
    rw [xu,yu,zu]
    rfl
  · constructor
    · rw [wt.wordsVal (by decide) (by decide),xw]; simpa only [id_eq,Nat.one_mul] using xBound
    · constructor
      · rw [yt]
        split
        · exact oneBound
        · rw [yw]; simpa only [id_eq,Nat.one_mul] using yBound
      · rw [wt.wordsVal (by decide) (by decide),zw]; simpa only [id_eq,Nat.one_mul] using zBound
  · rw [wt.wordsVal (by decide) (by decide),xw]; exact xValue
  · rw [yt]
    by_cases hz : wordsVal w.mem base 1216 9=0
    · simp only [hz,ite_true,zEq.mp hz]
    · simp only [hz,ite_false,show pointRun finishProjectiveOps E 1432≠0 from fun e => hz (zEq.mpr e)]
      rw [yw]; exact yValue
  · rw [wt.wordsVal (by decide) (by decide),zw]; exact zValue
  · change Fin.ofNat fieldPrime (wordsVal u.mem base 280 9)=0
    rw [zeroU]; rfl
  · exact (kt.gpr .x19 (by decide)).trans ((kw.gpr .x19 (by decide)).trans ((kv.gpr .x19 (by decide)).trans (ku.gpr .x19 (by decide))))
  · exact (kt.gpr .x20 (by decide)).trans ((kw.gpr .x20 (by decide)).trans ((kv.gpr .x20 (by decide)).trans (ku.gpr .x20 (by decide))))
  · exact (kt.gpr .x26 (by decide)).trans ((kw.gpr .x26 (by decide)).trans ((kv.gpr .x26 (by decide)).trans (ku.gpr .x26 (by decide))))

  · constructor
    · intro r hr
      have outside : r∉[Reg.x1,.x2,.x4,.x5,.x7,.x9,.x16] :=
        (by decide : ∀r∈fieldPublicRegs,r∉[Reg.x1,.x2,.x4,.x5,.x7,.x9,.x16]) r hr
      have not1 : r∉[Reg.x1] := (by decide : ∀r∈fieldPublicRegs,r∉[Reg.x1]) r hr
      exact (kt.gpr r outside).trans ((kw.gpr r not1).trans ((kv.gpr r hr).trans (ku.gpr r not1)))
    · exact kt.sp.trans (kw.sp.trans (kv.sp.trans ku.sp))
    · exact kt.rd.trans (kw.rd.trans (kv.rd.trans ku.rd))
    · exact kt.wr.trans (kw.wr.trans (kv.wr.trans ku.wr))
    · exact (congrFun tvec .v31).trans ((congrFun vvec .v31).trans (kv.v31.trans (congrFun vu .v31)))

end VG.Proof.Weierstrass.AArch64.P521Native
