module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsFoldWords
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionBits
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionArithmetic
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionCorrect
import VerifiedGarbage.Proof.Framework.Block

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64.P521Square (value value_append)

theorem cms_scalar_split (s : State) : regsVal s cmsScalarRegs=regsVal s cmsLowOut+2^512*(s.gpr .x11).toNat := by
  have hs : cmsScalarRegs=cmsLowOut++[.x11] := rfl
  rw [hs,regsVal_append]
  simp only [show cmsLowOut.length=8 from by decide,Nat.reduceMul,regsVal,Nat.mul_zero,Nat.add_zero]

theorem cms_fold_extended_length (s : State) : (cmsFoldExtended s).length=9 := by
  simp only [cmsFoldExtended,List.length_append,List.length_map,show cmsLowOut.length=8 from by decide,
    List.length_cons,List.length_nil]

theorem cms_fold_addend_length (s : State) : (cmsFoldAddend s).length=9 := rfl

theorem cms_fold_extended_value (s : State) :
    value (cmsFoldExtended s)=regsVal s cmsScalarRegs%(2^521)+(2^576-2^521) := by
  have hmask : (0 : Word)-512#64=(BitVec.ofNat 64 (2^64-1) <<< 9) := by decide
  have ho := P521Square.orHigh9_value (s.gpr .x11)
  have hl : regsVal s cmsLowOut<2^512 := by
    simpa only [show cmsLowOut.length=8 from by decide,Nat.reduceMul] using regsVal_lt s cmsLowOut
  rw [cmsFoldExtended,value_append,List.length_map,show cmsLowOut.length=8 from by decide,value_map_gpr]
  simp only [Nat.reduceMul,value,Nat.mul_zero,Nat.add_zero,cmsFoldTop,hmask]
  have hs := cms_scalar_split s
  omega_using [ho,hl,hs]

theorem cms_fold_high_value (s : State) : (cmsFoldHigh s).toNat=regsVal s cmsScalarRegs/(2^521) := by
  have hs := cms_scalar_split s
  have hl : regsVal s cmsLowOut<2^512 := by
    simpa only [show cmsLowOut.length=8 from by decide,Nat.reduceMul] using regsVal_lt s cmsLowOut
  simp only [cmsFoldHigh,BitVec.toNat_ushiftRight]
  omega_using [hs,hl]

theorem cms_fold_addend_value (s : State) : value (cmsFoldAddend s)=regsVal s cmsScalarRegs/(2^521) := by
  have hz : value (List.replicate 8 (0 : Word))=0 := by decide
  simp only [cmsFoldAddend,value,hz,Nat.mul_zero,Nat.add_zero,cms_fold_high_value]

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64
open VG.Proof.Mont.AArch64.P521Square (value value_lt addWords addWords_length addWords_value)

theorem cms_fold_detect_eq (s : State) (hm : s.gpr .x15=cmsAndWords (cmsMiddleRegs.map s.gpr)) :
    cmsFoldDetect s=(addWords (cmsFoldExtended s) (cmsFoldAddend s) true).2 := by
  have h := cms_compressed_carry (s.gpr .x3) (cmsFoldHigh s) (cmsFoldTop s) (cmsMiddleRegs.map s.gpr) true
  have he : cmsFoldExtended s=s.gpr .x3::(cmsMiddleRegs.map s.gpr++[cmsFoldTop s]) := rfl
  have ha : cmsFoldAddend s=cmsFoldHigh s::List.replicate ((cmsMiddleRegs.map s.gpr).length+1) 0 := rfl
  rw [he,ha]
  dsimp only [cmsFoldDetect]
  rw [hm]
  exact h.symm

theorem cms_fold_detect_value (s : State) (hm : s.gpr .x15=cmsAndWords (cmsMiddleRegs.map s.gpr)) :
    value (addWords (cmsFoldExtended s) (cmsFoldAddend s) true).1+2^576*(cmsFoldDetect s).toNat=
      (2^576-2^521)+(regsVal s cmsScalarRegs%(2^521)+regsVal s cmsScalarRegs/(2^521))+1 := by
  have e := addWords_value (cmsFoldExtended s) (cmsFoldAddend s) true
    (by rw [cms_fold_extended_length,cms_fold_addend_length])
  rw [cms_fold_extended_length,←cms_fold_detect_eq s hm,cms_fold_extended_value,cms_fold_addend_value] at e
  simp only [Nat.reduceMul,Bool.toNat_true] at e
  omega_using [e]

theorem cms_fold_detect_bound (s : State) : value (addWords (cmsFoldExtended s) (cmsFoldAddend s) true).1<2^576 := by
  have hl := addWords_length (cmsFoldExtended s) (cmsFoldAddend s) true
    (by rw [cms_fold_extended_length,cms_fold_addend_length])
  rw [cms_fold_extended_length] at hl
  simpa only [hl,Nat.reduceMul] using value_lt (addWords (cmsFoldExtended s) (cmsFoldAddend s) true).1

theorem cms_fold_detect_flag (s : State) (hm : s.gpr .x15=cmsAndWords (cmsMiddleRegs.map s.gpr)) :
    cmsFoldDetect s=decide (2^521-1≤regsVal s cmsScalarRegs%(2^521)+regsVal s cmsScalarRegs/(2^521)) := by
  have e := cms_fold_detect_value s hm
  have ho := cms_fold_detect_bound s
  have hF : 0<(2:Nat)^521 := by lit_decide
  have hR : (2:Nat)^521≤2^576 := by lit_decide
  generalize hf : (2:Nat)^521=F at e hF hR ⊢
  generalize hr : (2:Nat)^576=R at e ho hR
  exact cms_detect_field hF hR ho e

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Square (value addWords addWords_length addWords_value)

theorem cms_fold_sum_length (s : State) : (cmsFoldSum s).length=9 := by
  have hl := addWords_length (cmsFoldExtended s) (cmsFoldAddend s) (cmsFoldDetect s)
    (by rw [cms_fold_extended_length,cms_fold_addend_length])
  simpa only [cmsFoldSum,cms_fold_extended_length] using hl

theorem cms_fold_result_mask (s : State) : value (cmsFoldResult s)=value (cmsFoldSum s)%(2^521) := by
  dsimp only [cmsFoldResult]
  exact P521Square.maskLast_value (cmsFoldSum s) (cms_fold_sum_length s)

theorem cms_fold_result_value (s : State) :
    value (cmsFoldResult s)=(regsVal s cmsScalarRegs%(2^521)+regsVal s cmsScalarRegs/(2^521)+(cmsFoldDetect s).toNat)%(2^521) := by
  have e := addWords_value (cmsFoldExtended s) (cmsFoldAddend s) (cmsFoldDetect s)
    (by rw [cms_fold_extended_length,cms_fold_addend_length])
  rw [cms_fold_extended_length,cms_fold_extended_value,cms_fold_addend_value] at e
  simp only [Nat.reduceMul] at e
  have e' : value (cmsFoldSum s)+2^576*(addWords (cmsFoldExtended s) (cmsFoldAddend s) (cmsFoldDetect s)).2.toNat=
      (2^576-2^521)+(regsVal s cmsScalarRegs%(2^521)+regsVal s cmsScalarRegs/(2^521))+(cmsFoldDetect s).toNat := by
    dsimp only [cmsFoldSum]
    omega_using [e]
  rw [cms_fold_result_mask]
  have hR : (2:Nat)^521≤2^576 := by lit_decide
  have hmod : (2:Nat)^576%(2^521)=0 := by lit_decide
  generalize hf : (2:Nat)^521=F at e' hR hmod ⊢
  generalize hr : (2:Nat)^576=R at e' hR hmod
  exact cms_sum_mask_math hR hmod e'

theorem cms_fold_result_canonical (s : State) (hm : s.gpr .x15=cmsAndWords (cmsMiddleRegs.map s.gpr))
    (hn : regsVal s cmsScalarRegs<33*(2^521-1)) :
    value (cmsFoldResult s)=regsVal s cmsScalarRegs%(2^521-1) ∧ value (cmsFoldResult s)<2^521-1 := by
  have hc := cms_fold_detect_flag s hm
  have hw := cms_fold_result_value s
  have hF : 34<(2:Nat)^521 := by lit_decide
  generalize hf : (2:Nat)^521=F at hn hc hw hF ⊢
  exact cms_field_end_carry hF hn hc hw

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Square (value)

theorem cms_fold_ok (s : State) (hm : s.gpr .x13=511)
    (hand : s.gpr .x15=cmsAndWords (cmsMiddleRegs.map s.gpr))
    (hn : regsVal s cmsScalarRegs<33*(2^521-1)) :
    WP isa (.block cmsFoldCode) s fun t =>
      regsVal t cmsScalarRegs=regsVal s cmsScalarRegs%(2^521-1) ∧
      regsVal t cmsScalarRegs<2^521-1 ∧ t.gpr .x1=0 ∧
      VG.Proof.Ed25519.AArch64.Keeps cmsFoldClob s t := by
  refine WP.mono (cms_fold_words s hm) fun t ⟨words,z,k⟩ => ?_
  have hv := congrArg value words
  rw [value_map_gpr] at hv
  have hc := cms_fold_result_canonical s hand hn
  exact ⟨hv.trans hc.1,hv ▸ hc.2,z,k⟩

end VG.Proof.Mont.AArch64.P521Field
