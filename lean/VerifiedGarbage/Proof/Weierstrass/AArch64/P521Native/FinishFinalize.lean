module

-- separate module: the representation round trip and inverse write frame are checked independently of API input validation

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishCopy
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishInverse
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishProducts
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishFrames
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.RepresentationMath
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontSaves
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-! Standalone final projective-coordinate inversion and products. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass
open VG.Proof.Mont.AArch64.P521Field (OrdinaryInv pointRun toMontValue)
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Impl.Weierstrass.AArch64.P521Native (config)

def finalizeCore : Prog isa := .seq (.block finishCopyPoint) (.seq finishInversePhase finishProductsMachine)
def finalizeWrites : List (Nat × Nat) :=
  [(1072,72),(1144,72),(1216,72)]++normalizeInverseWrites++fieldProgramWrites id finishProductsOps

theorem finalize_core_ok (hc : VG.Proof.Ecdsa.AArch64.BaseCfgOk config)
    {base : Addr} {s : State} (hs : Scr s base 8192)
    (hM : ModOkA config.MP' 8192 config.C.p s.mem base)
    (bounds : ∀d∈[1288,1360,1432,352],wordsVal s.mem base d 9<fieldPrime) :
    WP isa finalizeCore s fun t =>
      Scr t base 8192 ∧ wordsVal t.mem base 2584 9<fieldPrime ∧
      Fin.ofNat fieldPrime (wordsVal t.mem base 2584 9)=
        Fin.ofNat fieldPrime (wordsVal s.mem base 1288 9)*
        Fin.ofNat fieldPrime (wordsVal s.mem base 1432 9)^(fieldPrime-2)*
        Fin.ofNat fieldPrime (wordsVal s.mem base 352 9) ∧
      wordsVal t.mem base 1216 9=toMontValue (wordsVal s.mem base 1432 9) ∧
      Unch base finalizeWrites s.mem t.mem ∧
      t.gpr .x0=base ∧ t.rd=s.rd ∧ t.wr=s.wr ∧ t.sp=s.sp ∧
      t.gpr .x20=s.gpr .x20 ∧ t.gpr .x26=s.gpr .x26 ∧ t.gpr .x30=s.gpr .x30 ∧
      t.gpr .x27=s.gpr .x27 ∧ t.gpr .x28=s.gpr .x28 ∧ t.v .v31=s.v .v31 := by
  rw [finalizeCore,WP.seq_iff]
  refine WP.mono (VG.Proof.Weierstrass.AArch64.Mont.WP.block_novec (by decide)
    (finish_copy_point_ok hs)) fun u ⟨⟨xu,yu,zu,ku,uc⟩,vu⟩ => ?_
  have hu := hs.of_keepRegs ku (by decide)
  have Mu : ModOkA config.MP' 8192 config.C.p u.mem base := {hM with val:=by rw [uc.wordsVal (by decide) (by decide)]; exact hM.val}
  have bu : wordsVal u.mem base 1216 9<fieldPrime := by rw [zu]; exact bounds 1432 (by simp)
  rw [WP.seq_iff]
  refine WP.mono (finish_inverse_phase_ok hc hu Mu bu)
    fun v ⟨invBound,invValue,uv,zero,rd,wr,sp,g20,g26,g30,v31,converted,gExtra⟩ => ?_
  have hv : Scr v base 8192 := ⟨zero,by rw [wr]; exact hu.wr,hu.nowrap,hu.enc⟩
  have xSame : wordsVal v.mem base 1072 9=wordsVal s.mem base 1288 9 := by
    rw [uv.wordsVal (by decide) (by decide),xu]
  have oneSame : wordsVal v.mem base 352 9=wordsVal s.mem base 352 9 := by
    rw [uv.wordsVal (by decide) (by decide),uc.wordsVal (by decide) (by decide)]
  let E : Nat → Fin fieldPrime := fun d => Fin.ofNat fieldPrime (wordsVal v.mem base d 9)
  have live : OrdinaryInv base fieldPrime id [1072,2152,352] E (fun _ => 1) v := by
    constructor
    · intro d hd
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
      rcases hd with rfl|rfl|rfl
      · simpa only [id_eq,Nat.one_mul,xSame] using bounds 1288 (by simp)
      · simpa only [id_eq,Nat.one_mul] using invBound
      · simpa only [id_eq,Nat.one_mul,oneSame] using bounds 352 (by simp)
    · intro d _; rfl
  refine WP.mono (finish_products_machine_ok hv live) fun t ⟨it,ht,kt,ft⟩ => ?_
  have productsU := field_program_frame_unch ft
  have allU : Unch base finalizeWrites s.mem t.mem := uc.trans (uv.trans productsU)
  have outBound := it.bound 2584 (by decide)
  have outValue := it.value 2584 (by decide)
  rw [finish_products_value] at outValue
  change Fin.ofNat fieldPrime (wordsVal t.mem base 2584 9)=
    Fin.ofNat fieldPrime (wordsVal v.mem base 1072 9)*
    Fin.ofNat fieldPrime (wordsVal v.mem base 2152 9)*
    Fin.ofNat fieldPrime (wordsVal v.mem base 352 9) at outValue
  rw [xSame,invValue,zu,oneSame] at outValue
  refine ⟨ht,by simpa only [id_eq,Nat.one_mul] using outBound,outValue,?_,allU,?_,
    kt.rd.trans (rd.trans ku.rd),kt.wr.trans (wr.trans ku.wr),kt.sp.trans (sp.trans ku.sp),?_,?_,?_,?_,?_,?_⟩
  · rw [productsU.wordsVal (by decide) (by decide),converted,zu]
  · exact ht.x0
  · exact (kt.gpr .x20 (by decide)).trans (g20.trans (ku.gpr .x20 (by decide)))
  · exact (kt.gpr .x26 (by decide)).trans (g26.trans (ku.gpr .x26 (by decide)))
  · exact (kt.gpr .x30 (by decide)).trans (g30.trans (ku.gpr .x30 (by decide)))
  · exact (kt.gpr .x27 (by decide)).trans ((gExtra .x27 (by simp)).trans (ku.gpr .x27 (by decide)))
  · exact (kt.gpr .x28 (by decide)).trans ((gExtra .x28 (by simp)).trans (ku.gpr .x28 (by decide)))
  · exact kt.v31.trans (v31.trans (congrFun vu .v31))

end VG.Proof.Weierstrass.AArch64.P521Native
