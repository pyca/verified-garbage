module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeCorrect
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionMath
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Reduction
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Product
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionCorrect
import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Framework.Block

/-! Canonical reduction of the seventeen-word streamed product. -/

-- separate module: compose scratch loads, fold and correction using existing Mersenne arithmetic
@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps)
open VG.Proof.Mont.AArch64.P521Square
  (value inputValue folded fieldPrime addWords_length corrected_length corrected_value prime_value)

def streamedValue (s : State) (pt : Addr) : Nat :=
  wordsVal s.mem pt 0 8+2^512*regsVal s row8In

theorem range9_eq {f : Nat → BitVec 64} {xs : List (BitVec 64)} (hl : xs.length=9)
    (h : ∀i,i<9 → f i=xs.getD i 0) : (List.range 9).map f=xs := by
  apply List.ext_getElem
  · simpa using hl.symm
  · intro i hi hi'
    have hi9 : i<9 := by simpa using hi
    simpa only [List.getElem_map,List.getElem_range,List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi',Option.getD_some] using h i hi9

theorem fold_output_value (s : State) :
    value ((List.range 9).map (foldOutAt s))=regsVal s bRegs := rfl

theorem normalized_reduce_ok {s : State} {pt : Addr}
    (hp : Ptr s .x27 pt 64) (hz : s.gpr .x2=0)
    (hu : streamedValue s pt<fieldPrime*fieldPrime) :
    WP isa (.block (nativeFoldLoads++(nativeFoldArith++nativeCorrect))) s fun t =>
      regsVal t bRegs<fieldPrime ∧ regsVal t bRegs=streamedValue s pt%fieldPrime ∧
      Keeps foldClob s t := by
  rw [nativeFoldLoads,WP.block_append_iff]
  refine WP.mono (loadsR_ok foldLowRegs hp (a:=0) (by decide) (by decide) (by decide) (by decide))
    fun u ⟨loaded,kl,_⟩ => ?_
  have hinput : inputValue (foldWordAt u)=streamedValue s pt := by
    have hm : (List.range 17).map (foldWordAt u)=foldInputs.map u.gpr := rfl
    have high : regsVal u row8In=regsVal s row8In := regsVal_congr fun r hr =>
      kl.gpr r ((show ∀r∈row8In,r∉foldLowRegs from by decide) r hr)
    change regsVal u foldLowRegs=wordsVal s.mem pt 0 8 at loaded
    rw [inputValue,hm,value_map_gpr,foldInputs,regsVal_append,loaded,high]
    simp only [streamedValue,show foldLowRegs.length=8 from rfl,Nat.reduceMul]
  have zu : u.gpr .x2=0 := (kl.gpr _ (by decide)).trans hz
  rw [WP.block_append_iff]
  refine WP.mono (fold_arith_ok u zu) fun v ⟨fold,carry,kf⟩ => ?_
  have hlen : (folded (foldWordAt u)).1.length=9 := addWords_length _ _ _ rfl
  have efold := range9_eq hlen fold
  have zv : v.gpr .x2=0 := (kf.gpr _ (by decide)).trans zu
  refine WP.mono (native_correct_ok v zv) fun t ⟨correct,kc⟩ => ?_
  have ecorrect := range9_eq (corrected_length ((List.range 9).map (foldOutAt v)) v.c rfl) correct
  rw [efold,carry] at ecorrect
  have hv := congrArg value ecorrect
  rw [fold_output_value,corrected_value (foldWordAt u) (by rw [hinput]; exact hu),hinput] at hv
  have hpos : 0<fieldPrime := by dsimp only [fieldPrime]; rw [prime_value]; decide
  exact ⟨by rw [hv]; exact Nat.mod_lt _ hpos,hv,
    (kl.mono (by decide)).trans (kf.trans kc)⟩

theorem native_reduce_ok {s : State} {pt : Addr}
    (hp : Ptr s .x27 pt 64) (hz : s.gpr .x2=0)
    (hu : streamedValue s pt<fieldPrime*fieldPrime) :
    WP isa (.block (nativeFold++nativeCorrect)) s fun t =>
      regsVal t bRegs<fieldPrime ∧ regsVal t bRegs=streamedValue s pt%fieldPrime ∧
      Keeps foldClob s t := by
  rw [WP.block_append_iff]
  apply WP.hoistLoads nativeFold_hoist
  rw [WP.block_append_iff]
  have h := normalized_reduce_ok hp hz hu
  rw [WP.block_append_iff] at h
  exact WP.mono h fun _ hu => WP.block_append_iff.mp hu

end VG.Proof.Mont.AArch64.P521Field
