module

-- separate module: The fused-coefficient word and normalization replay at DoubleCms12 (doubleCms12_normalized) costs 1.08s of proof versus 0.52s of imports; DoubleBlocks composition edits reuse this checked computation.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsFold
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeArithmetic
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsScalar
public import VerifiedGarbage.Impl.Mont.AArch64.P521Field.Kernels
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.KernelSlice
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsLowLoaded
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.Hoist
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointSchedule
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeProduct

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64.P521Field

def doubleCmsScalarCode : List Instr := ((doubleFnBlocks.drop 60).flatten.drop 25).take 35

theorem doubleCmsScalar_source : doubleCmsScalarCode=(doubleFnBlocks.flatten.drop 1945).take 35 := by
  have h := drop_flatten_prefix doubleFnBlocks 60 1920 25
    (by rw [List.length_flatten]; lit_decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 35) h.symm

theorem doubleCmsScalar_eq : doubleCmsScalarCode=cmsScalarCode 216 := by decide

theorem double_cms_scalar_ok {s : State} {p : Addr} {size : Nat}
    (hp : Ptr s .x28 p size) (hb : 288≤size)
    (ha : wordsVal s.mem p 216 9<2*(2^521-1)) :
    WP isa (.block doubleCmsScalarCode) s fun t =>
      regsVal t cmsScalarRegs=12*wordsVal s.mem p 216 9 ∧ t.gpr .x1=12 ∧
      VG.Proof.Ed25519.AArch64.Keeps cmsScalarClob s t := by
  rw [doubleCmsScalar_eq]
  exact cms_scalar_ok hp hb (by decide) ha

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 VG.Impl.Mont.AArch64.P521Field
open VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64.P521Square (addWords)

def doubleCmsLowCode : List Instr := ((doubleFnBlocks.drop 61).flatten.drop 28).take 57

theorem doubleCmsLow_source : doubleCmsLowCode=(doubleFnBlocks.flatten.drop 1980).take 57 := by
  have h := drop_flatten_prefix doubleFnBlocks 61 1952 28
    (by rw [List.length_flatten]; lit_decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 57) h.symm

theorem doubleCmsLow_hoist : hoistLoads .x28 doubleCmsLowCode=some (loadsR .x28 cmsLowIn 432,cmsLowCode) := by lit_decide

theorem double_cms_low_ok {s : State} {p : Addr} {size : Nat}
    (hp : Ptr s .x28 p size) (hb : 496≤size) :
    WP isa (.block doubleCmsLowCode) s fun t =>
      cmsLowOut.map t.gpr=(addWords (cmsLowOut.map s.gpr) ((readWords s.mem p 432 8).map fun x => 9 * (~~~x)) false).1 ∧
      t.c=(addWords (cmsLowOut.map s.gpr) ((readWords s.mem p 432 8).map fun x => 9 * (~~~x)) false).2 ∧
      cmsLowIn.map t.gpr=(readWords s.mem p 432 8).map (fun x => mulHi 9 (~~~x)) ∧
      t.gpr .x1=9 ∧ Keeps cmsLowClob s t := by
  have h := cms_low_loaded_words hp hb (by decide)
  obtain ⟨t,ht,hq⟩ := VG.AArch64.Interleave.runBlock_of_WP h
  exact WP.of_runBlock ⟨t,(hoistLoads_run doubleCmsLow_hoist s).trans ht,hq⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 (storesR)
open VG.Proof.Ed25519.AArch64

def cms12Code (a b o : Nat) : List Instr := cmsCombinationCode a b++
  (cmsFoldCode++storesR .x28 cmsScalarRegs o)

theorem cms12_ok {s : State} {p : Addr} {size a b o : Nat}
    (hp : PtrW s .x28 p size) (hA : a+72≤size) (hB : b+72≤size) (hO : o+72≤size)
    (ha8 : a%8=0) (hb8 : b%8=0) (ho8 : o%8=0)
    (ha : wordsVal s.mem p a 9<2*(2^521-1)) (hb : wordsVal s.mem p b 9<2^521-1) :
    WP isa (.block (cms12Code a b o)) s fun t =>
      wordsVal t.mem p o 9=(12*wordsVal s.mem p a 9+9*((2^521-1)-wordsVal s.mem p b 9))%(2^521-1) ∧
      wordsVal t.mem p o 9<2^521-1 ∧ t.gpr .x1=0 ∧ t.gpr .x13=511 ∧
      KeepRegs cmsCombinationClob s t ∧ Outside p o 72 s.mem t.mem := by
  rw [cms12Code,WP.block_append_iff]
  refine WP.mono (cms_combination_ok hp.readable hA hB ha8 hb8 ha hb) fun u ⟨eu,bu,mid,mu,_,ku⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cms_fold_ok u mu mid bu) fun v ⟨ev,bv,zv,kv⟩ => ?_
  have kept : Keeps cmsCombinationClob s v := ku.trans (kv.mono (by decide))
  have hpv := hp.of_keepRegs (Keeps.regs kept) (by decide)
  refine WP.mono (storesR_ok cmsScalarRegs hpv (by simpa only [show cmsScalarRegs.length=9 from by decide] using hO)
    ho8 (by decide)) fun t ⟨stored,kt,ot⟩ => ?_
  simp only [show cmsScalarRegs.length=9 from by decide] at stored ot
  have comp : cmsComplementValue s.mem p b=(2^521-1)-wordsVal s.mem p b 9 := by
    have h := cms_complement_value s.mem p b (by omega_using [hb])
    omega_using [h]
  rw [eu,comp] at ev
  exact ⟨stored.trans ev,stored ▸ bv,(kt.gpr .x1 (by simp)).trans zv,
    (kt.gpr .x13 (by simp)).trans ((kv.gpr .x13 (by decide)).trans mu),
    (Keeps.regs kept).trans (kt.mono (by simp)),by rw [kept.mem] at ot; exact ot⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64.P521Field

def doubleCms12Code : List Instr := ((doubleFnBlocks.drop 60).flatten.drop 25).take 139
def doubleCms12Tail : List Instr := ((doubleFnBlocks.drop 63).flatten.drop 21).take 47

theorem doubleCms12_source : doubleCms12Code=(doubleFnBlocks.flatten.drop 1945).take 139 := by
  have h := drop_flatten_prefix doubleFnBlocks 60 1920 25
    (by rw [List.length_flatten]; lit_decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 139) h.symm

theorem doubleCms12_split : doubleCms12Code=doubleCmsScalarCode++(doubleCmsLowCode++doubleCms12Tail) := by
  apply chunks_eq 128 <;> decide

theorem doubleCms12_normalized : cms12Code 216 432 432=
    cmsScalarCode 216++(cmsLowLoaded 432++doubleCms12Tail) := by
  apply chunks_eq 128 <;> decide

theorem doubleCms12_run (s : State) : runBlock isa doubleCms12Code s=runBlock isa (cms12Code 216 432 432) s := by
  rw [doubleCms12_split,doubleCms12_normalized]
  exact append_run_eq (fun u => congrArg (fun code => runBlock isa code u) doubleCmsScalar_eq)
    (append_run_eq (hoistLoads_run doubleCmsLow_hoist) (fun _ => rfl)) s

theorem double_cms12_ok {s : State} {p : Addr} {size : Nat}
    (hp : PtrW s .x28 p size) (hA : 288≤size) (hB : 504≤size)
    (ha : wordsVal s.mem p 216 9<2*(2^521-1)) (hb : wordsVal s.mem p 432 9<2^521-1) :
    WP isa (.block doubleCms12Code) s fun t =>
      wordsVal t.mem p 432 9=(12*wordsVal s.mem p 216 9+9*((2^521-1)-wordsVal s.mem p 432 9))%(2^521-1) ∧
      wordsVal t.mem p 432 9<2^521-1 ∧ t.gpr .x1=0 ∧ t.gpr .x13=511 ∧
      KeepRegs cmsCombinationClob s t ∧ Outside p 432 72 s.mem t.mem := by
  have h := cms12_ok (a:=216) (b:=432) (o:=432) hp hA hB hB (by decide) (by decide) (by decide) ha hb
  obtain ⟨t,ht,hq⟩ := VG.AArch64.Interleave.runBlock_of_WP h
  exact WP.of_runBlock ⟨t,(doubleCms12_run s).trans ht,hq⟩

end VG.Proof.Mont.AArch64.P521Field
