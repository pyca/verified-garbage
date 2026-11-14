module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.DoubleSquare0
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.DoubleSquare1
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.LinearAdd
public import VerifiedGarbage.Impl.Mont.AArch64.P521Field.Kernels
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.HoistMarked
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointSchedule
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.KernelSlice
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.LinearSub
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.DoubleMul0Field
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.DoubleSquare2
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.DoubleMul1Field
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.DoubleSquare3
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.DoubleCms12
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.DoubleSquare4
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.DoubleMul2Field
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.DoubleCms41
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.DoubleCms38
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 VG.Impl.Mont.AArch64.P521Field

def DoubleSub2Code : List Instr := ((doubleFnBlocks.drop 74).flatten.drop 8).take 46
def DoubleSub2Early : List Instr := DoubleSub2Code.take 27
def DoubleSub2Tail : List Instr := ((doubleFnBlocks.drop 75).flatten.drop 3).take 19
def DoubleSub2Pick : Instr → Bool
  | .ldr .x r _ _ => linearRegs9.contains r
  | _ => false

theorem DoubleSub2_source : DoubleSub2Code=(doubleFnBlocks.flatten.drop 2376).take 46 := by
  have h := drop_flatten_prefix doubleFnBlocks 74 2368 8
    (by rw [List.length_flatten]; lit_decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 46) h.symm

theorem DoubleSub2_hoist : hoistMarked DoubleSub2Pick .x26 DoubleSub2Early=
    some (loadsR .x28 linearRegs9 360,linearDifference .x28 72) := by lit_decide

theorem DoubleSub2_run (s : State) : runBlock isa DoubleSub2Code s=
    runBlock isa (linearSubNormalized .x28 360 .x28 72 .x26 144 .x1 true) s := by
  have hs : DoubleSub2Code=DoubleSub2Early++DoubleSub2Tail := by decide
  have hn : linearSubNormalized .x28 360 .x28 72 .x26 144 .x1 true=
      (loadsR .x28 linearRegs9 360++linearDifference .x28 72)++DoubleSub2Tail := by decide
  rw [hs,hn]
  exact append_run_eq (hoistMarked_run DoubleSub2_hoist) (fun _ => rfl) s

theorem DoubleSub2_ok {s : State} {pa pb po : Addr} {size cap room : Nat}
    (ha : Ptr s .x28 pa size) (hb : Ptr s .x28 pb cap) (ho : PtrW s .x26 po room)
    (hA : 432≤size) (hB : 144≤cap) (hO : 216≤room)
    (hz : s.gpr .x1=0)
    (hm : s.gpr .x0=511)
    (hva : wordsVal s.mem pa 360 9<2^521-1) (hvb : wordsVal s.mem pb 72 9<2^521-1) :
    WP isa (.block DoubleSub2Code) s fun t =>
      wordsVal t.mem po 144 9=(wordsVal s.mem pa 360 9+(2^521-1)-wordsVal s.mem pb 72 9)%(2^521-1) ∧
      wordsVal t.mem po 144 9<2^521-1 ∧ t.gpr .x0=511 ∧
      KeepRegs linearAddClob s t ∧ Outside po 144 72 s.mem t.mem := by
  have h := linear_sub_normalized_ok (a:=360) (b:=72) (o:=144) (z:=.x1) true ha hb ho hA hB hO
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hz
    (fun _ => hm) hva hvb
  obtain ⟨t,ht,hq⟩ := VG.AArch64.Interleave.runBlock_of_WP h
  exact WP.of_runBlock ⟨t,(DoubleSub2_run s).trans ht,hq⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 VG.Impl.Mont.AArch64.P521Field

def DoubleSub1Code : List Instr := ((doubleFnBlocks.drop 65).flatten.drop 4).take 47
def DoubleSub1Early : List Instr := DoubleSub1Code.take 27
def DoubleSub1Tail : List Instr := ((doubleFnBlocks.drop 65).flatten.drop 31).take 20
def DoubleSub1Pick : Instr → Bool
  | .ldr .x r _ _ => linearRegs9.contains r
  | _ => false

theorem DoubleSub1_source : DoubleSub1Code=(doubleFnBlocks.flatten.drop 2084).take 47 := by
  have h := drop_flatten_prefix doubleFnBlocks 65 2080 4
    (by rw [List.length_flatten]; lit_decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 47) h.symm

theorem DoubleSub1_hoist : hoistMarked DoubleSub1Pick .x28 DoubleSub1Early=
    some (loadsR .x28 linearRegs9 288,linearDifference .x28 0) := by lit_decide

theorem DoubleSub1_run (s : State) : runBlock isa DoubleSub1Code s=
    runBlock isa (linearSubNormalized .x28 288 .x28 0 .x28 360 .x1 false) s := by
  have hs : DoubleSub1Code=DoubleSub1Early++DoubleSub1Tail := by decide
  have hn : linearSubNormalized .x28 288 .x28 0 .x28 360 .x1 false=
      (loadsR .x28 linearRegs9 288++linearDifference .x28 0)++DoubleSub1Tail := by decide
  rw [hs,hn]
  exact append_run_eq (hoistMarked_run DoubleSub1_hoist) (fun _ => rfl) s

theorem DoubleSub1_ok {s : State} {pa pb po : Addr} {size cap room : Nat}
    (ha : Ptr s .x28 pa size) (hb : Ptr s .x28 pb cap) (ho : PtrW s .x28 po room)
    (hA : 360≤size) (hB : 72≤cap) (hO : 432≤room)
    (hz : s.gpr .x1=0)
    (hva : wordsVal s.mem pa 288 9<2^521-1) (hvb : wordsVal s.mem pb 0 9<2^521-1) :
    WP isa (.block DoubleSub1Code) s fun t =>
      wordsVal t.mem po 360 9=(wordsVal s.mem pa 288 9+(2^521-1)-wordsVal s.mem pb 0 9)%(2^521-1) ∧
      wordsVal t.mem po 360 9<2^521-1 ∧ t.gpr .x0=511 ∧
      KeepRegs linearAddClob s t ∧ Outside po 360 72 s.mem t.mem := by
  have h := linear_sub_normalized_ok (a:=288) (b:=0) (o:=360) (z:=.x1) false ha hb ho hA hB hO
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hz
    (by intro h; cases h) hva hvb
  obtain ⟨t,ht,hq⟩ := VG.AArch64.Interleave.runBlock_of_WP h
  exact WP.of_runBlock ⟨t,(DoubleSub1_run s).trans ht,hq⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 VG.Impl.Mont.AArch64.P521Field

def DoubleSub0Code : List Instr := ((doubleFnBlocks.drop 17).flatten.drop 13).take 47
def DoubleSub0Early : List Instr := DoubleSub0Code.take 27
def DoubleSub0Tail : List Instr := ((doubleFnBlocks.drop 18).flatten.drop 8).take 20
def DoubleSub0Pick : Instr → Bool
  | .ldr .x r _ _ => linearRegs9.contains r
  | _ => false

theorem DoubleSub0_source : DoubleSub0Code=(doubleFnBlocks.flatten.drop 557).take 47 := by
  have h := drop_flatten_prefix doubleFnBlocks 17 544 13
    (by rw [List.length_flatten]; lit_decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 47) h.symm

theorem DoubleSub0_hoist : hoistMarked DoubleSub0Pick .x28 DoubleSub0Early=
    some (loadsR .x27 linearRegs9 0,linearDifference .x28 0) := by lit_decide

theorem DoubleSub0_run (s : State) : runBlock isa DoubleSub0Code s=
    runBlock isa (linearSubNormalized .x27 0 .x28 0 .x28 288 .x1 false) s := by
  have hs : DoubleSub0Code=DoubleSub0Early++DoubleSub0Tail := by decide
  have hn : linearSubNormalized .x27 0 .x28 0 .x28 288 .x1 false=
      (loadsR .x27 linearRegs9 0++linearDifference .x28 0)++DoubleSub0Tail := by decide
  rw [hs,hn]
  exact append_run_eq (hoistMarked_run DoubleSub0_hoist) (fun _ => rfl) s

theorem DoubleSub0_ok {s : State} {pa pb po : Addr} {size cap room : Nat}
    (ha : Ptr s .x27 pa size) (hb : Ptr s .x28 pb cap) (ho : PtrW s .x28 po room)
    (hA : 72≤size) (hB : 72≤cap) (hO : 360≤room)
    (hz : s.gpr .x1=0)
    (hva : wordsVal s.mem pa 0 9<2^521-1) (hvb : wordsVal s.mem pb 0 9<2^521-1) :
    WP isa (.block DoubleSub0Code) s fun t =>
      wordsVal t.mem po 288 9=(wordsVal s.mem pa 0 9+(2^521-1)-wordsVal s.mem pb 0 9)%(2^521-1) ∧
      wordsVal t.mem po 288 9<2^521-1 ∧ t.gpr .x0=511 ∧
      KeepRegs linearAddClob s t ∧ Outside po 288 72 s.mem t.mem := by
  have h := linear_sub_normalized_ok (a:=0) (b:=0) (o:=288) (z:=.x1) false ha hb ho hA hB hO
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hz
    (by intro h; cases h) hva hvb
  obtain ⟨t,ht,hq⟩ := VG.AArch64.Interleave.runBlock_of_WP h
  exact WP.of_runBlock ⟨t,(DoubleSub0_run s).trans ht,hq⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 VG.Impl.Mont.AArch64.P521Field

def DoubleAdd1Code : List Instr := ((doubleFnBlocks.drop 31).flatten.drop 16).take 51

def DoubleAdd1Pick : Instr → Bool
  | .ldr .x r _ _ => linearRegs9.contains r
  | _ => false

def DoubleAdd1Early : List Instr := DoubleAdd1Code.take 28

def DoubleAdd1Tail : List Instr := ((doubleFnBlocks.drop 32).flatten.drop 12).take 23

def DoubleAdd1Rest : List Instr := linearSetCarry++linearSum .x27 144

theorem DoubleAdd1_source : DoubleAdd1Code=(doubleFnBlocks.flatten.drop 1008).take 51 := by
  have h := drop_flatten_prefix doubleFnBlocks 31 992 16
    (by rw [List.length_flatten]; lit_decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 51) h.symm

theorem DoubleAdd1_hoist : hoistMarked DoubleAdd1Pick .x28 DoubleAdd1Early=
    some (loadsR .x27 linearRegs9 72,DoubleAdd1Rest) := by lit_decide

theorem DoubleAdd1_run (s : State) : runBlock isa DoubleAdd1Code s=
    runBlock isa (linearAddNormalized .x27 72 .x27 144 .x28 360 .x2) s := by
  have hs : DoubleAdd1Code=DoubleAdd1Early++DoubleAdd1Tail := by decide
  have hn : linearAddNormalized .x27 72 .x27 144 .x28 360 .x2=
      (loadsR .x27 linearRegs9 72++DoubleAdd1Rest)++DoubleAdd1Tail := by decide
  rw [hs,hn]
  exact append_run_eq (hoistMarked_run DoubleAdd1_hoist) (fun _ => rfl) s

theorem DoubleAdd1_ok {s : State} {pa pb po : Addr} {size cap room : Nat}
    (ha : Ptr s .x27 pa size) (hb : Ptr s .x27 pb cap) (ho : PtrW s .x28 po room)
    (hA : 144≤size) (hB : 216≤cap) (hO : 432≤room)
    (hz : s.gpr .x2=0)
    (hva : wordsVal s.mem pa 72 9<2^521-1) (hvb : wordsVal s.mem pb 144 9<2^521-1) :
    WP isa (.block DoubleAdd1Code) s fun t =>
      wordsVal t.mem po 360 9=(wordsVal s.mem pa 72 9+wordsVal s.mem pb 144 9)%(2^521-1) ∧
      wordsVal t.mem po 360 9<2^521-1 ∧ t.gpr .x0=512 ∧
      KeepRegs linearAddClob s t ∧ Outside po 360 72 s.mem t.mem := by
  have h := linear_add_normalized_ok (a:=72) (b:=144) (o:=360) (z:=.x2) ha hb ho hA hB hO
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hz hva hvb
  obtain ⟨t,ht,hq⟩ := VG.AArch64.Interleave.runBlock_of_WP h
  exact WP.of_runBlock ⟨t,(DoubleAdd1_run s).trans ht,hq⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 VG.Impl.Mont.AArch64.P521Field

def DoubleAdd0Code : List Instr := ((doubleFnBlocks.drop 15).flatten.drop 26).take 51

def DoubleAdd0Pick : Instr → Bool
  | .ldr .x r _ _ => linearRegs9.contains r
  | _ => false

def DoubleAdd0Early : List Instr := DoubleAdd0Code.take 28

def DoubleAdd0Tail : List Instr := ((doubleFnBlocks.drop 16).flatten.drop 22).take 23

def DoubleAdd0Rest : List Instr := linearSetCarry++linearSum .x28 0

theorem DoubleAdd0_source : DoubleAdd0Code=(doubleFnBlocks.flatten.drop 506).take 51 := by
  have h := drop_flatten_prefix doubleFnBlocks 15 480 26
    (by rw [List.length_flatten]; lit_decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 51) h.symm

theorem DoubleAdd0_hoist : hoistMarked DoubleAdd0Pick .x28 DoubleAdd0Early=
    some (loadsR .x27 linearRegs9 0,DoubleAdd0Rest) := by lit_decide

theorem DoubleAdd0_run (s : State) : runBlock isa DoubleAdd0Code s=
    runBlock isa (linearAddNormalized .x27 0 .x28 0 .x28 360 .x1) s := by
  have hs : DoubleAdd0Code=DoubleAdd0Early++DoubleAdd0Tail := by decide
  have hn : linearAddNormalized .x27 0 .x28 0 .x28 360 .x1=
      (loadsR .x27 linearRegs9 0++DoubleAdd0Rest)++DoubleAdd0Tail := by decide
  rw [hs,hn]
  exact append_run_eq (hoistMarked_run DoubleAdd0_hoist) (fun _ => rfl) s

theorem DoubleAdd0_ok {s : State} {pa pb po : Addr} {size cap room : Nat}
    (ha : Ptr s .x27 pa size) (hb : Ptr s .x28 pb cap) (ho : PtrW s .x28 po room)
    (hA : 72≤size) (hB : 72≤cap) (hO : 432≤room)
    (hz : s.gpr .x1=0)
    (hva : wordsVal s.mem pa 0 9<2^521-1) (hvb : wordsVal s.mem pb 0 9<2^521-1) :
    WP isa (.block DoubleAdd0Code) s fun t =>
      wordsVal t.mem po 360 9=(wordsVal s.mem pa 0 9+wordsVal s.mem pb 0 9)%(2^521-1) ∧
      wordsVal t.mem po 360 9<2^521-1 ∧ t.gpr .x0=512 ∧
      KeepRegs linearAddClob s t ∧ Outside po 360 72 s.mem t.mem := by
  have h := linear_add_normalized_ok (a:=0) (b:=0) (o:=360) (z:=.x1) ha hb ho hA hB hO
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hz hva hvb
  obtain ⟨t,ht,hq⟩ := VG.AArch64.Interleave.runBlock_of_WP h
  exact WP.of_runBlock ⟨t,(DoubleAdd0_run s).trans ht,hq⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Impl.Mont.AArch64.P521Field

def doubleArithmeticBlocks : List (List Instr) := [
  DoubleSquare0Code,
  DoubleSquare1Code,
  DoubleAdd0Code,
  DoubleSub0Code,
  DoubleMul0FieldCode,
  DoubleAdd1Code,
  DoubleSquare2Code,
  DoubleMul1FieldCode,
  DoubleSquare3Code,
  doubleCms12Code,
  DoubleSub1Code,
  DoubleSquare4Code,
  DoubleSub2Code,
  DoubleMul2FieldCode,
  doubleCms41Code,
  doubleCms38Code]

def doubleArithmeticCode : List Instr := doubleArithmeticBlocks.flatten

theorem double_arithmetic_novec : ∀i∈doubleArithmeticCode,vdstOf i=none := by
  have h : doubleArithmeticCode.all (fun i => vdstOf i==none)=true := by lit_decide
  simpa only [List.all_eq_true,beq_iff_eq] using h

end VG.Proof.Mont.AArch64.P521Field
