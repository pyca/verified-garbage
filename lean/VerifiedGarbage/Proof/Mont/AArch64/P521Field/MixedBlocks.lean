module

-- separate module: The mixed-add literal schedule partition and instruction replay (mixed_arithmetic_source) costs 6.22s of proof versus 0.33s of imports; MixedBody composition edits reuse this checked computation.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MixedSquare5
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MixedMul3Field
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MixedMul4Field
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MixedMul5Field
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.LinearSub
public import VerifiedGarbage.Impl.Mont.AArch64.P521Field.Kernels
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.HoistMarked
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointSchedule
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.KernelSlice
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MixedSquare6
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MixedSquare7
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MixedMul6Field
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MixedMul7Field
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MixedMul8Field
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MixedMul9Field
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MixedMul10Field
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 VG.Impl.Mont.AArch64.P521Field

def MixedSub6Code : List Instr := ((mixedFnBlocks.drop 132).flatten.drop 27).take 46
def MixedSub6Early : List Instr := MixedSub6Code.take 27
def MixedSub6Tail : List Instr := ((mixedFnBlocks.drop 133).flatten.drop 22).take 19
def MixedSub6Pick : Instr → Bool
  | .ldr .x r _ _ => linearRegs9.contains r
  | _ => false

theorem MixedSub6_source : MixedSub6Code=(mixedFnBlocks.flatten.drop 4251).take 46 := by
  have h := drop_flatten_prefix mixedFnBlocks 132 4224 27
    (by rw [List.length_flatten]; lit_decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 46) h.symm

theorem MixedSub6_hoist : hoistMarked MixedSub6Pick .x30 MixedSub6Early=
    some (loadsR .x30 linearRegs9 288,linearDifference .x30 216) := by lit_decide

theorem MixedSub6_run (s : State) : runBlock isa MixedSub6Code s=
    runBlock isa (linearSubNormalized .x30 288 .x30 216 .x30 288 .x2 true) s := by
  have hs : MixedSub6Code=MixedSub6Early++MixedSub6Tail := by decide
  have hn : linearSubNormalized .x30 288 .x30 216 .x30 288 .x2 true=
      (loadsR .x30 linearRegs9 288++linearDifference .x30 216)++MixedSub6Tail := by decide
  rw [hs,hn]
  exact append_run_eq (hoistMarked_run MixedSub6_hoist) (fun _ => rfl) s

theorem MixedSub6_ok {s : State} {pa pb po : Addr} {size cap room : Nat}
    (ha : Ptr s .x30 pa size) (hb : Ptr s .x30 pb cap) (ho : PtrW s .x30 po room)
    (hA : 360≤size) (hB : 288≤cap) (hO : 360≤room)
    (hz : s.gpr .x2=0)
    (hm : s.gpr .x0=511)
    (hva : wordsVal s.mem pa 288 9<2^521-1) (hvb : wordsVal s.mem pb 216 9<2^521-1) :
    WP isa (.block MixedSub6Code) s fun t =>
      wordsVal t.mem po 288 9=(wordsVal s.mem pa 288 9+(2^521-1)-wordsVal s.mem pb 216 9)%(2^521-1) ∧
      wordsVal t.mem po 288 9<2^521-1 ∧ t.gpr .x0=511 ∧
      KeepRegs linearAddClob s t ∧ Outside po 288 72 s.mem t.mem := by
  have h := linear_sub_normalized_ok (a:=288) (b:=216) (o:=288) (z:=.x2) true ha hb ho hA hB hO
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hz
    (fun _ => hm) hva hvb
  obtain ⟨t,ht,hq⟩ := VG.AArch64.Interleave.runBlock_of_WP h
  exact WP.of_runBlock ⟨t,(MixedSub6_run s).trans ht,hq⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 VG.Impl.Mont.AArch64.P521Field

def MixedSub4Code : List Instr := ((mixedFnBlocks.drop 104).flatten.drop 27).take 46
def MixedSub4Early : List Instr := MixedSub4Code.take 27
def MixedSub4Tail : List Instr := ((mixedFnBlocks.drop 105).flatten.drop 22).take 19
def MixedSub4Pick : Instr → Bool
  | .ldr .x r _ _ => linearRegs9.contains r
  | _ => false

theorem MixedSub4_source : MixedSub4Code=(mixedFnBlocks.flatten.drop 3355).take 46 := by
  have h := drop_flatten_prefix mixedFnBlocks 104 3328 27
    (by rw [List.length_flatten]; lit_decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 46) h.symm

theorem MixedSub4_hoist : hoistMarked MixedSub4Pick .x30 MixedSub4Early=
    some (loadsR .x30 linearRegs9 0,linearDifference .x30 144) := by lit_decide

theorem MixedSub4_run (s : State) : runBlock isa MixedSub4Code s=
    runBlock isa (linearSubNormalized .x30 0 .x30 144 .x30 0 .x2 true) s := by
  have hs : MixedSub4Code=MixedSub4Early++MixedSub4Tail := by decide
  have hn : linearSubNormalized .x30 0 .x30 144 .x30 0 .x2 true=
      (loadsR .x30 linearRegs9 0++linearDifference .x30 144)++MixedSub4Tail := by decide
  rw [hs,hn]
  exact append_run_eq (hoistMarked_run MixedSub4_hoist) (fun _ => rfl) s

theorem MixedSub4_ok {s : State} {pa pb po : Addr} {size cap room : Nat}
    (ha : Ptr s .x30 pa size) (hb : Ptr s .x30 pb cap) (ho : PtrW s .x30 po room)
    (hA : 72≤size) (hB : 216≤cap) (hO : 72≤room)
    (hz : s.gpr .x2=0)
    (hm : s.gpr .x0=511)
    (hva : wordsVal s.mem pa 0 9<2^521-1) (hvb : wordsVal s.mem pb 144 9<2^521-1) :
    WP isa (.block MixedSub4Code) s fun t =>
      wordsVal t.mem po 0 9=(wordsVal s.mem pa 0 9+(2^521-1)-wordsVal s.mem pb 144 9)%(2^521-1) ∧
      wordsVal t.mem po 0 9<2^521-1 ∧ t.gpr .x0=511 ∧
      KeepRegs linearAddClob s t ∧ Outside po 0 72 s.mem t.mem := by
  have h := linear_sub_normalized_ok (a:=0) (b:=144) (o:=0) (z:=.x2) true ha hb ho hA hB hO
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hz
    (fun _ => hm) hva hvb
  obtain ⟨t,ht,hq⟩ := VG.AArch64.Interleave.runBlock_of_WP h
  exact WP.of_runBlock ⟨t,(MixedSub4_run s).trans ht,hq⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 VG.Impl.Mont.AArch64.P521Field

def MixedSub3Code : List Instr := ((mixedFnBlocks.drop 90).flatten.drop 27).take 46
def MixedSub3Early : List Instr := MixedSub3Code.take 27
def MixedSub3Tail : List Instr := ((mixedFnBlocks.drop 91).flatten.drop 22).take 19
def MixedSub3Pick : Instr → Bool
  | .ldr .x r _ _ => linearRegs9.contains r
  | _ => false

theorem MixedSub3_source : MixedSub3Code=(mixedFnBlocks.flatten.drop 2907).take 46 := by
  have h := drop_flatten_prefix mixedFnBlocks 90 2880 27
    (by rw [List.length_flatten]; lit_decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 46) h.symm

theorem MixedSub3_hoist : hoistMarked MixedSub3Pick .x30 MixedSub3Early=
    some (loadsR .x30 linearRegs9 144,linearDifference .x30 288) := by lit_decide

theorem MixedSub3_run (s : State) : runBlock isa MixedSub3Code s=
    runBlock isa (linearSubNormalized .x30 144 .x30 288 .x30 216 .x2 true) s := by
  have hs : MixedSub3Code=MixedSub3Early++MixedSub3Tail := by decide
  have hn : linearSubNormalized .x30 144 .x30 288 .x30 216 .x2 true=
      (loadsR .x30 linearRegs9 144++linearDifference .x30 288)++MixedSub3Tail := by decide
  rw [hs,hn]
  exact append_run_eq (hoistMarked_run MixedSub3_hoist) (fun _ => rfl) s

theorem MixedSub3_ok {s : State} {pa pb po : Addr} {size cap room : Nat}
    (ha : Ptr s .x30 pa size) (hb : Ptr s .x30 pb cap) (ho : PtrW s .x30 po room)
    (hA : 216≤size) (hB : 360≤cap) (hO : 288≤room)
    (hz : s.gpr .x2=0)
    (hm : s.gpr .x0=511)
    (hva : wordsVal s.mem pa 144 9<2^521-1) (hvb : wordsVal s.mem pb 288 9<2^521-1) :
    WP isa (.block MixedSub3Code) s fun t =>
      wordsVal t.mem po 216 9=(wordsVal s.mem pa 144 9+(2^521-1)-wordsVal s.mem pb 288 9)%(2^521-1) ∧
      wordsVal t.mem po 216 9<2^521-1 ∧ t.gpr .x0=511 ∧
      KeepRegs linearAddClob s t ∧ Outside po 216 72 s.mem t.mem := by
  have h := linear_sub_normalized_ok (a:=144) (b:=288) (o:=216) (z:=.x2) true ha hb ho hA hB hO
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hz
    (fun _ => hm) hva hvb
  obtain ⟨t,ht,hq⟩ := VG.AArch64.Interleave.runBlock_of_WP h
  exact WP.of_runBlock ⟨t,(MixedSub3_run s).trans ht,hq⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 VG.Impl.Mont.AArch64.P521Field

def MixedSub2Code : List Instr := ((mixedFnBlocks.drop 89).flatten.drop 13).take 46
def MixedSub2Early : List Instr := MixedSub2Code.take 27
def MixedSub2Tail : List Instr := ((mixedFnBlocks.drop 90).flatten.drop 8).take 19
def MixedSub2Pick : Instr → Bool
  | .ldr .x r _ _ => linearRegs9.contains r
  | _ => false

theorem MixedSub2_source : MixedSub2Code=(mixedFnBlocks.flatten.drop 2861).take 46 := by
  have h := drop_flatten_prefix mixedFnBlocks 89 2848 13
    (by rw [List.length_flatten]; lit_decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 46) h.symm

theorem MixedSub2_hoist : hoistMarked MixedSub2Pick .x30 MixedSub2Early=
    some (loadsR .x30 linearRegs9 0,linearDifference .x30 288) := by lit_decide

theorem MixedSub2_run (s : State) : runBlock isa MixedSub2Code s=
    runBlock isa (linearSubNormalized .x30 0 .x30 288 .x30 0 .x2 true) s := by
  have hs : MixedSub2Code=MixedSub2Early++MixedSub2Tail := by decide
  have hn : linearSubNormalized .x30 0 .x30 288 .x30 0 .x2 true=
      (loadsR .x30 linearRegs9 0++linearDifference .x30 288)++MixedSub2Tail := by decide
  rw [hs,hn]
  exact append_run_eq (hoistMarked_run MixedSub2_hoist) (fun _ => rfl) s

theorem MixedSub2_ok {s : State} {pa pb po : Addr} {size cap room : Nat}
    (ha : Ptr s .x30 pa size) (hb : Ptr s .x30 pb cap) (ho : PtrW s .x30 po room)
    (hA : 72≤size) (hB : 360≤cap) (hO : 72≤room)
    (hz : s.gpr .x2=0)
    (hm : s.gpr .x0=511)
    (hva : wordsVal s.mem pa 0 9<2^521-1) (hvb : wordsVal s.mem pb 288 9<2^521-1) :
    WP isa (.block MixedSub2Code) s fun t =>
      wordsVal t.mem po 0 9=(wordsVal s.mem pa 0 9+(2^521-1)-wordsVal s.mem pb 288 9)%(2^521-1) ∧
      wordsVal t.mem po 0 9<2^521-1 ∧ t.gpr .x0=511 ∧
      KeepRegs linearAddClob s t ∧ Outside po 0 72 s.mem t.mem := by
  have h := linear_sub_normalized_ok (a:=0) (b:=288) (o:=0) (z:=.x2) true ha hb ho hA hB hO
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hz
    (fun _ => hm) hva hvb
  obtain ⟨t,ht,hq⟩ := VG.AArch64.Interleave.runBlock_of_WP h
  exact WP.of_runBlock ⟨t,(MixedSub2_run s).trans ht,hq⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 VG.Impl.Mont.AArch64.P521Field

def MixedSub1Code : List Instr := ((mixedFnBlocks.drop 47).flatten.drop 13).take 46
def MixedSub1Early : List Instr := MixedSub1Code.take 27
def MixedSub1Tail : List Instr := ((mixedFnBlocks.drop 48).flatten.drop 8).take 19
def MixedSub1Pick : Instr → Bool
  | .ldr .x r _ _ => linearRegs9.contains r
  | _ => false

theorem MixedSub1_source : MixedSub1Code=(mixedFnBlocks.flatten.drop 1517).take 46 := by
  have h := drop_flatten_prefix mixedFnBlocks 47 1504 13
    (by rw [List.length_flatten]; lit_decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 46) h.symm

theorem MixedSub1_hoist : hoistMarked MixedSub1Pick .x30 MixedSub1Early=
    some (loadsR .x30 linearRegs9 72,linearDifference .x27 72) := by lit_decide

theorem MixedSub1_run (s : State) : runBlock isa MixedSub1Code s=
    runBlock isa (linearSubNormalized .x30 72 .x27 72 .x30 72 .x2 true) s := by
  have hs : MixedSub1Code=MixedSub1Early++MixedSub1Tail := by decide
  have hn : linearSubNormalized .x30 72 .x27 72 .x30 72 .x2 true=
      (loadsR .x30 linearRegs9 72++linearDifference .x27 72)++MixedSub1Tail := by decide
  rw [hs,hn]
  exact append_run_eq (hoistMarked_run MixedSub1_hoist) (fun _ => rfl) s

theorem MixedSub1_ok {s : State} {pa pb po : Addr} {size cap room : Nat}
    (ha : Ptr s .x30 pa size) (hb : Ptr s .x27 pb cap) (ho : PtrW s .x30 po room)
    (hA : 144≤size) (hB : 144≤cap) (hO : 144≤room)
    (hz : s.gpr .x2=0)
    (hm : s.gpr .x0=511)
    (hva : wordsVal s.mem pa 72 9<2^521-1) (hvb : wordsVal s.mem pb 72 9<2^521-1) :
    WP isa (.block MixedSub1Code) s fun t =>
      wordsVal t.mem po 72 9=(wordsVal s.mem pa 72 9+(2^521-1)-wordsVal s.mem pb 72 9)%(2^521-1) ∧
      wordsVal t.mem po 72 9<2^521-1 ∧ t.gpr .x0=511 ∧
      KeepRegs linearAddClob s t ∧ Outside po 72 72 s.mem t.mem := by
  have h := linear_sub_normalized_ok (a:=72) (b:=72) (o:=72) (z:=.x2) true ha hb ho hA hB hO
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hz
    (fun _ => hm) hva hvb
  obtain ⟨t,ht,hq⟩ := VG.AArch64.Interleave.runBlock_of_WP h
  exact WP.of_runBlock ⟨t,(MixedSub1_run s).trans ht,hq⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 VG.Impl.Mont.AArch64.P521Field

def MixedSub0Code : List Instr := ((mixedFnBlocks.drop 45).flatten.drop 31).take 46
def MixedSub0Early : List Instr := MixedSub0Code.take 27
def MixedSub0Tail : List Instr := ((mixedFnBlocks.drop 46).flatten.drop 26).take 19
def MixedSub0Pick : Instr → Bool
  | .ldr .x r _ _ => linearRegs9.contains r
  | _ => false

theorem MixedSub0_source : MixedSub0Code=(mixedFnBlocks.flatten.drop 1471).take 46 := by
  have h := drop_flatten_prefix mixedFnBlocks 45 1440 31
    (by rw [List.length_flatten]; lit_decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 46) h.symm

theorem MixedSub0_hoist : hoistMarked MixedSub0Pick .x30 MixedSub0Early=
    some (loadsR .x30 linearRegs9 144,linearDifference .x27 0) := by lit_decide

theorem MixedSub0_run (s : State) : runBlock isa MixedSub0Code s=
    runBlock isa (linearSubNormalized .x30 144 .x27 0 .x30 360 .x2 true) s := by
  have hs : MixedSub0Code=MixedSub0Early++MixedSub0Tail := by decide
  have hn : linearSubNormalized .x30 144 .x27 0 .x30 360 .x2 true=
      (loadsR .x30 linearRegs9 144++linearDifference .x27 0)++MixedSub0Tail := by decide
  rw [hs,hn]
  exact append_run_eq (hoistMarked_run MixedSub0_hoist) (fun _ => rfl) s

theorem MixedSub0_ok {s : State} {pa pb po : Addr} {size cap room : Nat}
    (ha : Ptr s .x30 pa size) (hb : Ptr s .x27 pb cap) (ho : PtrW s .x30 po room)
    (hA : 216≤size) (hB : 72≤cap) (hO : 432≤room)
    (hz : s.gpr .x2=0)
    (hm : s.gpr .x0=511)
    (hva : wordsVal s.mem pa 144 9<2^521-1) (hvb : wordsVal s.mem pb 0 9<2^521-1) :
    WP isa (.block MixedSub0Code) s fun t =>
      wordsVal t.mem po 360 9=(wordsVal s.mem pa 144 9+(2^521-1)-wordsVal s.mem pb 0 9)%(2^521-1) ∧
      wordsVal t.mem po 360 9<2^521-1 ∧ t.gpr .x0=511 ∧
      KeepRegs linearAddClob s t ∧ Outside po 360 72 s.mem t.mem := by
  have h := linear_sub_normalized_ok (a:=144) (b:=0) (o:=360) (z:=.x2) true ha hb ho hA hB hO
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hz
    (fun _ => hm) hva hvb
  obtain ⟨t,ht,hq⟩ := VG.AArch64.Interleave.runBlock_of_WP h
  exact WP.of_runBlock ⟨t,(MixedSub0_run s).trans ht,hq⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 VG.Impl.Mont.AArch64.P521Field

def MixedSub5Code : List Instr := ((mixedFnBlocks.drop 106).flatten.drop 9).take 46
def MixedSub5Early : List Instr := MixedSub5Code.take 27
def MixedSub5Tail : List Instr := ((mixedFnBlocks.drop 107).flatten.drop 4).take 19
def MixedSub5Pick : Instr → Bool
  | .ldr .x r _ _ => linearRegs9.contains r
  | _ => false

theorem MixedSub5_source : MixedSub5Code=(mixedFnBlocks.flatten.drop 3401).take 46 := by
  have h := drop_flatten_prefix mixedFnBlocks 106 3392 9
    (by rw [List.length_flatten]; lit_decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 46) h.symm

theorem MixedSub5_hoist : hoistMarked MixedSub5Pick .x30 MixedSub5Early=
    some (loadsR .x30 linearRegs9 288,linearDifference .x30 0) := by lit_decide

theorem MixedSub5_run (s : State) : runBlock isa MixedSub5Code s=
    runBlock isa (linearSubNormalized .x30 288 .x30 0 .x30 288 .x2 true) s := by
  have hs : MixedSub5Code=MixedSub5Early++MixedSub5Tail := by decide
  have hn : linearSubNormalized .x30 288 .x30 0 .x30 288 .x2 true=
      (loadsR .x30 linearRegs9 288++linearDifference .x30 0)++MixedSub5Tail := by decide
  rw [hs,hn]
  exact append_run_eq (hoistMarked_run MixedSub5_hoist) (fun _ => rfl) s

theorem MixedSub5_ok {s : State} {pa pb po : Addr} {size cap room : Nat}
    (ha : Ptr s .x30 pa size) (hb : Ptr s .x30 pb cap) (ho : PtrW s .x30 po room)
    (hA : 360≤size) (hB : 72≤cap) (hO : 360≤room)
    (hz : s.gpr .x2=0)
    (hm : s.gpr .x0=511)
    (hva : wordsVal s.mem pa 288 9<2^521-1) (hvb : wordsVal s.mem pb 0 9<2^521-1) :
    WP isa (.block MixedSub5Code) s fun t =>
      wordsVal t.mem po 288 9=(wordsVal s.mem pa 288 9+(2^521-1)-wordsVal s.mem pb 0 9)%(2^521-1) ∧
      wordsVal t.mem po 288 9<2^521-1 ∧ t.gpr .x0=511 ∧
      KeepRegs linearAddClob s t ∧ Outside po 288 72 s.mem t.mem := by
  have h := linear_sub_normalized_ok (a:=288) (b:=0) (o:=288) (z:=.x2) true ha hb ho hA hB hO
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hz
    (fun _ => hm) hva hvb
  obtain ⟨t,ht,hq⟩ := VG.AArch64.Interleave.runBlock_of_WP h
  exact WP.of_runBlock ⟨t,(MixedSub5_run s).trans ht,hq⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Impl.Mont.AArch64.P521Field

def mixedArithmeticBlocks : List (List Instr) := [
  MixedSquare5Code,
  MixedMul3FieldCode,
  MixedMul4FieldCode,
  MixedMul5FieldCode,
  MixedSub0Code,
  MixedSub1Code,
  MixedSquare6Code,
  MixedSquare7Code,
  MixedMul6FieldCode,
  MixedMul7FieldCode,
  MixedSub2Code,
  MixedSub3Code,
  MixedMul8FieldCode,
  MixedSub4Code,
  MixedSub5Code,
  MixedMul9FieldCode,
  MixedMul10FieldCode,
  MixedSub6Code]

def mixedArithmeticCode : List Instr := mixedArithmeticBlocks.flatten

theorem mixed_arithmetic_source : mixedArithmeticCode=(mixedFnBlocks.flatten.drop 16).take 4281 := by lit_decide

theorem mixed_arithmetic_novec : ∀i∈mixedArithmeticCode,vdstOf i=none := by
  have h : mixedArithmeticCode.all (fun i => vdstOf i==none)=true := by lit_decide
  simpa only [List.all_eq_true,beq_iff_eq] using h

end VG.Proof.Mont.AArch64.P521Field
