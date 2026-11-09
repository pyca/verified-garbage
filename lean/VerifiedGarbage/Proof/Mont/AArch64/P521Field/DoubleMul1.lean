module

-- separate module: The inline multiply source/carry replay at DoubleMul1 (DoubleMul1_normalized) costs 1.21s of proof versus 0.52s of imports; DoubleMul1Field composition edits reuse this checked computation.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointMulProduct
public import VerifiedGarbage.Impl.Mont.AArch64.P521Field.Kernels
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.Hoist
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeProduct
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.KernelSlice
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit

/-! Checked measured inline multiplication product at DoubleMul1. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64.P521Field

def DoubleMul1Code : List Instr := ((doubleFnBlocks.drop 40).flatten.drop 26).take 355
def DoubleMul1Early : List Instr := ((doubleFnBlocks.drop 40).flatten.drop 26).take 39
def DoubleMul1Rest : List Instr := ((doubleFnBlocks.drop 42).flatten.drop 1).take 316
def DoubleMul1Loads : List Instr := [
  .ldr .x .x3 .x27 0,
  .ldr .x .x4 .x27 8,
  .ldr .x .x5 .x28 72,
  .ldr .x .x6 .x28 80,
  .ldr .x .x7 .x28 88,
  .ldr .x .x8 .x28 96,
  .ldr .x .x9 .x28 104,
  .ldr .x .x10 .x28 112,
  .ldr .x .x11 .x28 120,
  .ldr .x .x12 .x28 128,
  .ldr .x .x13 .x28 136]

theorem DoubleMul1_source : DoubleMul1Code=(doubleFnBlocks.flatten.drop 1306).take 355 := by
  have h := drop_flatten_prefix doubleFnBlocks 40 1280 26
    (by rw [List.length_flatten]; decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 355) h.symm

theorem DoubleMul1_hoist : hoistLoads .x27 DoubleMul1Early=some (DoubleMul1Loads,pointMulRow0Arithmetic) := by lit_decide

theorem DoubleMul1_split : DoubleMul1Code=DoubleMul1Early++DoubleMul1Rest := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128 <;> decide

theorem DoubleMul1_normalized : pointMulProductCode .x27 0 .x28 72 .x28 216=
    (DoubleMul1Loads++pointMulRow0Arithmetic)++DoubleMul1Rest := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128 <;> decide

theorem DoubleMul1_ok {s : State} {pa pb po : Addr} {size cap room : Nat}
    (ha : Ptr s .x27 pa size) (hb : Ptr s .x28 pb cap) (ht : PtrW s .x28 po room)
    (hA : 72≤size) (hB : 144≤cap) (hO : 280≤room)
    (stable : StableInput s (off pa 0) (off po 216))
    (ha' : wordsVal s.mem (off pa 0) 0 9<2^521)
    (hb' : wordsVal s.mem (off pb 72) 0 9<2^521) :
    WP isa (.block DoubleMul1Code) s
      (PointMulProductInv s (off pa 0) (off po 216) (wordsVal s.mem (off pb 72) 0 9)) := by
  have h := point_mul_product_ok (a:=0) (b:=72) (o:=216) ha hb ht hA hB hO
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) stable ha' hb'
  rw [DoubleMul1_normalized,WP.block_append_iff] at h
  rw [DoubleMul1_split,WP.block_append_iff]
  exact WP.hoistLoads DoubleMul1_hoist h

end VG.Proof.Mont.AArch64.P521Field
