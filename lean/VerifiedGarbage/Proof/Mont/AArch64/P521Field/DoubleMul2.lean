module

-- separate module: The inline multiply source/carry replay at DoubleMul2 (DoubleMul2_normalized) costs 1.25s of proof versus 0.54s of imports; DoubleMul2Field composition edits reuse this checked computation.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointMulProduct
public import VerifiedGarbage.Impl.Mont.AArch64.P521Field.Kernels
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.Hoist
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeProduct
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.KernelSlice
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit

/-! Checked measured inline multiplication product at DoubleMul2. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64.P521Field

def DoubleMul2Code : List Instr := ((doubleFnBlocks.drop 75).flatten.drop 22).take 355
def DoubleMul2Early : List Instr := ((doubleFnBlocks.drop 75).flatten.drop 22).take 39
def DoubleMul2Rest : List Instr := ((doubleFnBlocks.drop 76).flatten.drop 29).take 316
def DoubleMul2Loads : List Instr := [
  .ldr .x .x3 .x28 432,
  .ldr .x .x4 .x28 440,
  .ldr .x .x5 .x28 144,
  .ldr .x .x6 .x28 152,
  .ldr .x .x7 .x28 160,
  .ldr .x .x8 .x28 168,
  .ldr .x .x9 .x28 176,
  .ldr .x .x10 .x28 184,
  .ldr .x .x11 .x28 192,
  .ldr .x .x12 .x28 200,
  .ldr .x .x13 .x28 208]

theorem DoubleMul2_source : DoubleMul2Code=(doubleFnBlocks.flatten.drop 2422).take 355 := by
  have h := drop_flatten_prefix doubleFnBlocks 75 2400 22
    (by rw [List.length_flatten]; decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 355) h.symm

theorem DoubleMul2_hoist : hoistLoads .x28 DoubleMul2Early=some (DoubleMul2Loads,pointMulRow0Arithmetic) := by lit_decide

theorem DoubleMul2_split : DoubleMul2Code=DoubleMul2Early++DoubleMul2Rest := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128 <;> decide

theorem DoubleMul2_normalized : pointMulProductCode .x28 432 .x28 144 .x28 360=
    (DoubleMul2Loads++pointMulRow0Arithmetic)++DoubleMul2Rest := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128 <;> decide

theorem DoubleMul2_ok {s : State} {pa pb po : Addr} {size cap room : Nat}
    (ha : Ptr s .x28 pa size) (hb : Ptr s .x28 pb cap) (ht : PtrW s .x28 po room)
    (hA : 504≤size) (hB : 216≤cap) (hO : 424≤room)
    (stable : StableInput s (off pa 432) (off po 360))
    (ha' : wordsVal s.mem (off pa 432) 0 9<2^521)
    (hb' : wordsVal s.mem (off pb 144) 0 9<2^521) :
    WP isa (.block DoubleMul2Code) s
      (PointMulProductInv s (off pa 432) (off po 360) (wordsVal s.mem (off pb 144) 0 9)) := by
  have h := point_mul_product_ok (a:=432) (b:=144) (o:=360) ha hb ht hA hB hO
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) stable ha' hb'
  rw [DoubleMul2_normalized,WP.block_append_iff] at h
  rw [DoubleMul2_split,WP.block_append_iff]
  exact WP.hoistLoads DoubleMul2_hoist h

end VG.Proof.Mont.AArch64.P521Field
