module

-- separate module: The inline multiply source/carry replay at DoubleMul0 (DoubleMul0_normalized) costs 1.07s of proof versus 0.48s of imports; DoubleMul0Field composition edits reuse this checked computation.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointMulProduct
public import VerifiedGarbage.Impl.Mont.AArch64.P521Field.Kernels
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.Hoist
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeProduct
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.KernelSlice
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit

/-! Checked measured inline multiplication product at DoubleMul0. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64.P521Field

def DoubleMul0Code : List Instr := ((doubleFnBlocks.drop 18).flatten.drop 28).take 355
def DoubleMul0Early : List Instr := ((doubleFnBlocks.drop 18).flatten.drop 28).take 39
def DoubleMul0Rest : List Instr := ((doubleFnBlocks.drop 20).flatten.drop 3).take 316
def DoubleMul0Loads : List Instr := [
  .ldr .x .x3 .x28 360,
  .ldr .x .x4 .x28 368,
  .ldr .x .x5 .x28 288,
  .ldr .x .x6 .x28 296,
  .ldr .x .x7 .x28 304,
  .ldr .x .x8 .x28 312,
  .ldr .x .x9 .x28 320,
  .ldr .x .x10 .x28 328,
  .ldr .x .x11 .x28 336,
  .ldr .x .x12 .x28 344,
  .ldr .x .x13 .x28 352]

theorem DoubleMul0_source : DoubleMul0Code=(doubleFnBlocks.flatten.drop 604).take 355 := by
  have h := drop_flatten_prefix doubleFnBlocks 18 576 28
    (by rw [List.length_flatten]; decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 355) h.symm

theorem DoubleMul0_hoist : hoistLoads .x28 DoubleMul0Early=some (DoubleMul0Loads,pointMulRow0Arithmetic) := by lit_decide

theorem DoubleMul0_split : DoubleMul0Code=DoubleMul0Early++DoubleMul0Rest := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128 <;> decide

theorem DoubleMul0_normalized : pointMulProductCode .x28 360 .x28 288 .x28 144=
    (DoubleMul0Loads++pointMulRow0Arithmetic)++DoubleMul0Rest := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128 <;> decide

theorem DoubleMul0_ok {s : State} {pa pb po : Addr} {size cap room : Nat}
    (ha : Ptr s .x28 pa size) (hb : Ptr s .x28 pb cap) (ht : PtrW s .x28 po room)
    (hA : 432≤size) (hB : 360≤cap) (hO : 208≤room)
    (stable : StableInput s (off pa 360) (off po 144))
    (ha' : wordsVal s.mem (off pa 360) 0 9<2^521)
    (hb' : wordsVal s.mem (off pb 288) 0 9<2^521) :
    WP isa (.block DoubleMul0Code) s
      (PointMulProductInv s (off pa 360) (off po 144) (wordsVal s.mem (off pb 288) 0 9)) := by
  have h := point_mul_product_ok (a:=360) (b:=288) (o:=144) ha hb ht hA hB hO
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) stable ha' hb'
  rw [DoubleMul0_normalized,WP.block_append_iff] at h
  rw [DoubleMul0_split,WP.block_append_iff]
  exact WP.hoistLoads DoubleMul0_hoist h

end VG.Proof.Mont.AArch64.P521Field
