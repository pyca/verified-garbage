module

-- separate module: The inline multiply source/carry replay at MixedMul7 (MixedMul7_normalized) costs 1.33s of proof versus 0.59s of imports; MixedMul7Field composition edits reuse this checked computation.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointMulProduct
public import VerifiedGarbage.Impl.Mont.AArch64.P521Field.Kernels
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.Hoist
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeProduct
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.KernelSlice
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit

/-! Checked measured inline multiplication product at MixedMul7. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64.P521Field

def MixedMul7Code : List Instr := ((mixedFnBlocks.drop 76).flatten.drop 27).take 353
def MixedMul7Early : List Instr := ((mixedFnBlocks.drop 76).flatten.drop 27).take 38
def MixedMul7Rest : List Instr := ((mixedFnBlocks.drop 78).flatten.drop 1).take 315
def MixedMul7Loads : List Instr := [
  .ldr .x .x3 .x30 216,
  .ldr .x .x4 .x30 224,
  .ldr .x .x5 .x30 144,
  .ldr .x .x6 .x30 152,
  .ldr .x .x7 .x30 160,
  .ldr .x .x8 .x30 168,
  .ldr .x .x9 .x30 176,
  .ldr .x .x10 .x30 184,
  .ldr .x .x11 .x30 192,
  .ldr .x .x12 .x30 200,
  .ldr .x .x13 .x30 208]

theorem MixedMul7_source : MixedMul7Code=(mixedFnBlocks.flatten.drop 2459).take 353 := by
  have h := drop_flatten_prefix mixedFnBlocks 76 2432 27
    (by rw [List.length_flatten]; decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 353) h.symm

theorem MixedMul7_hoist : hoistLoads .x30 MixedMul7Early=some (MixedMul7Loads,pointMulRow0Z2Arithmetic) := by lit_decide

theorem MixedMul7_split : MixedMul7Code=MixedMul7Early++MixedMul7Rest := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128 <;> decide

theorem MixedMul7_normalized : pointMulProductZ2Code .x30 216 .x30 144 .x30 144=
    (MixedMul7Loads++pointMulRow0Z2Arithmetic)++MixedMul7Rest := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128 <;> decide

theorem MixedMul7_ok {s : State} {pa pb po : Addr} {size cap room : Nat}
    (ha : Ptr s .x30 pa size) (hb : Ptr s .x30 pb cap) (ht : PtrW s .x30 po room)
    (hA : 288≤size) (hB : 216≤cap) (hO : 208≤room)
    (hz : s.gpr .x2=0)
    (stable : StableInput s (off pa 216) (off po 144))
    (ha' : wordsVal s.mem (off pa 216) 0 9<2^521)
    (hb' : wordsVal s.mem (off pb 144) 0 9<2^521) :
    WP isa (.block MixedMul7Code) s
      (PointMulProductInv s (off pa 216) (off po 144) (wordsVal s.mem (off pb 144) 0 9)) := by
  have h := point_mul_product_z2_ok (a:=216) (b:=144) (o:=144) ha hb ht hA hB hO
    (by decide) (by decide) (by decide) hz (by decide) (by decide) (by decide) stable ha' hb'
  rw [MixedMul7_normalized,WP.block_append_iff] at h
  rw [MixedMul7_split,WP.block_append_iff]
  exact WP.hoistLoads MixedMul7_hoist h

end VG.Proof.Mont.AArch64.P521Field
