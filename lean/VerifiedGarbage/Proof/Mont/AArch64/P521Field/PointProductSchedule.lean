module

-- separate module: The computed first-square/product instruction-order identities (pointFirstSquare_normalized) costs 0.73s of proof versus 0.29s of imports; PointSquare composition edits reuse this checked computation.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointLoadedProduct
public import VerifiedGarbage.Impl.Mont.AArch64.P521Field.Kernels
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.Hoist
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeProduct
import VerifiedGarbage.Proof.Framework.Block

/-! Connect the exact square product to the measured interleaved point schedule. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64.P521Field

def pointFirstSquareProduct : List Instr := (doubleFnBlocks.flatten.drop 14).take 206
def pointFirstSquareEarly : List Instr := (doubleFnBlocks.flatten.drop 14).take 30
def pointFirstSquareRest : List Instr := (doubleFnBlocks.flatten.drop 44).take 176
def pointFirstSquareLoads : List Instr := [
  .ldr .x .x2 .x27 144,.ldr .x .x3 .x27 152,
  .ldr .x .x4 .x27 160,.ldr .x .x5 .x27 168,
  .ldr .x .x6 .x27 176,.ldr .x .x7 .x27 184,
  .ldr .x .x8 .x27 192,.ldr .x .x9 .x27 200]

theorem pointFirstSquare_hoist : hoistLoads .x27 pointFirstSquareEarly =
    some (pointFirstSquareLoads,pointCross0Code) := by decide

theorem pointFirstSquare_split : pointFirstSquareProduct=
    pointFirstSquareEarly++pointFirstSquareRest := by
  apply chunks_eq 128 <;> decide

theorem pointFirstSquare_normalized : pointLoadedProduct .x27 144=
    (pointFirstSquareLoads++pointCross0Code)++pointFirstSquareRest := by
  apply chunks_eq 128 <;> decide

/-- Input reads are hoisted only in the proof; emitted instructions retain
all measured load/multiply overlap and the late ninth-limb read. -/
theorem point_first_square_product_ok {s : State} {p : Addr}
    (hp : Ptr s .x27 p 216) (ha : wordsVal s.mem p 144 9<2^521) :
    WP isa (.block pointFirstSquareProduct) s fun t =>
      regsVal t pointProductRegs=wordsVal s.mem p 144 9*wordsVal s.mem p 144 9 ∧
      t.gpr .x6=0 ∧ VG.Proof.Ed25519.AArch64.Keeps pointFullProductClob s t := by
  have h := point_loaded_product_ok hp (d:=144) (by decide) (by decide) (by decide) ha
  rw [pointFirstSquare_normalized,WP.block_append_iff] at h
  rw [pointFirstSquare_split,WP.block_append_iff]
  exact WP.hoistLoads pointFirstSquare_hoist h

end VG.Proof.Mont.AArch64.P521Field
