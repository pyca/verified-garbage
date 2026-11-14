module

-- separate module: The off-diagonal cross-product carry proof at PointCross1 (point_cross1_ok) costs 0.76s of proof versus 0.74s of imports; PointLow composition edits reuse this checked computation.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross1
public import VerifiedGarbage.Impl.Mont.AArch64.P521Field.Kernels
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MulRow
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointCarry
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Reduce

/-! The measured fused point-square cross-product schedule. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64.P521Square (cross1_value)

def pointCross1Code : List Instr := [
  .mul .x .x10 .x3 .x4,
  .adds .x .x13 .x13 .x10,
  .mul .x .x10 .x3 .x5,
  .adcs .x .x14 .x14 .x10,
  .mul .x .x10 .x3 .x6,
  .adcs .x .x15 .x15 .x10,
  .mul .x .x10 .x3 .x7,
  .adcs .x .x16 .x16 .x10,
  .mul .x .x10 .x3 .x8,
  .adcs .x .x17 .x17 .x10,
  .mul .x .x10 .x3 .x9,
  .adcs .x .x19 .x19 .x10,
  .movz .x .x20 1 0,
  .cselc .x .x20 .x20 .x0 .hs,
  .umulh .x10 .x3 .x4,
  .adds .x .x14 .x14 .x10,
  .umulh .x10 .x3 .x5,
  .adcs .x .x15 .x15 .x10,
  .umulh .x10 .x3 .x6,
  .adcs .x .x16 .x16 .x10,
  .umulh .x10 .x3 .x7,
  .adcs .x .x17 .x17 .x10,
  .umulh .x10 .x3 .x8,
  .adcs .x .x19 .x19 .x10,
  .umulh .x10 .x3 .x9,
  .adc .x .x20 .x20 .x10,
  .mul .x .x10 .x6 .x7,
  .umulh .x21 .x6 .x7,
  .adds .x .x20 .x20 .x10,
  .adc .x .x21 .x21 .x0]

theorem pointCross1_eq : (VG.Impl.Mont.AArch64.P521Field.doubleFnBlocks.flatten.drop 44).take 30 =
    pointCross1Code := by decide

theorem point_cross1_ok (s : State) (hz : s.gpr .x0=0) :
 WP isa (.block pointCross1Code) s fun t => 
  (t.gpr .x11).toNat + 2^64*(t.gpr .x12).toNat + 2^128*(t.gpr .x13).toNat + 2^192*(t.gpr .x14).toNat + 2^256*(t.gpr .x15).toNat + 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576*(t.gpr .x16).toNat + 39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816*(t.gpr .x17).toNat + 726838724295606890549323807888004534353641360687318060281490199180639288113397923326191050713763565560762521606266177933534601628614656*(t.gpr .x19).toNat + 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096*(t.gpr .x20).toNat + 247330401473104534060502521019647190035131349101211839914063056092897225106531867170316401061243044989597671426016139339351365034306751209967546155101893167916606772148699136*(t.gpr .x21).toNat = (s.gpr .x11).toNat + 2^64*(s.gpr .x12).toNat + 2^128*(s.gpr .x13).toNat + 2^192*(s.gpr .x14).toNat + 2^256*(s.gpr .x15).toNat + 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576*(s.gpr .x16).toNat + 39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816*(s.gpr .x17).toNat + 726838724295606890549323807888004534353641360687318060281490199180639288113397923326191050713763565560762521606266177933534601628614656*(s.gpr .x19).toNat + 2^128*((s.gpr .x3).toNat*(s.gpr .x4).toNat) + 2^192*((s.gpr .x3).toNat*(s.gpr .x5).toNat) + 2^256*((s.gpr .x3).toNat*(s.gpr .x6).toNat) + 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576*((s.gpr .x3).toNat*(s.gpr .x7).toNat) + 39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816*((s.gpr .x3).toNat*(s.gpr .x8).toNat) + 726838724295606890549323807888004534353641360687318060281490199180639288113397923326191050713763565560762521606266177933534601628614656*((s.gpr .x3).toNat*(s.gpr .x9).toNat) + 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096*((s.gpr .x6).toNat*(s.gpr .x7).toNat) ∧
  Keeps [.x10,.x13,.x14,.x15,.x16,.x17,.x19,.x20,.x21] s t := by
 apply WP.of_runBlock
 simp only [pointCross1Code, runBlock_cons, runStep_some, runBlock_nil, reduceExec, read_x,Size.bits,Nat.mul_zero,Nat.reduceLT,CondCode.holds,
  RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, RegUpd.c_write,
  BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, hz,Option.some.injEq, exists_eq_left',carry_select]
 have h := cross1_value (s.gpr .x11) (s.gpr .x12) (s.gpr .x13) (s.gpr .x14) (s.gpr .x15) (s.gpr .x16) (s.gpr .x17) (s.gpr .x19) (s.gpr .x3) (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) (s.gpr .x8) (s.gpr .x9)
 simp only [addCarry_zero] at h
 dsimp only [addCarry,carryOut,mulHi,Size.bits] at h ⊢
 refine ⟨?_, ⟨?_, by simp only [RegUpd.mem_write, RegUpd.mem_addWithCarry],
  by simp only [RegUpd.rd_write, RegUpd.rd_addWithCarry],
  by simp only [RegUpd.wr_write, RegUpd.wr_addWithCarry],
  by simp only [RegUpd.sp_write, RegUpd.sp_addWithCarry]⟩⟩
 · simpa only [BitVec.zero_add,BitVec.add_zero] using h
 · reg_keeps

end VG.Proof.Mont.AArch64.P521Field
