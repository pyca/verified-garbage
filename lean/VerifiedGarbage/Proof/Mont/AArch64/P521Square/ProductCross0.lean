module
public import VerifiedGarbage.Impl.Mont.AArch64.P521Square
public import VerifiedGarbage.Proof.Ed25519.AArch64.SqrRows
public import VerifiedGarbage.Proof.Mont.AArch64.Words
import Mathlib.Tactic.SplitIfs
@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Square
open VG VG.AArch64 VG.Impl.Mont.AArch64.P521Square
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64
theorem cross0_arith {v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 _k5 _k8 _k11 _k14 _k17 _k20 _k21 P0 P1 P2 P3 P4 P5 P6 : Nat}
 (e0 : v5 + 2^64*_k5 = v2 + v3 + 0)
 (e1 : v8 + 2^64*_k8 = v4 + v6 + _k5)
 (e2 : v11 + 2^64*_k11 = v7 + v9 + _k8)
 (e3 : v14 + 2^64*_k14 = v10 + v12 + _k11)
 (e4 : v17 + 2^64*_k17 = v13 + v15 + _k14)
 (e5 : v20 + 2^64*_k20 = v16 + v18 + _k17)
 (e6 : v21 + 2^64*_k21 = v19 + 0 + _k20)
 (e7 : v1 + 2^64*v2 = P0)
 (e8 : v3 + 2^64*v4 = P1)
 (e9 : v6 + 2^64*v7 = P2)
 (e10 : v9 + 2^64*v10 = P3)
 (e11 : v12 + 2^64*v13 = P4)
 (e12 : v15 + 2^64*v16 = P5)
 (e13 : v18 + 2^64*v19 = P6)
 (_b0 : P0 ≤ (2^64-1)*(2^64-1))
 (_b1 : P1 ≤ (2^64-1)*(2^64-1))
 (_b2 : P2 ≤ (2^64-1)*(2^64-1))
 (_b3 : P3 ≤ (2^64-1)*(2^64-1))
 (_b4 : P4 ≤ (2^64-1)*(2^64-1))
 (_b5 : P5 ≤ (2^64-1)*(2^64-1))
 (_b6 : P6 ≤ (2^64-1)*(2^64-1))
 (_c0 : _k5 ≤ 1)
 (_c1 : _k8 ≤ 1)
 (_c2 : _k11 ≤ 1)
 (_c3 : _k14 ≤ 1)
 (_c4 : _k17 ≤ 1)
 (_c5 : _k20 ≤ 1)
 (_c6 : _k21 ≤ 1)
 (_v8 : v1<2^64)
 (_v9 : v2<2^64)
 (_v10 : v3<2^64)
 (_v11 : v4<2^64)
 (_v12 : v5<2^64)
 (_v13 : v6<2^64)
 (_v14 : v7<2^64)
 (_v15 : v8<2^64)
 (_v16 : v9<2^64)
 (_v17 : v10<2^64)
 (_v18 : v11<2^64)
 (_v19 : v12<2^64)
 (_v20 : v13<2^64)
 (_v21 : v14<2^64)
 (_v22 : v15<2^64)
 (_v23 : v16<2^64)
 (_v24 : v17<2^64)
 (_v25 : v18<2^64)
 (_v26 : v19<2^64)
 (_v27 : v20<2^64)
 (_v28 : v21<2^64)
 : v1 + 2^64*v5 + 2^128*v8 + 2^192*v11 + 2^256*v14 + 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576*v17 + 39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816*v20 + 726838724295606890549323807888004534353641360687318060281490199180639288113397923326191050713763565560762521606266177933534601628614656*v21 = P0 + 2^64*P1 + 2^128*P2 + 2^192*P3 + 2^256*P4 + 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576*P5 + 39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816*P6 := by
 omega

theorem cross0_value (a2 a3 a4 a5 a6 a7 a8 a9 : BitVec 64) :
 let v1 := a2 * a3
 let v2 := mulHi a2 a3
 let v3 := a2 * a4
 let v4 := mulHi a2 a4
 let _k5 := carryOut v2 v3 false
 let v5 := addCarry v2 v3 false
 let v6 := a2 * a5
 let v7 := mulHi a2 a5
 let _k8 := carryOut v4 v6 _k5
 let v8 := addCarry v4 v6 _k5
 let v9 := a2 * a6
 let v10 := mulHi a2 a6
 let _k11 := carryOut v7 v9 _k8
 let v11 := addCarry v7 v9 _k8
 let v12 := a2 * a7
 let v13 := mulHi a2 a7
 let _k14 := carryOut v10 v12 _k11
 let v14 := addCarry v10 v12 _k11
 let v15 := a2 * a8
 let v16 := mulHi a2 a8
 let _k17 := carryOut v13 v15 _k14
 let v17 := addCarry v13 v15 _k14
 let v18 := a2 * a9
 let v19 := mulHi a2 a9
 let _k20 := carryOut v16 v18 _k17
 let v20 := addCarry v16 v18 _k17
 let _k21 := carryOut v19 (0 : BitVec 64) _k20
 let v21 := addCarry v19 (0 : BitVec 64) _k20
 v1.toNat + 2^64*v5.toNat + 2^128*v8.toNat + 2^192*v11.toNat + 2^256*v14.toNat + 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576*v17.toNat + 39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816*v20.toNat + 726838724295606890549323807888004534353641360687318060281490199180639288113397923326191050713763565560762521606266177933534601628614656*v21.toNat = (a2.toNat*a3.toNat) + 2^64*(a2.toNat*a4.toNat) + 2^128*(a2.toNat*a5.toNat) + 2^192*(a2.toNat*a6.toNat) + 2^256*(a2.toNat*a7.toNat) + 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576*(a2.toNat*a8.toNat) + 39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816*(a2.toNat*a9.toNat) := by
 intro v1 v2 v3 v4 _k5 v5 v6 v7 _k8 v8 v9 v10 _k11 v11 v12 v13 _k14 v14 v15 v16 _k17 v17 v18 v19 _k20 v20 _k21 v21
 exact cross0_arith (addCarry_value v2 v3 false)
  (addCarry_value v4 v6 _k5)
  (addCarry_value v7 v9 _k8)
  (addCarry_value v10 v12 _k11)
  (addCarry_value v13 v15 _k14)
  (addCarry_value v16 v18 _k17)
  (addCarry_value v19 (0 : BitVec 64) _k20)
  (mul_lo_hi a2 a3)
  (mul_lo_hi a2 a4)
  (mul_lo_hi a2 a5)
  (mul_lo_hi a2 a6)
  (mul_lo_hi a2 a7)
  (mul_lo_hi a2 a8)
  (mul_lo_hi a2 a9)
  (mul_le a2 a3)
  (mul_le a2 a4)
  (mul_le a2 a5)
  (mul_le a2 a6)
  (mul_le a2 a7)
  (mul_le a2 a8)
  (mul_le a2 a9)
  (show _k5.toNat ≤ 1 from Bool.toNat_le _)
  (show _k8.toNat ≤ 1 from Bool.toNat_le _)
  (show _k11.toNat ≤ 1 from Bool.toNat_le _)
  (show _k14.toNat ≤ 1 from Bool.toNat_le _)
  (show _k17.toNat ≤ 1 from Bool.toNat_le _)
  (show _k20.toNat ≤ 1 from Bool.toNat_le _)
  (show _k21.toNat ≤ 1 from Bool.toNat_le _)
  (BitVec.isLt v1)
  (BitVec.isLt v2)
  (BitVec.isLt v3)
  (BitVec.isLt v4)
  (BitVec.isLt v5)
  (BitVec.isLt v6)
  (BitVec.isLt v7)
  (BitVec.isLt v8)
  (BitVec.isLt v9)
  (BitVec.isLt v10)
  (BitVec.isLt v11)
  (BitVec.isLt v12)
  (BitVec.isLt v13)
  (BitVec.isLt v14)
  (BitVec.isLt v15)
  (BitVec.isLt v16)
  (BitVec.isLt v17)
  (BitVec.isLt v18)
  (BitVec.isLt v19)
  (BitVec.isLt v20)
  (BitVec.isLt v21)

theorem cross0_ok (s : State) (hz : s.gpr .x30=0) :
 WP isa (.block cross0Code) s fun t => 
  (t.gpr .x12).toNat + 2^64*(t.gpr .x13).toNat + 2^128*(t.gpr .x14).toNat + 2^192*(t.gpr .x15).toNat + 2^256*(t.gpr .x16).toNat + 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576*(t.gpr .x17).toNat + 39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816*(t.gpr .x19).toNat + 726838724295606890549323807888004534353641360687318060281490199180639288113397923326191050713763565560762521606266177933534601628614656*(t.gpr .x20).toNat = ((s.gpr .x2).toNat*(s.gpr .x3).toNat) + 2^64*((s.gpr .x2).toNat*(s.gpr .x4).toNat) + 2^128*((s.gpr .x2).toNat*(s.gpr .x5).toNat) + 2^192*((s.gpr .x2).toNat*(s.gpr .x6).toNat) + 2^256*((s.gpr .x2).toNat*(s.gpr .x7).toNat) + 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576*((s.gpr .x2).toNat*(s.gpr .x8).toNat) + 39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816*((s.gpr .x2).toNat*(s.gpr .x9).toNat) ∧
  Keeps [.x12,.x13,.x10,.x14,.x15,.x16,.x17,.x19,.x20] s t := by
 apply WP.of_runBlock
 simp only [cross0Code, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
  RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, RegUpd.c_write,
  BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, hz,Option.some.injEq, exists_eq_left']
 have h := cross0_value (s.gpr .x2) (s.gpr .x3) (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) (s.gpr .x8) (s.gpr .x9)
 dsimp only [addCarry,carryOut,mulHi,Size.bits] at h ⊢
 refine ⟨h, ⟨?_, by simp only [RegUpd.mem_write, RegUpd.mem_addWithCarry],
  by simp only [RegUpd.rd_write, RegUpd.rd_addWithCarry],
  by simp only [RegUpd.wr_write, RegUpd.wr_addWithCarry],
  by simp only [RegUpd.sp_write, RegUpd.sp_addWithCarry]⟩⟩
 reg_keeps

end VG.Proof.Mont.AArch64.P521Square
