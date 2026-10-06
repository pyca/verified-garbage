import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecKdk
import VerifiedGarbage.Proof.RsaPkcs1Enc.Steps

/-!
# RSAES-PKCS1-v1_5 decryption on AArch64: IRPRF's messages

The message of block `i` of IRPRF, `I2OSP(i, 2) ‖ label ‖ I2OSP(8 length, 2)`,
written at `scratch + sMsg` (`msgCL_ok` for `CL`, `msgAM_ok` for `AM`).
-/

namespace VG.Proof.RsaPkcs1Enc.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Decrypt

theorem add_ofNat_inj (p : Addr) {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (p + BitVec.ofNat 64 a = p + BitVec.ofNat 64 b) ↔ a = b :=
  ⟨fun e => Classical.byContradiction fun h => Offset.add_ofNat_ne p ha hb h e, fun e => e ▸ rfl⟩

theorem byte_imm (v : Nat) :
    BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ofNat 16 v) <<< 0)) = BitVec.ofNat 8 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.shiftLeft_zero, BitVec.toNat_ofNat]
  omega

theorem byte_reg (x : Nat) : BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.ofNat 64 x)) = BitVec.ofNat 8 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem ascii_length : Spec.RsaPkcs1Enc.ascii "length" = [0x6c, 0x65, 0x6e, 0x67, 0x74, 0x68] := by decide

theorem ascii_message : Spec.RsaPkcs1Enc.ascii "message" = [0x6d, 0x65, 0x73, 0x73, 0x61, 0x67, 0x65] := by
  decide

theorem bytes10 (m : Mem) (B : Addr) : Spec.Rsa.bytesAt m B 10 = [m (B + BitVec.ofNat 64 0), m (B + BitVec.ofNat 64 1),
    m (B + BitVec.ofNat 64 2), m (B + BitVec.ofNat 64 3), m (B + BitVec.ofNat 64 4), m (B + BitVec.ofNat 64 5),
    m (B + BitVec.ofNat 64 6), m (B + BitVec.ofNat 64 7), m (B + BitVec.ofNat 64 8), m (B + BitVec.ofNat 64 9)] :=
  rfl

theorem msgCL_ok {t : State} {B : Addr} {i : Nat} (h9 : t.gpr .x9 = B) (h11 : t.gpr .x11 = BitVec.ofNat 64 i)
    (hi : i < 256) (hw : ∀ d < 16, InRegions t.wr (B + BitVec.ofNat 64 d) 1) :
    WP isa (.block (msgBytes lengthLabel clLen)) t fun u => u.rd = t.rd ∧ u.wr = t.wr ∧ u.sp = t.sp ∧
      u.v = t.v ∧ (∀ r ∈ preserved, u.gpr r = t.gpr r) ∧ Frame [⟨B, 16⟩] t.mem u.mem ∧
      Spec.Rsa.bytesAt u.mem B 10 =
        Spec.Rsa.i2osp i 2 ++ Spec.RsaPkcs1Enc.ascii "length" ++ Spec.Rsa.i2osp (8 * 256) 2 := by
  have w0 := hw 0 (by decide)
  have w1 := hw 1 (by decide)
  have w2 := hw 2 (by decide)
  have w3 := hw 3 (by decide)
  have w4 := hw 4 (by decide)
  have w5 := hw 5 (by decide)
  have w6 := hw 6 (by decide)
  have w7 := hw 7 (by decide)
  have w8 := hw 8 (by decide)
  have w9 := hw 9 (by decide)
  apply WP.of_runBlock
  simp only [msgBytes, lengthLabel, clLen, putByte, List.zipIdx, List.zipIdx_cons, List.flatMap_cons,
    List.flatMap_nil, List.cons_append, List.nil_append, List.append_nil, runBlock_cons, runStep_some,
    runBlock_nil, exec, addr, State.read, State.store, Size.bits, BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceMod,
    Nat.reduceLT, Nat.reduceAdd, and_self, ite_true, Option.bind_some, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, RegUpd.v_write,
    reduceCtorEq, ite_false, h9, h11, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9]
  refine ⟨trivial, trivial, trivial, trivial, fun r hr => ?_, ?_, ?_⟩
  · simp only [mem_ne hr (by decide : Reg.x10 ∉ preserved), ite_false]
  · repeat (first
      | exact Frame.refl _ _
      | refine Frame.write ?_ (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide)))
  · rw [bytes10]
    simp only [Bytes.write1_apply, add_ofNat_inj, Nat.reducePow, Nat.reduceLT, Nat.reduceEqDiff, ite_true,
      ite_false, byte_imm, byte_reg, Proof.RsaPkcs1Enc.i2osp_two, ascii_length, Nat.div_eq_of_lt hi]
    rfl

theorem bytes11 (m : Mem) (B : Addr) : Spec.Rsa.bytesAt m B 11 = [m (B + BitVec.ofNat 64 0), m (B + BitVec.ofNat 64 1),
    m (B + BitVec.ofNat 64 2), m (B + BitVec.ofNat 64 3), m (B + BitVec.ofNat 64 4), m (B + BitVec.ofNat 64 5),
    m (B + BitVec.ofNat 64 6), m (B + BitVec.ofNat 64 7), m (B + BitVec.ofNat 64 8), m (B + BitVec.ofNat 64 9),
    m (B + BitVec.ofNat 64 10)] :=
  rfl

theorem am_lo (K : BitVec 64) : BitVec.setWidth 8 (BitVec.setWidth 32 (K <<< 3)) = BitVec.ofNat 8 (8 * K.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem am_hi (K : BitVec 64) (hK : K.toNat ≤ 1024) :
    BitVec.setWidth 8 (BitVec.setWidth 32 (K <<< 3 >>> 8)) = BitVec.ofNat 8 (8 * K.toNat / 256) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega

theorem msgAM_ok {t : State} {B : Addr} {i : Nat} {K : BitVec 64} (h9 : t.gpr .x9 = B)
    (h11 : t.gpr .x11 = BitVec.ofNat 64 i) (h12 : t.gpr .x12 = K) (hi : i < 256) (hK : K.toNat ≤ 1024)
    (hw : ∀ d < 16, InRegions t.wr (B + BitVec.ofNat 64 d) 1) :
    WP isa (.block (msgBytes messageLabel amLen)) t fun u => u.rd = t.rd ∧ u.wr = t.wr ∧ u.sp = t.sp ∧
      u.v = t.v ∧ (∀ r ∈ preserved, u.gpr r = t.gpr r) ∧ Frame [⟨B, 16⟩] t.mem u.mem ∧
      Spec.Rsa.bytesAt u.mem B 11 =
        Spec.Rsa.i2osp i 2 ++ Spec.RsaPkcs1Enc.ascii "message" ++ Spec.Rsa.i2osp (8 * K.toNat) 2 := by
  have w0 := hw 0 (by decide)
  have w1 := hw 1 (by decide)
  have w2 := hw 2 (by decide)
  have w3 := hw 3 (by decide)
  have w4 := hw 4 (by decide)
  have w5 := hw 5 (by decide)
  have w6 := hw 6 (by decide)
  have w7 := hw 7 (by decide)
  have w8 := hw 8 (by decide)
  have w9 := hw 9 (by decide)
  have w10 := hw 10 (by decide)
  apply WP.of_runBlock
  simp only [msgBytes, messageLabel, amLen, putByte, List.zipIdx, List.zipIdx_cons, List.flatMap_cons,
    List.flatMap_nil, List.cons_append, List.nil_append, List.append_nil, runBlock_cons, runStep_some,
    runBlock_nil, exec, addr, State.read, State.store, Size.bits, BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceMod,
    Nat.reduceLT, Nat.reduceAdd, and_self, ite_true, Option.bind_some, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, RegUpd.v_write,
    reduceCtorEq, ite_false, h9, h11, h12, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10]
  refine ⟨trivial, trivial, trivial, trivial, fun r hr => ?_, ?_, ?_⟩
  · simp only [mem_ne hr (by decide : Reg.x10 ∉ preserved), ite_false]
  · repeat (first
      | exact Frame.refl _ _
      | refine Frame.write ?_ (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide)))
  · rw [bytes11]
    simp only [Bytes.write1_apply, add_ofNat_inj, Nat.reducePow, Nat.reduceLT, Nat.reduceEqDiff, ite_true,
      ite_false, byte_imm, byte_reg, am_lo, am_hi K hK, Proof.RsaPkcs1Enc.i2osp_two, ascii_message,
      Nat.div_eq_of_lt hi]
    rfl

end VG.Proof.RsaPkcs1Enc.AArch64.Dec
