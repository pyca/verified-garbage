module

public import VerifiedGarbage.Impl.RsaPkcs1Enc.PPC64LE.Decrypt
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.RsaPkcs1Enc
import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
import VerifiedGarbage.Proof.RsaPkcs1Enc.Steps
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# `vg_rsa_pkcs1_decrypt` on PPC64LE: IRPRF's messages

The message of block `i` of IRPRF, `I2OSP(i, 2) ‖ label ‖ I2OSP(8 length, 2)`,
written at `scratch + sMsg` (`msgCL_ok` for `CL`, `msgAM_ok` for `AM`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Decrypt
open VG.Proof.Bignum.PPC64LE (Keep)

theorem add_ofNat_inj (p : Addr) {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (p + BitVec.ofNat 64 a = p + BitVec.ofNat 64 b) ↔ a = b :=
  ⟨fun e => Classical.byContradiction fun h => Offset.add_ofNat_ne p ha hb h e, fun e => e ▸ rfl⟩

theorem write1_eq (m : Mem) (b x : Addr) (v : BitVec (8 * 1)) :
    m.write b 1 v x = if x = b then v else m x := by
  by_cases h : x = b
  · simp only [h, ite_true]; exact VG.Proof.Bignum.PPC64LE.write1_self _ _ _
  · simp only [h, ite_false]; exact Mem.write_apply fun h' => h (by bv_omega)

theorem byte_ofNat (x : Nat) : BitVec.setWidth 8 (BitVec.ofNat 64 x) = BitVec.ofNat 8 x := by
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

theorem bytes11 (m : Mem) (B : Addr) : Spec.Rsa.bytesAt m B 11 = [m (B + BitVec.ofNat 64 0), m (B + BitVec.ofNat 64 1),
    m (B + BitVec.ofNat 64 2), m (B + BitVec.ofNat 64 3), m (B + BitVec.ofNat 64 4), m (B + BitVec.ofNat 64 5),
    m (B + BitVec.ofNat 64 6), m (B + BitVec.ofNat 64 7), m (B + BitVec.ofNat 64 8), m (B + BitVec.ofNat 64 9),
    m (B + BitVec.ofNat 64 10)] :=
  rfl

/-- A byte store at `r9 + d`, for any state with `r9 = B`. -/
theorem exec_stb9 {s : State} {t : Reg} {B : Addr} {d : Nat} (h9 : s.gpr .r9 = B) (hd : d < 2 ^ 15)
    (hw : InRegions s.wr (B + BitVec.ofNat 64 d) 1) :
    exec (.stb t .r9 d) s = some { s with mem := s.mem.write (B + BitVec.ofNat 64 d) 1 ((s.gpr t).setWidth 8) } := by
  rw [exec_stb (by decide) hd (by rw [h9]; exact hw), h9]

theorem am_lo (K : BitVec 64) : BitVec.setWidth 8 (K <<< 3) = BitVec.ofNat 8 (8 * K.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem am_hi (K : BitVec 64) (hK : K.toNat ≤ 1024) :
    BitVec.setWidth 8 (K <<< 3 >>> 8) = BitVec.ofNat 8 (8 * K.toNat / 256) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega

/-- The writes of a message: `Frame` for each of its bytes. -/
theorem frame_bytes {m : Mem} {B : Addr} {d : Nat} (hd : d + 1 ≤ 16) {m' : Mem} (h : Frame [⟨B, 16⟩] m m')
    (v : BitVec (8 * 1)) : Frame [⟨B, 16⟩] m (m'.write (B + BitVec.ofNat 64 d) 1 v) :=
  h.write (List.mem_singleton_self _) _ (Offset.contains_base _ hd (by omega))

theorem msgCL_ok {t : State} {B : Addr} {i : Nat} (h9 : t.gpr .r9 = B) (h11 : t.gpr .r11 = BitVec.ofNat 64 i)
    (hi : i < 256) (hw : ∀ d < 16, InRegions t.wr (B + BitVec.ofNat 64 d) 1) :
    WP isa (.block (msgBytes lengthLabel clLen)) t fun u => (Frame [⟨B, 16⟩] t.mem u.mem ∧
      Spec.Rsa.bytesAt u.mem B 10 =
        Spec.Rsa.i2osp i 2 ++ Spec.RsaPkcs1Enc.ascii "length" ++ Spec.Rsa.i2osp (8 * 256) 2) ∧ Keep [.r10] t u := by
  refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ rfl
  simp only [msgBytes, lengthLabel, clLen, putByte, List.zipIdx, List.zipIdx_cons, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.cons_append, List.nil_append]
  repeat (first
    | with_reducible refine WP.cons (exec_li (by decide)) ?_
    | with_reducible refine WP.cons (exec_lsl (by decide)) ?_
    | with_reducible refine WP.cons (exec_lsr_d (by decide)) ?_
    | refine WP.cons (exec_stb9 (by simp only [VG.Proof.Bignum.PPC64LE.gpr_write, reduceCtorEq, ↓reduceIte, h9])
        (by decide) (hw _ (by decide))) ?_)
  refine WP.block_nil ?_
  simp only [VG.Proof.Bignum.PPC64LE.gpr_write, VG.Proof.Bignum.PPC64LE.mem_write, reduceCtorEq, ↓reduceIte, h11]
  refine ⟨?_, ?_⟩
  · repeat (first
      | exact Frame.refl _ _
      | refine frame_bytes (by decide) ?_ _)
  · rw [bytes10]
    simp only [write1_eq, add_ofNat_inj, Nat.reducePow, Nat.reduceLT, Nat.reduceEqDiff, ite_true,
      ite_false, byte_ofNat, Nat.reduceAdd, Proof.RsaPkcs1Enc.i2osp_two, ascii_length, Nat.div_eq_of_lt hi]
    rfl

theorem msgAM_ok {t : State} {B : Addr} {i : Nat} {K : BitVec 64} (h9 : t.gpr .r9 = B)
    (h11 : t.gpr .r11 = BitVec.ofNat 64 i) (h8 : t.gpr .r8 = K) (hi : i < 256) (hK : K.toNat ≤ 1024)
    (hw : ∀ d < 16, InRegions t.wr (B + BitVec.ofNat 64 d) 1) :
    WP isa (.block (msgBytes messageLabel amLen)) t fun u => (Frame [⟨B, 16⟩] t.mem u.mem ∧
      Spec.Rsa.bytesAt u.mem B 11 =
        Spec.Rsa.i2osp i 2 ++ Spec.RsaPkcs1Enc.ascii "message" ++ Spec.Rsa.i2osp (8 * K.toNat) 2) ∧
      Keep [.r10] t u := by
  refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ rfl
  simp only [msgBytes, messageLabel, amLen, putByte, List.zipIdx, List.zipIdx_cons, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.cons_append, List.nil_append]
  repeat (first
    | with_reducible refine WP.cons (exec_li (by decide)) ?_
    | with_reducible refine WP.cons (exec_lsl (by decide)) ?_
    | with_reducible refine WP.cons (exec_lsr_d (by decide)) ?_
    | refine WP.cons (exec_stb9 (by simp only [VG.Proof.Bignum.PPC64LE.gpr_write, reduceCtorEq, ↓reduceIte, h9])
        (by decide) (hw _ (by decide))) ?_)
  refine WP.block_nil ?_
  simp only [VG.Proof.Bignum.PPC64LE.gpr_write, VG.Proof.Bignum.PPC64LE.mem_write, reduceCtorEq, ↓reduceIte, h11, h8]
  refine ⟨?_, ?_⟩
  · repeat (first
      | exact Frame.refl _ _
      | refine frame_bytes (by decide) ?_ _)
  · rw [bytes11]
    simp only [write1_eq, add_ofNat_inj, Nat.reducePow, Nat.reduceLT, Nat.reduceEqDiff, ite_true,
      ite_false, byte_ofNat, Nat.reduceAdd, am_lo, am_hi K hK, Proof.RsaPkcs1Enc.i2osp_two, ascii_message,
      Nat.div_eq_of_lt hi]
    rfl

end VG.Proof.RsaPkcs1Enc.PPC64LE.Dec
