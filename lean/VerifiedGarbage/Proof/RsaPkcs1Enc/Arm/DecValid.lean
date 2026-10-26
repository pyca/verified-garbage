module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecScan
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Select
import VerifiedGarbage.Proof.RsaPkcs1Enc.Decrypt
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Encode
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Tactic.ToDual

/-!
# RSAES-PKCS1-v1_5 decryption on ARMv7: the validity and the length

The validity of the padding as the scan finds it (`vEM`), the selected
length (`lselOf`), the mask of a successful private-key operation, and the
length masked with it (`validBlock_wp`), written as a 64-bit word to
`*msg_len` (`mlStore_wp`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.Arm.Dec

open VG VG.Arm VG.Impl.RsaPkcs1Enc.Arm.Decrypt VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_dp wp_ldrb wp_str op2_imm op2_reg op2_lsr dpVal)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.RsaPkcs1Enc (firstZero vEM vOf lselOf)

variable {P : EP}

/-! ## Bits -/

theorem negbit (b : Bool) : (0 : BitVec 32) - BitVec.ofNat 32 b.toNat = if b then BitVec.allOnes 32 else 0 := by
  cases b <;> decide

theorem sel2 (x y : BitVec 32) (b : Bool) :
    ((x ^^^ y) &&& (if b then BitVec.allOnes 32 else 0)) ^^^ y = if b then x else y := by
  cases b
  · simp
  · show ((x ^^^ y) &&& BitVec.allOnes 32) ^^^ y = x
    rw [BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem band (a b : Bool) : BitVec.ofNat 32 a.toNat &&& BitVec.ofNat 32 b.toNat = BitVec.ofNat 32 (a && b).toNat := by
  cases a <;> cases b <;> decide

theorem mask_and (v : Nat) (b : Bool) :
    BitVec.ofNat 32 v &&& (if b then BitVec.allOnes 32 else 0) = BitVec.ofNat 32 (if b then v else 0) := by
  cases b
  · simp
  · exact BitVec.and_allOnes

theorem ge10 {sep : Nat} :
    ((if sep < 10 then (1 : BitVec 32) else 0) ^^^ 1) = BitVec.ofNat 32 (decide (10 ≤ sep)).toNat := by
  by_cases h : sep < 10
  · simp only [h, ↓reduceIte, show ¬ 10 ≤ sep by omega_arith, decide_false]; decide
  · simp only [h, ↓reduceIte, show 10 ≤ sep by omega_arith, decide_true]; decide

theorem xbit (b : Byte) :
    (if b.setWidth 32 ^^^ 2 = 0 then (1 : BitVec 32) else 0) = BitVec.ofNat 32 (decide (b = 2)).toNat := by
  by_cases h : b = 2
  · subst h; decide
  · have : b.setWidth 32 ^^^ 2 ≠ 0 := by
      intro e
      have e1 := congrArg (· ^^^ (2 : BitVec 32)) e
      simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] at e1
      have e2 := congrArg (BitVec.setWidth 8) e1
      simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32), BitVec.setWidth_eq] at e2
      exact h (e2.trans (by decide))
    simp only [this, ↓reduceIte, h, decide_false]; rfl

theorem xor2_lt (b : Byte) : (b.setWidth 32 ^^^ 2).toNat < 2 ^ 31 := by
  have := b.isLt
  rw [BitVec.toNat_xor, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega_arith)]
  have := Nat.xor_lt_two_pow (n := 8) (x := b.toNat) (y := (2 : BitVec 32).toNat) (by omega_arith) (by decide)
  omega_arith

theorem vOf_bits (b0 b1 : Byte) (f : Bool) (sep : Nat) :
    (((decide (b0 = 0) && decide (b1 = 2)) && f) && decide (10 ≤ sep)) = vOf b0 b1 f sep := by
  simp only [vOf, Bool.decide_and, Bool.decide_eq_true, Bool.and_assoc]

/-! ## The validity -/

/-- The selection's inputs: `AL`, the validity, the separator and the
selected length. -/
abbrev alV (P : EP) (σ : State) : Nat := Spec.RsaPkcs1Enc.altLength P.K (clV P σ)
abbrev vB (P : EP) (σ : State) : Bool := vEM (emOf P σ) P.K
abbrev sepV (P : EP) (σ : State) : Nat := (fz P σ P.K).getD 0
abbrev lselV (P : EP) (σ : State) : Nat := lselOf (vB P σ) (sepV P σ) (alV P σ) P.K
abbrev okB (P : EP) (σ : State) : Bool := decide (rcOf P σ = 1)

theorem alV_le (P : EP) (σ : State) : alV P σ ≤ P.K - 11 := VG.Proof.RsaPkcs1Enc.altLength_le _ _

theorem sep_lt {σ : State} (h : vB P σ = true) : sepV P σ < P.K := by
  simp only [vB, vEM, vOf, decide_eq_true_eq] at h
  obtain ⟨-, -, hs, -⟩ := h
  simp only [sepV, fz]
  cases hf : firstZero (emOf P σ) P.K with
  | none => rw [hf] at hs; cases hs
  | some i => exact (VG.Proof.RsaPkcs1Enc.firstZero_some hf).2.1

theorem lsel_le (P : EP) (σ : State) (hK : 11 ≤ P.K) : lselV P σ ≤ P.K := by
  have := alV_le P σ
  simp only [lselV, lselOf]; split <;> omega_arith

/-- After `validLoads`. -/
def VL (P : EP) (σ s : State) : Prop :=
  SCQ P σ s ∧ s.gpr .r0 = P.out ∧ s.gpr .r7 = BitVec.ofNat 32 P.K ∧ s.gpr .r8 = BitVec.ofNat 32 (alV P σ) ∧
    s.gpr .r9 = rcOf P σ

/-- After `validBlock`. -/
def VB (P : EP) (σ s : State) : Prop :=
  SB P σ s ∧ s.gpr .r6 = 0 ∧ s.gpr .r10 = (if vB P σ then BitVec.allOnes 32 else 0) ∧
    s.gpr .r11 = (if okB P σ then BitVec.allOnes 32 else 0) ∧ s.gpr .r9 = BitVec.ofNat 32 (P.K - lselV P σ) ∧
    s.gpr .r3 = BitVec.ofNat 32 (if okB P σ then lselV P σ else 0)

theorem validLoads_wp {σ s : State} (h : SCQ P σ s) : WP isa (.block validLoads) s (VL P σ) := by
  have hs := h.1.S
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  refine s1.wp_arg (j := 0) (by simp) (by dsimp only; decide) fun t2 s2 u2 => ?_
  refine s2.wp_arg (j := 4) (by simp) (by dsimp only; decide) fun t3 s3 u3 => ?_
  refine s3.wp_slot (d := oAL) (by show oAL + 4 ≤ frameBytes; decide) (by decide) fun t4 s4 u4 => ?_
  refine s4.wp_slot (d := oR) (by show oR + 4 ≤ frameBytes; decide) (by decide) fun t5 s5 u5 => WP.block_nil ?_
  have R : Rest [.r0, .r7, .r8, .r9, .r12] s t5 := (((((u1.rest (by simp)).trans (u2.rest (by simp))).trans
    (u3.rest (by simp))).trans (u4.rest (by simp))).trans (u5.rest (by simp)))
  have m4 : t4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
  have mm : t5.mem = s.mem := by rw [u5.mem, m4]
  obtain ⟨hb, r6, r4, r5⟩ := h
  refine ⟨⟨hb.of_mem s5 mm, by rw [R.gpr _ (by decide), r6], by rw [R.gpr _ (by decide), r4],
    by rw [R.gpr _ (by decide), r5]⟩, ?_, ?_, ?_, ?_⟩
  · rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.gpr]; rfl
  · rw [u5.other _ (by decide), u4.other _ (by decide), u3.gpr]; rfl
  · rw [u5.other _ (by decide), u4.gpr, u3.mem, u2.mem, u1.mem]; exact hb.1.2
  · rw [u5.gpr, m4]; exact hb.2.2

theorem validBlock_wp {σ s : State} (h : VL P σ s) : WP isa (.block validBlock) s (VB P σ) := by
  obtain ⟨⟨hb, r6, r4, r5⟩, r0, r7, r8, r9⟩ := h
  have hs := hb.S
  have hK := hs.1.k64
  have hK' := hs.1.k1024
  have hsep : sepV P σ < 2 ^ 31 := by
    simp only [sepV, fz]
    cases hf : firstZero (emOf P σ) P.K with
    | none => decide
    | some i => have := (VG.Proof.RsaPkcs1Enc.firstZero_some hf).2.1; simp only [Option.getD_some]; omega_arith
  have ha : ∀ d < 2, State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = State.addr P.out + BitVec.ofNat 64 d :=
    fun d hd => by rw [r0, hs.1.outA (by omega_arith)]
  refine wp_ldrb (by decide) (ha 0 (by decide)) (St.out_r hs (by omega_arith)) fun t1 u1 => ?_
  refine wp_dp (op2_imm (by decide)) fun t2 u2 => ?_
  refine wp_mov (op2_lsr (by decide)) fun t3 u3 => ?_
  refine wp_ldrb (by decide) (a := State.addr P.out + BitVec.ofNat 64 1)
    (by rw [u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide)]; exact ha 1 (by decide))
    (by rw [u3.rd, u3.wr, u2.rd, u2.wr, u1.rd, u1.wr]; exact St.out_r hs (by omega_arith)) fun t4 u4 => ?_
  refine wp_dp (op2_imm (by decide)) fun t5 u5 => ?_
  refine wp_dp (op2_imm (by decide)) fun t6 u6 => ?_
  refine wp_mov (op2_lsr (by decide)) fun t7 u7 => ?_
  refine wp_dp (op2_reg _ _) fun t8 u8 => ?_
  refine wp_dp (op2_reg _ _) fun t9 u9 => ?_
  refine wp_dp (op2_imm (by decide)) fun t10 u10 => ?_
  refine wp_mov (op2_lsr (by decide)) fun t11 u11 => ?_
  refine wp_dp (op2_imm (by decide)) fun t12 u12 => ?_
  refine wp_dp (op2_reg _ _) fun t13 u13 => ?_
  refine wp_dp (op2_reg _ _) fun t14 u14 => ?_
  refine wp_dp (op2_imm (by decide)) fun t15 u15 => ?_
  refine wp_dp (op2_reg _ _) fun t16 u16 => ?_
  refine wp_dp (op2_reg _ _) fun t17 u17 => ?_
  refine wp_dp (op2_reg _ _) fun t18 u18 => ?_
  refine wp_dp (op2_reg _ _) fun t19 u19 => ?_
  refine wp_dp (op2_imm (by decide)) fun t20 u20 => ?_
  refine wp_dp (op2_imm (by decide)) fun t21 u21 => ?_
  refine wp_mov (op2_lsr (by decide)) fun t22 u22 => ?_
  refine wp_dp (op2_reg _ _) fun t23 u23 => ?_
  refine wp_dp (op2_reg _ _) fun t24 u24 => ?_
  refine wp_dp (op2_reg _ _) fun t25 u25 => WP.block_nil ?_
  have R7 : Rest [.r2, .r3] s t7 := (((((u1.rest (by simp)).trans (u2.rest (by simp))).trans (u3.rest (by simp))).trans
    (u4.rest (by simp))).trans (u5.rest (by simp))).trans (u6.rest (by simp)) |>.trans (u7.rest (by simp))
  have R16 : Rest [.r2, .r3] s t16 := ((((((((R7.trans (u8.rest (by simp))).trans (u9.rest (by simp))).trans
    (u10.rest (by simp))).trans (u11.rest (by simp))).trans (u12.rest (by simp))).trans (u13.rest (by simp))).trans
    (u14.rest (by simp))).trans (u15.rest (by simp))).trans (u16.rest (by simp))
  have R22 : Rest [.r2, .r3, .r10, .r11] s t22 := (((((R16.mono (by simp)).trans (u17.rest (by simp))).trans
    (u18.rest (by simp))).trans (u19.rest (by simp))).trans (u20.rest (by simp))).trans (u21.rest (by simp))
      |>.trans (u22.rest (by simp))
  have R25 : Rest [.r2, .r3, .r9, .r10, .r11] s t25 := (((R22.mono (by simp)).trans (u23.rest (by simp))).trans
    (u24.rest (by simp))).trans (u25.rest (by simp))
  have m3 : t3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  have mm : t25.mem = s.mem := by
    rw [u25.mem, u24.mem, u23.mem, u22.mem, u21.mem, u20.mem, u19.mem, u18.mem, u17.mem, u16.mem, u15.mem,
      u14.mem, u13.mem, u12.mem, u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, m3]
  have st : P.lay.St σ t25 := hs.2.of_rest R25 mm
  have v3 : t3.gpr .r2 = BitVec.ofNat 32 (decide ((emOf P σ).getD 0 1 = 0)).toNat := by
    rw [u3.gpr, u2.gpr, dpVal, u1.gpr, hb.byte (by omega_arith), isZero_bit _ (byte_lt _), zbit]
  have v7 : t7.gpr .r3 = BitVec.ofNat 32 (decide ((emOf P σ).getD 1 1 = 2)).toNat := by
    rw [u7.gpr, u6.gpr, dpVal, u5.gpr, dpVal, u4.gpr, m3, hb.byte (by omega_arith), isZero_bit _ (xor2_lt _), xbit]
  have v8 : t8.gpr .r2 = BitVec.ofNat 32 (decide ((emOf P σ).getD 0 1 = 0) &&
      decide ((emOf P σ).getD 1 1 = 2)).toNat := by
    rw [u8.gpr, dpVal, v7, u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide),
      u4.other _ (by decide), v3, band]
  have v9 : t9.gpr .r2 = BitVec.ofNat 32 ((decide ((emOf P σ).getD 0 1 = 0) &&
      decide ((emOf P σ).getD 1 1 = 2)) && (fz P σ P.K).isSome).toNat := by
    rw [u9.gpr, dpVal, v8, u8.other _ (by decide), R7.gpr _ (by decide), r4, band]
  have v12 : t12.gpr .r3 = BitVec.ofNat 32 (decide (10 ≤ sepV P σ)).toNat := by
    rw [u12.gpr, dpVal, u11.gpr, u10.gpr, dpVal, u9.other _ (by decide), u8.other _ (by decide),
      R7.gpr _ (by decide), r5, ← ge10]
    congr 1
    exact top_sub hsep (by decide)
  have v13 : t13.gpr .r2 = BitVec.ofNat 32 (vB P σ).toNat := by
    rw [u13.gpr, dpVal, v12, u12.other _ (by decide), u11.other _ (by decide), u10.other _ (by decide), v9, band,
      vOf_bits]
  have v17 : t17.gpr .r10 = if vB P σ then BitVec.allOnes 32 else 0 := by
    rw [u17.gpr, dpVal, R16.gpr _ (by decide), r6, u16.other _ (by decide), u15.other _ (by decide),
      u14.other _ (by decide), v13, negbit]
  have R13 : Rest [.r2, .r3] s t13 := (((((R7.trans (u8.rest (by simp))).trans (u9.rest (by simp))).trans
    (u10.rest (by simp))).trans (u11.rest (by simp))).trans (u12.rest (by simp))).trans (u13.rest (by simp))
  have v19 : t19.gpr .r3 = BitVec.ofNat 32 (lselV P σ) := by
    rw [u19.gpr, dpVal, u18.gpr, dpVal, u17.other _ (by decide), u16.gpr, dpVal, u15.gpr, dpVal, u14.gpr, dpVal,
      u18.other _ (by decide), v17, u17.other _ (by decide), R16.gpr .r8 (by decide), r8, u15.other .r8 (by decide),
      u14.other .r8 (by decide), R13.gpr .r8 (by decide), r8, R13.gpr .r7 (by decide), R13.gpr .r5 (by decide), r7, r5,
      sel2]
    simp only [lselV, lselOf]
    cases hv : vB P σ
    · rfl
    · have := sep_lt hv
      simp only [sepV] at this ⊢
      simp only [↓reduceIte]
      rw [Offset.ofNat_sub_ofNat (by omega_arith)]
      obtain ⟨y, hy⟩ : ∃ y, P.K - (fz P σ P.K).getD 0 = y + 1 := ⟨P.K - (fz P σ P.K).getD 0 - 1, by omega_arith⟩
      rw [hy, sub_one_ofNat (by omega_arith), Nat.add_sub_cancel]
  have v23 : t23.gpr .r11 = if okB P σ then BitVec.allOnes 32 else 0 := by
    rw [u23.gpr, dpVal, R22.gpr .r6 (by decide), r6, u22.gpr, u21.gpr, dpVal, u20.gpr, dpVal,
      u19.other .r9 (by decide), u18.other .r9 (by decide), u17.other .r9 (by decide), R16.gpr .r9 (by decide), r9]
    simp only [okB]
    rcases rcOf_cases P σ with e | e | e <;> simp only [e] <;> decide
  have v24 : t24.gpr .r9 = BitVec.ofNat 32 (P.K - lselV P σ) := by
    rw [u24.gpr, dpVal, u23.other .r7 (by decide), R22.gpr .r7 (by decide), r7, u23.other .r3 (by decide),
      u22.other .r3 (by decide), u21.other .r3 (by decide), u20.other .r3 (by decide), v19,
      Offset.ofNat_sub_ofNat (lsel_le P σ (by omega_arith))]
  have v25 : t25.gpr .r3 = BitVec.ofNat 32 (if okB P σ then lselV P σ else 0) := by
    rw [u25.gpr, dpVal, u24.other .r3 (by decide), u23.other .r3 (by decide), u22.other .r3 (by decide),
      u21.other .r3 (by decide), u20.other .r3 (by decide), v19, u24.other .r11 (by decide), v23, mask_and]
  refine ⟨hb.of_mem st mm, by rw [R25.gpr .r6 (by decide), r6], ?_, by rw [u25.other _ (by decide),
    u24.other _ (by decide), v23], by rw [u25.other _ (by decide), v24], v25⟩
  rw [u25.other _ (by decide), u24.other _ (by decide), u23.other _ (by decide), u22.other _ (by decide),
    u21.other _ (by decide), u20.other _ (by decide), u19.other _ (by decide), u18.other _ (by decide), v17]

/-! ## `*msg_len` -/

/-- A 64-bit word written as two 32-bit halves, the high one zero. -/
theorem readW_pair (m : Mem) (a : Addr) {L : Nat} (hL : L < 2 ^ 32) :
    ((m.writeW a (BitVec.ofNat 32 L)).writeW (a + BitVec.ofNat 64 4) (0 : BitVec 32)).readW a 64 =
      BitVec.ofNat 64 L := by
  show (Mem.read _ a 8).setWidth 64 = _
  rw [Mem.read_eq_of_bytes (n := 8) (v := BitVec.ofNat 64 L) fun i hi => ?_]
  · exact BitVec.setWidth_eq _
  by_cases h4 : i < 4
  · have e1 : ¬ (a + BitVec.ofNat 64 i - (a + BitVec.ofNat 64 4)).toNat < 32 / 8 := by
      rw [show a + BitVec.ofNat 64 i - (a + BitVec.ofNat 64 4) = BitVec.ofNat 64 i - BitVec.ofNat 64 4 by
        rw [Offset.add_sub_add_left]]
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega_arith
    simp only [Mem.writeW]
    rw [Mem.write_apply e1]
    simp only [Mem.write, Mem.sub_ofNat_toNat a (by omega_arith : i < 2 ^ 64), show i < 32 / 8 by omega_arith, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show L < 2 ^ (8 * (32 / 8)) from hL),
      Nat.mod_eq_of_lt (show L < 2 ^ (8 * 8) from Nat.lt_of_lt_of_le hL (by decide))]
    rw [show 8 * (32 / 8) = 32 from rfl, Nat.mod_eq_of_lt hL]
  · have e : a + BitVec.ofNat 64 i = a + BitVec.ofNat 64 4 + BitVec.ofNat 64 (i - 4) := by
      rw [Offset.add_add, show 4 + (i - 4) = i by omega_arith]
    simp only [Mem.writeW, Mem.write]
    rw [e, Mem.sub_ofNat_toNat _ (by omega_arith : i - 4 < 2 ^ 64)]
    simp only [show i - 4 < 32 / 8 by omega_arith, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    have : 2 ^ 32 ≤ 2 ^ (8 * i) := Nat.pow_le_pow_right (by decide) (by omega_arith)
    rw [Nat.div_eq_of_lt (by omega_arith : L % 2 ^ 64 < 2 ^ (8 * i))]
    simp

theorem In.ml_fit {σ : State} (h : In P σ) : P.ml.toNat + 8 ≤ 2 ^ 32 := by
  have := h.ok.fits P.ML (by simp); simpa [Proof.X25519.Arm.addr_toNat] using this

theorem In.out_ml {σ : State} (h : In P σ) : P.OUT.Disjoint P.ML := by
  have := h.ok.wrw
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at this
  exact this.1.1

theorem SB.keep_ml {σ s t : State} (h : SB P σ s) (st : P.lay.St σ t) (hf : Frame [P.ML] s.mem t.mem) :
    SB P σ t := by
  have hs := h.S
  have hK := hs.1.k1024
  have fr : ∀ d, d + 4 ≤ frameBytes → Region.Disjoint ⟨P.lay.fr d, 4⟩ P.ML := fun d hd =>
    hs.1.ok.stk_fr (R := P.ML) (.inr (by simp)) (by simp only [frameBytes] at hd ⊢; omega_arith)
  have one : ∀ {R : Region}, R.Disjoint P.ML → ∀ r ∈ [P.ML], R.Disjoint r := fun hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd
  obtain ⟨⟨⟨hb, cl, am⟩, al⟩, out, rc⟩ := h
  refine ⟨⟨⟨hb.frame st hf fun r hr => ?_, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨hs.1.out_ml, fr oR (by decide)⟩
  · rw [bytes_frame hf (R := sc P sCL 256) (one (hs.1.sc_ml (by decide))) (by show 256 ≤ 2 ^ 64; decide)]; exact cl
  · rw [bytes_frame hf (R := sc P sAM P.K) (one (hs.1.sc_ml (by simp only [sAM]; omega_arith))) (by simp; omega_arith)]
    exact am
  · rw [slot_keep hf (one (fr oAL (by decide)))]; exact al
  · rw [bytes_frame hf (R := P.OUT) (one hs.1.out_ml) (by simp; omega_arith)]; exact out
  · rw [slot_keep hf (one (fr oR (by decide)))]; exact rc

/-- `*msg_len` written. -/
def VW (P : EP) (σ s : State) : Prop :=
  VB P σ s ∧ Spec.Rsa.wordsAt s.mem (State.addr P.ml) 1 = [BitVec.ofNat 64 (if okB P σ then lselV P σ else 0)]

theorem mlLoad_wp {σ s : State} (h : VB P σ s) :
    WP isa (.block mlLoad) s fun t => VB P σ t ∧ t.gpr .r1 = P.ml := by
  have hs := h.1.S
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  refine s1.wp_arg (j := 2) (by simp) (by dsimp only; decide) fun t2 s2 u2 => WP.block_nil ?_
  have R : Rest [.r1, .r12] s t2 := (u1.rest (by simp)).trans (u2.rest (by simp))
  obtain ⟨hb, r6, r10, r11, r9, r3⟩ := h
  exact ⟨⟨hb.of_mem s2 (by rw [u2.mem, u1.mem]), by rw [R.gpr _ (by decide), r6], by rw [R.gpr _ (by decide), r10],
    by rw [R.gpr _ (by decide), r11], by rw [R.gpr _ (by decide), r9], by rw [R.gpr _ (by decide), r3]⟩, u2.gpr⟩

theorem mlStore_wp {σ s : State} (h : VB P σ s ∧ s.gpr .r1 = P.ml) : WP isa (.block mlStore) s (VW P σ) := by
  obtain ⟨hv, r1⟩ := h
  have hs := hv.1.S
  have hK := hs.1.k1024
  have fit := hs.1.ml_fit
  have win : ∀ d, d + 4 ≤ 8 → InRegions s.wr (State.addr P.ml + BitVec.ofNat 64 d) 4 := fun d hd =>
    ⟨P.ML, by rw [hs.2.wr, hs.1.ok.wr]; simp, Offset.contains_base _ hd (by omega_arith)⟩
  refine wp_str (by decide) (a := State.addr P.ml) (by rw [r1, addr_add (by omega_arith)]; exact BitVec.add_zero _)
    (by have := win 0 (by decide); rwa [BitVec.add_zero] at this) fun t1 m1 => ?_
  refine wp_str (by decide) (a := State.addr P.ml + BitVec.ofNat 64 4) (by rw [m1.gpr, r1]; exact addr_add (by omega_arith))
    (by rw [m1.wr]; exact win 4 (by decide)) fun t2 m2 => WP.block_nil ?_
  have mm : t2.mem = (s.mem.writeW (State.addr P.ml) (s.gpr .r3)).writeW
      (State.addr P.ml + BitVec.ofNat 64 4) (s.gpr .r6) := by rw [m2.mem, m1.gpr, m1.mem]
  have c0 : (⟨State.addr P.ml, 8⟩ : Region).Contains (State.addr P.ml) (32 / 8) := by
    have := Offset.contains_base (State.addr P.ml) (d := 0) (n := 4) (k := 8) (by decide) (by decide)
    rwa [BitVec.add_zero] at this
  have fr : Frame [P.ML] s.mem t2.mem := by
    rw [mm]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) (s.gpr .r3) c0).writeW
      (List.mem_singleton_self _) (s.gpr .r6) (Offset.contains_base _ (by decide) (by decide))
  have st : P.lay.St σ t2 := hs.2.write fr (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨P.ML, by simp, fun _ h => h⟩) (by rw [m2.rd, m1.rd])
    (by rw [m2.wr, m1.wr]) (by rw [m2.sp, m1.sp])
  have g : t2.gpr = s.gpr := by rw [m2.gpr, m1.gpr]
  obtain ⟨hb, r6, r10, r11, r9, r3⟩ := hv
  refine ⟨⟨hb.keep_ml st fr, by rw [g, r6], by rw [g, r10], by rw [g, r11], by rw [g, r9], by rw [g, r3]⟩, ?_⟩
  have hl : (if okB P σ then lselV P σ else 0) < 2 ^ 32 := by
    have := lsel_le P σ (by have := hs.1.k64; omega_arith); split <;> omega_arith
  show [t2.mem.readW (State.addr P.ml + BitVec.ofNat 64 (8 * 0)) 64] = _
  rw [mm, r3, r6, show 8 * 0 = 0 from rfl, BitVec.add_zero]
  exact congrArg (· :: []) (readW_pair _ _ hl)

end VG.Proof.RsaPkcs1Enc.Arm.Dec
