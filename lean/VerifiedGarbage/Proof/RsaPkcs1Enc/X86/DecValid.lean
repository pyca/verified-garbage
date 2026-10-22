module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecScan
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Select
import VerifiedGarbage.Proof.RsaPkcs1Enc.Decrypt
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecTaint

/-!
# RSAES-PKCS1-v1_5 decryption on x86: the validity and the length

As on ARMv7 (`Proof/RsaPkcs1Enc/Arm/DecValid.lean`): the validity of the
padding as the scan finds it (`vEM`), as a mask in its slot, the selected
length (`lselOf`), the mask of a successful private-key operation in its
slot, and the length masked with it (`validRest_vp`), written as a 64-bit
word to `*msg_len` (`mlRest_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Dec

open VG VG.Impl.RsaPkcs1Enc.X86.Decrypt VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.X86.Wp
open VG.Proof.Mont.X86 (wp_storeS)
open VG.Proof.RsaPkcs1Enc (firstZero vEM vOf lselOf)

variable {P : EP}

/-! ## Masks -/

theorem mk_and (a b : Bool) : mk a &&& mk b = mk (a && b) := by cases a <;> cases b <;> decide

theorem mk_not (b : Bool) : mk b ^^^ BitVec.allOnes 32 = mk (!b) := by cases b <;> decide

theorem sel2 (x y : BitVec 32) (b : Bool) : ((x ^^^ y) &&& mk b) ^^^ y = if b then x else y := by
  cases b
  · simp only [mk, Bool.false_eq_true, ↓reduceIte, BitVec.and_zero, BitVec.zero_xor]
  · simp only [mk, ↓reduceIte, BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem mask_and (v : Nat) (b : Bool) :
    BitVec.ofNat 32 v &&& mk b = BitVec.ofNat 32 (if b then v else 0) := by
  cases b
  · simp only [mk, Bool.false_eq_true, ↓reduceIte, BitVec.and_zero]
  · exact BitVec.and_allOnes

/-- `b ^ 2` is zero exactly when the byte `b` is 2. -/
theorem xcf (b : Byte) : decide ((b.setWidth 32 ^^^ 2).toNat < (1 : BitVec 32).toNat) = decide (b = 2) := by
  have e1 : (1 : BitVec 32).toNat = 1 := rfl
  rw [e1]
  by_cases h : b = 2
  · subst h; decide
  · have : b.setWidth 32 ^^^ 2 ≠ 0 := by
      intro e
      have e1 := congrArg (· ^^^ (2 : BitVec 32)) e
      simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] at e1
      have e2 := congrArg (BitVec.setWidth 8) e1
      simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32), BitVec.setWidth_eq] at e2
      exact h (e2.trans (by decide))
    have : (b.setWidth 32 ^^^ 2).toNat ≠ 0 := fun e => this (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
    rw [decide_eq_false h, decide_eq_false (by omega)]

theorem sepcf {sep : Nat} (h : sep < 2 ^ 32) :
    decide ((BitVec.ofNat 32 sep).toNat < (10 : BitVec 32).toNat) = decide (sep < 10) := by
  have e : (10 : BitVec 32).toNat = 10 := rfl
  rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem okcf (P : EP) (σ : State) :
    mk (decide ((rcOf P σ ^^^ 1).toNat < (1 : BitVec 32).toNat)) = mk (decide (rcOf P σ = 1)) := by
  rcases rcOf_cases P σ with e | e | e <;> rw [e] <;> decide

theorem vOf_bits (b0 b1 : Byte) (f : Bool) (sep : Nat) :
    (((decide (b0 = 0) && decide (b1 = 2)) && f) && !decide (sep < 10)) = vOf b0 b1 f sep := by
  by_cases c : sep < 10
  · simp [vOf, c, show ¬ 10 ≤ sep by omega]
  · simp [vOf, c, show 10 ≤ sep by omega, Bool.and_assoc]

/-! ## The validity -/

/-- The selection's inputs: `AL`, the validity, the separator and the
selected length. -/
abbrev alV (P : EP) (σ : State) : Nat := Spec.RsaPkcs1Enc.altLength P.K (clV P σ)
abbrev vB (P : EP) (σ : State) : Bool := vEM (emOf P σ) P.K
abbrev sepV (P : EP) (σ : State) : Nat := (fz P σ P.K).getD 0
abbrev lselV (P : EP) (σ : State) : Nat := lselOf (vB P σ) (sepV P σ) (alV P σ) P.K
abbrev okB (P : EP) (σ : State) : Bool := decide (rcOf P σ = 1)

theorem alV_le (P : EP) (σ : State) : alV P σ ≤ P.K - 11 := VG.Proof.RsaPkcs1Enc.altLength_le _ _

theorem sep_lt (P : EP) (σ : State) : sepV P σ < P.K ∨ sepV P σ = 0 := by
  simp only [sepV, fz]
  cases hf : firstZero (emOf P σ) P.K with
  | none => exact .inr rfl
  | some i => exact .inl (VG.Proof.RsaPkcs1Enc.firstZero_some hf).2.1

theorem sep_ok {σ : State} (h : vB P σ = true) : 10 ≤ sepV P σ ∧ sepV P σ < P.K := by
  have h' := h
  simp only [vB, vEM, vOf, decide_eq_true_eq] at h'
  obtain ⟨-, -, hs, h10⟩ := h'
  refine ⟨h10, ?_⟩
  simp only [sepV, fz]
  cases hf : firstZero (emOf P σ) P.K with
  | none => rw [hf] at hs; cases hs
  | some i => exact (VG.Proof.RsaPkcs1Enc.firstZero_some hf).2.1

theorem lsel_le (P : EP) (σ : State) (hK : 11 ≤ P.K) : lselV P σ ≤ P.K := by
  have := alV_le P σ
  simp only [lselV, lselOf]; split <;> omega

/-- `out`, `AL` and the result kept by a store to another slot of the frame. -/
theorem SB.keep_fr {σ s t : State} (h : SB P σ s) (st : P.lay.St σ t) {d : Nat} {v : BitVec 32}
    (hm : t.mem = s.mem.writeW (P.lay.fr d) v) (hd : d + 4 ≤ frameBytes) (ho : d + 4 ≤ oR ∨ oR + 4 ≤ d)
    (hal : d + 4 ≤ oAL ∨ oAL + 4 ≤ d) : SB P σ t := by
  have hs := h.S
  have hK := hs.1.k1024
  obtain ⟨⟨ir, al⟩, out, rc⟩ := h
  have fr : Frame [⟨P.lay.fr d, 4⟩] s.mem t.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) v (Region.contains_self _ _)
  refine ⟨⟨ir.keep_fr st hm hd ho, ?_⟩, ?_, ?_⟩
  · rw [hm, Lay.readW_fr_other _ _ _ hal.symm (by decide) (by simp only [frameBytes] at hd; omega)]; exact al
  · rw [Proof.RsaPkcs1Sig.bytesAt_frame fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hs.1.ok.stk_fr (R := P.OUT) (.inr (by simp)) (by show d + 4 ≤ frameBytes + 16; omega)).symm) (by omega)]
    exact out
  · rw [hm, Lay.readW_fr_other _ _ _ ho.symm (by decide) (by simp only [frameBytes] at hd; omega)]; exact rc

/-- After the load of `out`'s pointer. -/
def V0 (P : EP) (σ s : State) : Prop := SCQ P σ s ∧ s.gpr .esi = P.out

/-- After `validBlock`: the masks in their slots, `k - len` and `len & OK`. -/
def VB (P : EP) (σ s : State) : Prop :=
  SB P σ s ∧ s.mem.readW (P.lay.fr oV) 32 = mk (vB P σ) ∧ s.mem.readW (P.lay.fr oOK) 32 = mk (okB P σ) ∧
    s.gpr .ebx = BitVec.ofNat 32 (P.K - lselV P σ) ∧
    s.gpr .edx = BitVec.ofNat 32 (if okB P σ then lselV P σ else 0)

theorem validHead_vp : VP (SCQ P) (.block (validBlock.take 1)) (V0 P) :=
  VP.taint [.esp] validHead_taint (sp_agree fun _ _ h => h.1.S) fun σ s h => by
    have hs := h.1.S
    refine St.argv hs (j := 0) (by decide) (d := .esi) (by decide) fun t1 s1 u1 => WP.block_nil ?_
    obtain ⟨hb, bx, di⟩ := h
    exact ⟨⟨hb.of_mem s1.2 u1.mem, by rw [u1.other _ (by decide), bx], by rw [u1.other _ (by decide), di]⟩,
      u1.gpr⟩

theorem In.outA0 {σ : State} (h : In P σ) {d : Nat} (hd : d < P.K) :
    addr P.out d = P.out.setWidth 64 + BitVec.ofNat 64 d := by
  have := h.out_fit
  exact addr_eq (by omega)

theorem validRest_vp : VP (V0 P) (.block (validBlock.drop 1)) (VB P) :=
  VP.taint [.esp, .esi] validRest_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.1.1.S.2.sp, h₂.1.1.S.2.sp]
      · rw [h₁.2, h₂.2]) fun σ s h => by
    obtain ⟨⟨hb, bx, di⟩, si⟩ := h
    have hs := hb.S
    have hK := hs.1.k64
    have hK' := hs.1.k1024
    have hsep : sepV P σ < 2 ^ 32 := by have := sep_lt P σ; omega
    simp only [validBlock, List.drop_succ_cons, List.drop_zero]
    refine wp_movzx8 (a := P.out.setWidth 64 + BitVec.ofNat 64 0)
      (by show s.ea ⟨.esi, 0⟩ = _; rw [ea_at, si, hs.1.outA0 (by omega)]) (St.out_r hs (by omega)) fun t1 u1 => ?_
    refine wp_subi fun t2 u2 c2 _ => ?_
    refine wp_sbb_self c2 fun t3 u3 => ?_
    refine wp_movzx8 (a := P.out.setWidth 64 + BitVec.ofNat 64 1)
      (by show t3.ea ⟨.esi, 1⟩ = _
          rw [ea_at, u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), si,
            hs.1.outA0 (by omega)])
      (by rw [u3.rd, u3.wr, u2.rd, u2.wr, u1.rd, u1.wr]; exact St.out_r hs (by omega)) fun t4 u4 => ?_
    refine wp_xorI fun t5 u5 => ?_
    refine wp_subi fun t6 u6 c6 _ => ?_
    refine wp_sbb_self c6 fun t7 u7 => ?_
    refine wp_and fun t8 u8 => ?_
    refine wp_and fun t9 u9 => ?_
    refine wp_mov fun t10 u10 => ?_
    refine wp_subi fun t11 u11 c11 _ => ?_
    refine wp_sbb_self c11 fun t12 u12 => ?_
    refine wp_xorI fun t13 u13 => ?_
    refine wp_and fun t14 u14 => ?_
    have st14 : P.lay.St σ t14 := (((((((((((((hs.2.upd u1 (by decide)).upd u2 (by decide)).upd u3 (by decide)).upd
      u4 (by decide)).upd u5 (by decide)).upd u6 (by decide)).upd u7 (by decide)).upd u8 (by decide)).upd u9
      (by decide)).upd u10 (by decide)).upd u11 (by decide)).upd u12 (by decide)).upd u13 (by decide)).upd u14
      (by decide)
    refine st14.wp_strFr (d := oV) (by show oV + 4 ≤ frameBytes; decide) fun t15 st15 m15 => ?_
    refine St.argv ⟨hs.1, st15⟩ (j := 4) (by decide) (d := .edx) (by decide) fun t16 s16 u16 => ?_
    refine wp_sub fun t17 u17 _ => ?_
    refine wp_subi fun t18 u18 _ _ => ?_
    have st18 := (s16.2.upd u17 (by decide)).upd u18 (by decide)
    refine st18.wp_slot (d := oAL) (by show oAL + 4 ≤ frameBytes; decide) (r := .ecx) (by decide)
      fun t19 st19 u19 => ?_
    refine wp_xor fun t20 u20 => ?_
    refine wp_and fun t21 u21 => ?_
    refine wp_xor fun t22 u22 => ?_
    have st22 := ((st19.upd u20 (by decide)).upd u21 (by decide)).upd u22 (by decide)
    refine st22.wp_slot (d := oR) (by show oR + 4 ≤ frameBytes; decide) (r := .eax) (by decide)
      fun t23 st23 u23 => ?_
    refine wp_xorI fun t24 u24 => ?_
    refine wp_subi fun t25 u25 c25 _ => ?_
    refine wp_sbb_self c25 fun t26 u26 => ?_
    have st26 := ((st23.upd u24 (by decide)).upd u25 (by decide)).upd u26 (by decide)
    refine st26.wp_strFr (d := oOK) (by show oOK + 4 ≤ frameBytes; decide) fun t27 st27 m27 => ?_
    refine St.argv ⟨hs.1, st27⟩ (j := 4) (by decide) (d := .ebx) (by decide) fun t28 s28 u28 => ?_
    refine wp_sub fun t29 u29 _ => ?_
    refine wp_and fun t30 u30 => WP.block_nil ?_
    have st30 := (s28.2.upd u29 (by decide)).upd u30 (by decide)
    -- The values.
    have m14 : t14.mem = s.mem := by
      rw [u14.mem, u13.mem, u12.mem, u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem,
        u2.mem, u1.mem]
    have a3 : t3.gpr .eax = mk (decide ((emOf P σ).getD 0 1 = 0)) := by
      rw [u3.gpr, sbb_mk, u1.gpr, hb.byte (i := 0) (by omega), zcf]
    have d7 : t7.gpr .edx = mk (decide ((emOf P σ).getD 1 1 = 2)) := by
      rw [u7.gpr, sbb_mk, u5.gpr, u4.gpr, u3.mem, u2.mem, u1.mem, hb.byte (by omega), xcf]
    have a9 : t9.gpr .eax = mk ((decide ((emOf P σ).getD 0 1 = 0) && decide ((emOf P σ).getD 1 1 = 2)) &&
        (fz P σ P.K).isSome) := by
      rw [u9.gpr, u8.gpr, d7]
      simp (disch := decide) only [u8.other, u7.other, u6.other, u5.other, u4.other]
      rw [a3]
      simp (disch := decide) only [u3.other, u2.other, u1.other]
      rw [bx, mk_and, mk_and]
    have d13 : t13.gpr .edx = mk (!decide (sepV P σ < 10)) := by
      rw [u13.gpr, u12.gpr, sbb_mk, u10.gpr]
      simp (disch := decide) only [u9.other, u8.other, u7.other, u6.other, u5.other, u4.other, u3.other,
        u2.other, u1.other]
      rw [di, sepcf hsep, mk_not]
    have a14 : t14.gpr .eax = mk (vB P σ) := by
      rw [u14.gpr, d13, u13.other _ (by decide), u12.other _ (by decide), u11.other _ (by decide),
        u10.other _ (by decide), a9, mk_and, vOf_bits]
    have mm15 : t15.mem = s.mem.writeW (P.lay.fr oV) (mk (vB P σ)) := by rw [m15.mem, m14, a14]
    have d18 : t18.gpr .edx = BitVec.ofNat 32 P.K - BitVec.ofNat 32 (sepV P σ) - 1 := by
      rw [u18.gpr, u17.gpr, u16.gpr, u16.other _ (by decide), m15.gpr]
      simp (disch := decide) only [u14.other, u13.other, u12.other, u11.other, u10.other, u9.other, u8.other,
        u7.other, u6.other, u5.other, u4.other, u3.other, u2.other, u1.other]
      rw [di]; rfl
    have m18 : t18.mem = t15.mem := by rw [u18.mem, u17.mem, u16.mem]
    have c19 : t19.gpr .ecx = BitVec.ofNat 32 (alV P σ) := by
      rw [u19.gpr, m18, mm15, Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide)]; exact hb.1.2
    have a21 : t20.gpr .eax = mk (vB P σ) := by
      rw [u20.other _ (by decide), u19.other _ (by decide), u18.other _ (by decide),
        u17.other _ (by decide), u16.other _ (by decide), m15.gpr, a14]
    have d22 : t22.gpr .edx = BitVec.ofNat 32 (lselV P σ) := by
      rw [u22.gpr, u21.gpr, a21, u20.gpr, u21.other _ (by decide), u20.other _ (by decide), c19,
        u19.other _ (by decide), d18, sel2]
      simp only [lselV, lselOf]
      cases hv : vB P σ
      · rfl
      · have := sep_ok hv
        simp only [↓reduceIte]
        rw [Offset.ofNat_sub_ofNat (by omega)]
        exact Offset.ofNat_sub_ofNat (d := 1) (by omega)
    have m22 : t22.mem = t15.mem := by rw [u22.mem, u21.mem, u20.mem, u19.mem, m18]
    have r23 : t23.gpr .eax = rcOf P σ := by
      rw [u23.gpr, m22, mm15, Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide)]; exact hb.2.2
    have a26 : t26.gpr .eax = mk (okB P σ) := by
      rw [u26.gpr, sbb_mk, u24.gpr, r23]; exact okcf P σ
    have m26 : t26.mem = t15.mem := by rw [u26.mem, u25.mem, u24.mem, u23.mem, m22]
    have mm27 : t27.mem = t15.mem.writeW (P.lay.fr oOK) (mk (okB P σ)) := by rw [m27.mem, m26, a26]
    have d28 : t28.gpr .edx = BitVec.ofNat 32 (lselV P σ) := by
      rw [u28.other _ (by decide), m27.gpr, u26.other _ (by decide), u25.other _ (by decide),
        u24.other _ (by decide), u23.other _ (by decide), d22]
    have hl := lsel_le P σ (by omega)
    have b30 : t30.gpr .ebx = BitVec.ofNat 32 (P.K - lselV P σ) := by
      rw [u30.other _ (by decide), u29.gpr, u28.gpr, d28]
      exact Offset.ofNat_sub_ofNat hl
    have d30 : t30.gpr .edx = BitVec.ofNat 32 (if okB P σ then lselV P σ else 0) := by
      rw [u30.gpr, u29.other _ (by decide), d28, u29.other _ (by decide), u28.other _ (by decide), m27.gpr, a26,
        mask_and]
    have m30 : t30.mem = t27.mem := by rw [u30.mem, u29.mem, u28.mem]
    have sb15 := (hb.of_mem st14 m14).keep_fr st15 (m15.mem) (by decide) (by simp only [oR, oV]; decide)
      (by simp only [oAL, oV]; decide)
    have sb27 := (sb15.of_mem st26 m26).keep_fr st27 (by rw [m27.mem]) (by decide)
      (by simp only [oR, oOK]; decide) (by simp only [oAL, oOK]; decide)
    refine ⟨sb27.of_mem st30 m30, ?_, ?_, b30, d30⟩
    · rw [m30, mm27, Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide), mm15,
        Mem.readW_writeW_self32]
    · rw [m30, mm27, Mem.readW_writeW_self32]

end VG.Proof.RsaPkcs1Enc.X86.Dec
