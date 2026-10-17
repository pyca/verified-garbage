module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecValid
import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecTaint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# RSAES-PKCS1-v1_5 decryption on ARMv7: the output

Byte `i` of `out` (`obV`): `EM[i]` or `AM[i]` as the validity selects, if
`i ≥ k - len` and the private-key operation succeeded, and zero otherwise
(`selLoop_vp`); then the result returned (`fin_wp`), which is what the
shared contract states (`res_of`, `Res`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.Arm.Dec

open VG VG.Arm VG.Impl.RsaPkcs1Enc.Arm.Decrypt VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_dp wp_ldrb wp_strb wp_subs op2_imm op2_reg op2_lsr dpVal
  eval_ne)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.RsaPkcs1Enc (outByte)

variable {P : EP}

/-- Byte `i` of the output. -/
abbrev obV (P : EP) (σ : State) (i : Nat) : Byte :=
  outByte (vB P σ) (okB P σ) (P.K - lselV P σ) i ((emOf P σ).getD i 1) ((amV P σ).getD i 0)

/-- `j` bytes of `out` written. -/
def SL (P : EP) (j : Nat) (σ s : State) : Prop :=
  S P σ s ∧
    (∀ i < P.K, s.mem (State.addr P.out + BitVec.ofNat 64 i) = if i < j then obV P σ i else (emOf P σ).getD i 1) ∧
    Spec.Rsa.bytesAt s.mem (sc P sAM P.K).base P.K = amV P σ ∧ s.mem.readW (P.lay.fr oR) 32 = rcOf P σ ∧
    Spec.Rsa.wordsAt s.mem (State.addr P.ml) 1 = [BitVec.ofNat 64 (if okB P σ then lselV P σ else 0)] ∧
    s.gpr .r0 = P.out + BitVec.ofNat 32 j ∧ s.gpr .r1 = P.scr + BitVec.ofNat 32 (sAM + j) ∧
    s.gpr .r4 = BitVec.ofNat 32 j ∧ s.gpr .lr = BitVec.ofNat 32 (P.K - j) ∧
    s.gpr .r9 = BitVec.ofNat 32 (P.K - lselV P σ) ∧ s.gpr .r10 = (if vB P σ then BitVec.allOnes 32 else 0) ∧
    s.gpr .r11 = (if okB P σ then BitVec.allOnes 32 else 0) ∧ (emOf P σ).length = P.K

theorem selInit_wp {σ s : State} (h : VW P σ s) : WP isa (.block selInit) s (SL P 0 σ) := by
  obtain ⟨⟨hb, r6, r10, r11, r9, r3⟩, ml⟩ := h
  have hs := hb.S
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  refine s1.wp_arg (j := 0) (by simp) (by dsimp only; decide) fun t2 s2 u2 => ?_
  refine s2.wp_arg (j := 21) (by simp) (by dsimp only; decide) fun t3 s3 u3 => ?_
  refine wp_dp (op2_imm (by decide)) fun t4 u4 => ?_
  refine wp_mov (op2_imm (by decide)) fun t5 u5 => ?_
  have s5 : P.lay.St σ t5 := (s3.of_rest (u4.rest (ws := [.r1]) (by simp)) u4.mem).of_rest
    (u5.rest (ws := [.r4]) (by simp)) u5.mem
  refine s5.wp_arg (j := 4) (by simp) (by dsimp only; decide) fun t6 s6 u6 => WP.block_nil ?_
  have R : Rest [.r0, .r1, .r4, .r12, .lr] s t6 := ((((u1.rest (by simp)).trans (u2.rest (by simp))).trans
    (u3.rest (by simp))).trans (u4.rest (by simp))).trans (u5.rest (by simp)) |>.trans (u6.rest (by simp))
  have mm : t6.mem = s.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  refine ⟨⟨hs.1, s6⟩, fun i hi => ?_, by rw [mm]; exact hb.1.1.2.2, by rw [mm]; exact hb.2.2, by rw [mm]; exact ml,
    ?_, ?_, ?_, ?_, by rw [R.gpr _ (by decide), r9], by rw [R.gpr _ (by decide), r10],
    by rw [R.gpr _ (by decide), r11], emOf_length hb⟩
  · rw [mm, hb.byte hi]; simp
  · rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.gpr]
    exact (BitVec.add_zero _).symm
  · rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr, dpVal, u3.gpr]; rfl
  · rw [u6.other _ (by decide), u5.gpr]
  · rw [u6.gpr]; rfl

/-! ## One byte -/

theorem selByte (e a : Byte) (v : Bool) (c : Prop) [Decidable c] :
    ((if v then e.setWidth 32 else a.setWidth 32) &&& (if c then BitVec.allOnes 32 else 0)).setWidth 8 =
      if c then (if v then e else a) else 0 := by
  (by_cases h : c <;> cases v <;> simp [h]) <;> exact BitVec.and_allOnes

theorem mask_ge {j kl : Nat} (hj : j < 2 ^ 31) (hk : kl < 2 ^ 31) (c : Bool) :
    ((BitVec.ofNat 32 j - BitVec.ofNat 32 kl) >>> 31 - 1) &&& (if c then BitVec.allOnes 32 else 0) =
      if kl ≤ j ∧ c = true then BitVec.allOnes 32 else 0 := by
  rw [top_sub hj hk]
  by_cases h : j < kl
  · simp only [h, ↓reduceIte, show ¬ (kl ≤ j ∧ c = true) from fun h' => by omega]
    cases c <;> decide
  · simp only [h, ↓reduceIte, show kl ≤ j by omega, true_and]
    cases c <;> decide

/-- `m` bytes left. -/
def SLM (P : EP) (m : Nat) (σ s : State) : Prop := m ≤ P.K ∧ SL P (P.K - m) σ s

theorem selBody_vp (n : Nat) : VP (SLM P (n + 1)) (.block selBody) fun σ s =>
    isa.eval .ne s = some (decide (0 < n)) ∧ (n = 0 → SL P P.K σ s) ∧ (0 < n → SLM P n σ s) := by
  refine VP.taint [.r0, .r1, .lr] selBody_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s h => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.2.2.2.2.2.2.1, h₂.2.2.2.2.2.2.1]
    · rw [h₁.2.2.2.2.2.2.2.1, h₂.2.2.2.2.2.2.2.1]
    · rw [h₁.2.2.2.2.2.2.2.2.2.1, h₂.2.2.2.2.2.2.2.2.2.1]
  obtain ⟨hn, hs, ob, am, rc, ml, r0, r1, r4, lr, r9, r10, r11, hEM⟩ := h
  generalize hj : P.K - (n + 1) = j at ob r0 r1 r4 lr
  have hK := hs.1.k64
  have hK' := hs.1.k1024
  have hjK : j < P.K := by omega
  have hl := lsel_le P σ (by omega)
  refine wp_ldrb (by decide) (a := State.addr P.out + BitVec.ofNat 64 j)
    (by rw [r0, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_zero, hs.1.outA hjK])
    (St.out_r hs (by omega)) fun t1 u1 => ?_
  refine wp_ldrb (by decide) (a := State.addr P.scr + BitVec.ofNat 64 (sAM + j))
    (by rw [u1.other _ (by decide), r1, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_zero,
      hs.1.scrA (by simp only [sAM]; omega)])
    (by rw [u1.rd, u1.wr]; exact St.sc_r hs (by simp only [sAM]; omega)) fun t2 u2 => ?_
  refine wp_dp (op2_reg _ _) fun t3 u3 => ?_
  refine wp_dp (op2_reg _ _) fun t4 u4 => ?_
  refine wp_dp (op2_reg _ _) fun t5 u5 => ?_
  refine wp_dp (op2_reg _ _) fun t6 u6 => ?_
  refine wp_mov (op2_lsr (by decide)) fun t7 u7 => ?_
  refine wp_dp (op2_imm (by decide)) fun t8 u8 => ?_
  refine wp_dp (op2_reg _ _) fun t9 u9 => ?_
  refine wp_dp (op2_reg _ _) fun t10 u10 => ?_
  have R10 : Rest [.r2, .r3, .r5] s t10 := (((((((((u1.rest (by simp)).trans (u2.rest (by simp))).trans
    (u3.rest (by simp))).trans (u4.rest (by simp))).trans (u5.rest (by simp))).trans (u6.rest (by simp))).trans
    (u7.rest (by simp))).trans (u8.rest (by simp))).trans (u9.rest (by simp))).trans (u10.rest (by simp))
  have m10 : t10.mem = s.mem := by
    rw [u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have e1 : t1.gpr .r2 = ((emOf P σ).getD j 1).setWidth 32 := by
    rw [u1.gpr, ob j hjK]; simp only [Nat.lt_irrefl, ↓reduceIte]
  have e2 : t2.gpr .r3 = ((amV P σ).getD j 0).setWidth 32 := by
    rw [u2.gpr, u1.mem, ← am, bytesAt_getD hjK, Offset.add_add]
  have v5 : t5.gpr .r2 = if vB P σ then ((emOf P σ).getD j 1).setWidth 32 else ((amV P σ).getD j 0).setWidth 32 := by
    rw [u5.gpr, dpVal, u4.gpr, dpVal, u3.gpr, dpVal, u4.other .r3 (by decide), u3.other .r3 (by decide), e2,
      u3.other .r10 (by decide), u2.other .r10 (by decide), u1.other .r10 (by decide), r10,
      u2.other .r2 (by decide), e1, sel2]
  have R5 : Rest [.r2, .r3] s t5 := ((((u1.rest (by simp)).trans (u2.rest (by simp))).trans (u3.rest (by simp))).trans
    (u4.rest (by simp))).trans (u5.rest (by simp))
  have hkl : P.K - lselV P σ < 2 ^ 31 := by omega
  have v10 : t10.gpr .r2 = (if vB P σ then ((emOf P σ).getD j 1).setWidth 32 else ((amV P σ).getD j 0).setWidth 32)
      &&& (if P.K - lselV P σ ≤ j ∧ okB P σ = true then BitVec.allOnes 32 else 0) := by
    rw [u10.gpr, dpVal, u9.gpr, dpVal, u8.gpr, dpVal, u7.gpr, u6.gpr, dpVal, u9.other .r2 (by decide),
      u8.other .r2 (by decide), u7.other .r2 (by decide), u6.other .r2 (by decide), v5,
      u8.other .r11 (by decide), u7.other .r11 (by decide), u6.other .r11 (by decide), R5.gpr .r11 (by decide), r11,
      R5.gpr .r4 (by decide), r4, R5.gpr .r9 (by decide), r9, mask_ge (by omega) hkl]
  refine wp_strb (by decide) (a := State.addr P.out + BitVec.ofNat 64 j)
    (by rw [R10.gpr .r0 (by decide), r0, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_zero, hs.1.outA hjK])
    (by rw [R10.wr]; exact St.out_w hs (by omega)) fun t11 m11 => ?_
  refine wp_dp (op2_imm (by decide)) fun t12 u12 => ?_
  refine wp_dp (op2_imm (by decide)) fun t13 u13 => ?_
  refine wp_dp (op2_imm (by decide)) fun t14 u14 => ?_
  refine wp_subs (op2_imm (by decide)) fun t15 u15 hz => WP.block_nil ?_
  have R15 : Rest [.r0, .r1, .r2, .r3, .r4, .r5, .lr] s t15 := ((((((R10.mono (by simp)).trans (m11.rest _)).trans
    (u12.rest (by simp))).trans (u13.rest (by simp))).trans (u14.rest (by simp))).trans (u15.rest (by simp)))
  have bv : (t10.gpr .r2).setWidth 8 = obV P σ j := by rw [v10, selByte]; rfl
  have mm : t15.mem = s.mem.writeW (State.addr P.out + BitVec.ofNat 64 j) (obV P σ j) := by
    rw [u15.mem, u14.mem, u13.mem, u12.mem, m11.mem, m10, bv]
  have W1 : Region.Sub ⟨State.addr P.out + BitVec.ofNat 64 j, 1⟩ P.OUT := Offset.sub_base _ (by omega)
  have fr : Frame [⟨State.addr P.out + BitVec.ofNat 64 j, 1⟩] s.mem t15.mem := by
    rw [mm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) (obV P σ j) (Region.contains_self _ _)
  have st : P.lay.St σ t15 := hs.2.write fr (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨P.OUT, by simp, W1⟩) R15.rd R15.wr R15.sp
  have one : ∀ {R : Region}, R.Disjoint P.OUT → ∀ r ∈ [(⟨State.addr P.out + BitVec.ofNat 64 j, 1⟩ : Region)],
      R.Disjoint r := fun hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd.sub_right W1
  have r0t : t15.gpr .r0 = P.out + BitVec.ofNat 32 (j + 1) := by
    rw [u15.other _ (by decide), u14.other _ (by decide), u13.other _ (by decide), u12.gpr, dpVal, m11.gpr,
      R10.gpr .r0 (by decide), r0, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have r1t : t15.gpr .r1 = P.scr + BitVec.ofNat 32 (sAM + (j + 1)) := by
    rw [u15.other _ (by decide), u14.other _ (by decide), u13.gpr, dpVal, u12.other _ (by decide), m11.gpr,
      R10.gpr .r1 (by decide), r1, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_assoc]
  have r4t : t15.gpr .r4 = BitVec.ofNat 32 (j + 1) := by
    rw [u15.other _ (by decide), u14.gpr, dpVal, u13.other _ (by decide), u12.other _ (by decide), m11.gpr,
      R10.gpr .r4 (by decide), r4, BitVec.ofNat_add_ofNat]
  have lrt : t15.gpr .lr = BitVec.ofNat 32 n := by
    rw [u15.gpr, u14.other _ (by decide), u13.other _ (by decide), u12.other _ (by decide), m11.gpr,
      R10.gpr .lr (by decide), lr, show P.K - j = n + 1 by omega]
    exact sub_one_ofNat (by omega)
  have obt : ∀ i < P.K, t15.mem (State.addr P.out + BitVec.ofNat 64 i) =
      if i < j + 1 then obV P σ i else (emOf P σ).getD i 1 := by
    intro i hi
    rw [mm, WriteBytes.writeW8_apply]
    by_cases e : i = j
    · subst e; simp
    · simp only [Offset.add_ofNat_ne (State.addr P.out) (by omega) (by omega) e, ↓reduceIte]
      rw [ob i hi]
      simp only [show (i < j + 1) = (i < j) by apply propext; omega]
  have sl : SL P (j + 1) σ t15 :=
    ⟨⟨hs.1, st⟩, obt,
      (bytes_frame fr (R := sc P sAM P.K) (one (hs.1.sc_out (by simp only [sAM]; omega)))
        (by show P.K ≤ 2 ^ 64; omega)).trans am,
      by rw [slot_keep fr (one (hs.1.ok.stk_fr (R := P.OUT) (.inr (by simp))
        (by simp only [oR, frameBytes]; decide)))]; exact rc,
      (wordsAt_frame fr (one hs.1.out_ml.symm) (by decide)).trans ml,
      r0t, r1t, r4t, by rw [lrt, show P.K - (j + 1) = n by omega], by rw [R15.gpr .r9 (by decide), r9],
      by rw [R15.gpr .r10 (by decide), r10], by rw [R15.gpr .r11 (by decide), r11], hEM⟩
  refine ⟨?_, fun h0 => ?_, fun h0 => ⟨by omega, by rw [show P.K - n = j + 1 by omega]; exact sl⟩⟩
  · rw [eval_ne, hz, ← u15.gpr, lrt, ofNat_beq_zero (by omega)]
    by_cases h0 : n = 0 <;> simp [h0] <;> omega
  · rw [show P.K = j + 1 by omega]; exact sl

theorem selLoop_vp : VP (SL P 0) selLoop (SL P P.K) := by
  refine (VP.loop (I := SLM P) selBody_vp (P.K - 1)).mono (fun σ s h => ?_) fun _ _ h => h
  have hK := h.1.1.k64
  exact ⟨by omega, by rw [show P.K - (P.K - 1 + 1) = 0 by omega]; exact h⟩

/-! ## The result -/

/-- What the shared contract states of the result `r` and the memory `m`. -/
def Res (P : EP) (σ : State) (m : Mem) (r : BitVec 32) : Prop :=
  Spec.RsaPkcs1Enc.writtenMsg m (State.addr P.out) (State.addr P.ml) P.K r
    (Spec.RsaPkcs1Enc.decrypt P.nB P.eB (dB P σ) (pB P σ) (qB P σ) (dpB P σ) (dqB P σ) (qiB P σ) (cB P σ))

/-- The end of the body. -/
def Fin (P : EP) (σ s : State) : Prop := S P σ s ∧ Res P σ s.mem (s.gpr .r0)

theorem amV_length (P : EP) (σ : State) : (amV P σ).length = P.K := by
  rw [amV, VG.Proof.RsaPkcs1Enc.irprf_eq, List.length_take, flatMap_blocks_length]
  omega

theorem res_of {σ : State} {m : Mem} (hin : In P σ) (hEM : (emOf P σ).length = P.K)
    (hout : ∀ i < P.K, m (State.addr P.out + BitVec.ofNat 64 i) = obV P σ i)
    (hml : Spec.Rsa.wordsAt m (State.addr P.ml) 1 = [BitVec.ofNat 64 (if okB P σ then lselV P σ else 0)]) :
    Res P σ m (rcOf P σ) := by
  have hK := hin.k64
  have hn : P.nB.length = P.K := by rw [← hin.nB, bytesAt_length]
  have hC : (cB P σ).length = P.K := bytesAt_length _ _ _
  have hb : Spec.Rsa.bytesAt m (State.addr P.out) P.K = (List.range P.K).map (obV P σ) :=
    List.map_congr_left fun i hi => hout i (List.mem_range.mp hi)
  unfold Res Spec.RsaPkcs1Enc.decrypt
  rw [hn]
  cases ho : privO P σ with
  | ok EM =>
    have e1 : emOf P σ = EM := by simp only [emOf, ho]
    have r1 : rcOf P σ = 1 := by simp only [rcOf, ho]
    have ok1 : okB P σ = true := by simp only [okB, r1]; rfl
    have hEM' : EM.length = P.K := e1 ▸ hEM
    rw [VG.Proof.RsaPkcs1Enc.decryptWith_of_ok hC (by omega) ho]
    obtain ⟨hl, hm⟩ := VG.Proof.RsaPkcs1Enc.sel_eq (EM := EM) (AM := amV P σ) (al := alV P σ) hEM'
      (amV_length P σ) (by omega) (alV_le P σ)
    have hM : Spec.RsaPkcs1Enc.implicitDecode (dB P σ) (cB P σ) EM =
        (if Spec.RsaPkcs1Enc.valid EM then Spec.RsaPkcs1Enc.lastN (Spec.RsaPkcs1Enc.msgLength EM) EM
          else Spec.RsaPkcs1Enc.lastN (alV P σ) (amV P σ)) := by
      simp only [Spec.RsaPkcs1Enc.implicitDecode, Spec.RsaPkcs1Enc.alternative, hEM']
    rw [hM]
    refine ⟨r1, ?_, ?_⟩
    · rw [hb, ← hm]
      refine List.map_congr_left fun i _ => ?_
      simp only [obV, vB, lselV, sepV, fz, e1, ok1]
    · rw [hml, ok1, ← hl]
      simp only [lselV, vB, sepV, fz, e1, ↓reduceIte]
  | invalid =>
    have r0 : rcOf P σ = 0 := by simp only [rcOf, ho]
    have ok0 : okB P σ = false := by simp only [okB, r0]; rfl
    rw [VG.Proof.RsaPkcs1Enc.decryptWith_of_invalid (C := cB P σ)
      (rsadp := fun C => Spec.Rsa.privateChecked P.nB P.eB C (pB P σ) (qB P σ) (dpB P σ) (dqB P σ) (qiB P σ)) ho]
    refine ⟨r0, ?_, by rw [hml, ok0]; rfl⟩
    have z : ∀ i, obV P σ i = 0 := fun i => by
      simp only [obV, ok0]; exact VG.Proof.RsaPkcs1Enc.outByte_false _ _ _ _ _
    rw [hb, List.map_congr_left (g := fun _ => (0 : Byte)) fun i _ => z i]
    simp
  | fault =>
    have r2 : rcOf P σ = 2 := by simp only [rcOf, ho]
    have ok0 : okB P σ = false := by simp only [okB, r2]; rfl
    rw [VG.Proof.RsaPkcs1Enc.decryptWith_of_fault hC (by omega) ho]
    refine ⟨r2, ?_, by rw [hml, ok0]; rfl⟩
    have z : ∀ i, obV P σ i = 0 := fun i => by
      simp only [obV, ok0]; exact VG.Proof.RsaPkcs1Enc.outByte_false _ _ _ _ _
    rw [hb, List.map_congr_left (g := fun _ => (0 : Byte)) fun i _ => z i]
    simp

theorem fin_wp {σ s : State} (h : SL P P.K σ s) : WP isa (.block fin) s (Fin P σ) := by
  obtain ⟨hs, ob, -, rc, ml, -, -, -, -, -, -, -, hEM⟩ := h
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  refine s1.wp_slot (d := oR) (by show oR + 4 ≤ frameBytes; decide) (by decide) fun t2 s2 u2 => WP.block_nil ?_
  have mm : t2.mem = s.mem := by rw [u2.mem, u1.mem]
  refine ⟨⟨hs.1, s2⟩, ?_⟩
  rw [u2.gpr, u1.mem, rc, mm]
  exact res_of hs.1 hEM (fun i hi => by rw [ob i hi]; simp [hi]) ml

end VG.Proof.RsaPkcs1Enc.Arm.Dec
