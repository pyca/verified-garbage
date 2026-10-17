module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecPrfLoop
import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecTaint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# RSAES-PKCS1-v1_5 decryption on ARMv7: `CL` and `AM`

The two IRPRF loops (`Prf`): `CL = IRPRF(KDK, "length", 256)` at
`scratch + sCL` (`clLoop_vp`), keeping `KDK`, and
`AM = IRPRF(KDK, "message", k)` at `scratch + sAM` (`amLoop_vp`), keeping
`CL` (`IR`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.Arm.Dec

open VG VG.Arm VG.Impl.RsaPkcs1Enc.Arm.Decrypt VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_dp op2_imm op2_reg op2_lsr dpVal)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.RsaPkcs1Enc (prfBlock)

variable {P : EP}

theorem ascii_length : Spec.RsaPkcs1Enc.ascii "length" = lengthLabel.map (BitVec.ofNat 8) := by decide

theorem ascii_message : Spec.RsaPkcs1Enc.ascii "message" = messageLabel.map (BitVec.ofNat 8) := by decide

/-- `CL`. -/
abbrev clV (P : EP) (σ : State) : List Byte :=
  Spec.RsaPkcs1Enc.irprf (kdkV P σ) (Spec.RsaPkcs1Enc.ascii "length") 256

/-- `AM`. -/
abbrev amV (P : EP) (σ : State) : List Byte :=
  Spec.RsaPkcs1Enc.irprf (kdkV P σ) (Spec.RsaPkcs1Enc.ascii "message") P.K

/-- The loop of `CL`, keeping `KDK`. -/
def RCL (P : EP) : Prf P where
  vs := lengthLabel
  len := clLen
  L := 256
  dst := sCL
  nb := 8
  xo := sKDK
  xn := 32
  xv := kdkV P
  vs_lt := by decide
  vs_len := by decide
  nb1 := by decide
  nb_le := by decide
  dst_lo := by decide
  dst_hi := by decide
  dst_enc := by decide
  x_lo := by decide
  x_hi := by decide
  x_sep := .inl (by decide)
  lenOk := @fun _ _ _ _ _ r0 _ h _ k => clLen_wp rfl r0 h k

/-- `CL`'s blocks. -/
abbrev clBlocks (P : EP) (σ : State) : List Byte :=
  (List.range 8).flatMap (prfBlock (kdkV P σ) (lengthLabel.map (BitVec.ofNat 8)) 256)

/-- The loop of `AM`, keeping `CL`, for `64 ≤ k ≤ 1024`. -/
def RAM (P : EP) (hK : 64 ≤ P.K ∧ P.K ≤ 1024) : Prf P where
  vs := messageLabel
  len := amLen
  L := P.K
  dst := sAM
  nb := (P.K + 31) / 32
  xo := sCL
  xn := 256
  xv := clBlocks P
  vs_lt := by decide
  vs_len := by decide
  nb1 := by omega
  nb_le := by omega
  dst_lo := by decide
  dst_hi := by simp only [sAM]; omega
  dst_enc := by decide
  x_lo := by decide
  x_hi := by decide
  x_sep := .inl (by decide)
  lenOk := @fun _ _ _ _ _ r0 r3 h _ k => amLen_wp rfl hK.2 r0 r3 h k

theorem clInit_wp {σ s : State} (h : K6 P σ s) : WP isa (.block clInit) s (B0 P (RCL P) 0 σ) := by
  obtain ⟨hb, kd⟩ := h
  have hs := hb.1
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  have r12 : t1.gpr .r12 = P.B := by rw [u1.gpr, hs.2.sp, BitVec.add_zero]
  refine wp_mov (op2_imm (by decide)) fun t2 u2 => ?_
  have s2 : P.lay.St σ t2 := s1.of_rest (u2.rest (ws := [.r0]) (by simp)) u2.mem
  refine s2.wp_strFr (d := oI) (by show oI + 4 ≤ frameBytes; decide) (by decide)
    (by rw [u2.other _ (by decide), r12]) fun t3 s3 m3 => ?_
  refine wp_mov (op2_imm (by decide)) fun t4 u4 => ?_
  have s4 : P.lay.St σ t4 := s3.of_rest (u4.rest (ws := [.r0]) (by simp)) u4.mem
  refine s4.wp_strFr (d := oNB) (by show oNB + 4 ≤ frameBytes; decide) (by decide)
    (by rw [u4.other _ (by decide), m3.gpr, u2.other _ (by decide), r12]) fun t5 s5 m5 => WP.block_nil ?_
  have mm : t5.mem = (s.mem.writeW (P.lay.fr oI) (BitVec.ofNat 32 0)).writeW (P.lay.fr oNB) (BitVec.ofNat 32 8) := by
    rw [m5.mem, u4.gpr, u4.mem, m3.mem, u2.gpr, u2.mem, u1.mem]
  have fr : Frame [⟨P.lay.fr oI, 4⟩, ⟨P.lay.fr oNB, 4⟩] s.mem t5.mem := by
    rw [mm]
    exact ((Frame.refl _ _).writeW List.mem_cons_self (BitVec.ofNat 32 0) (Region.contains_self _ _)).writeW
      (List.mem_cons_of_mem _ List.mem_cons_self) (BitVec.ofNat 32 8) (Region.contains_self _ _)
  have sd : ∀ r ∈ [(⟨P.lay.fr oI, 4⟩ : Region), ⟨P.lay.fr oNB, 4⟩], Safe P r ∧ (sc P sKDK 32).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨hs.1.safe_fr (by decide) (by simp only [oR, oI]; decide),
        (hs.1.fr_sc (by simp only [oI, frameBytes]; decide) (by decide)).symm⟩
    · exact ⟨hs.1.safe_fr (by decide) (by simp only [oR, oNB]; decide),
        (hs.1.fr_sc (by simp only [oNB, frameBytes]; decide) (by decide)).symm⟩
  have kd' : Spec.Rsa.bytesAt t5.mem (sc P sKDK 32).base 32 = kdkV P σ :=
    (bytes_frame fr (R := sc P sKDK 32) (fun r hr => (sd r hr).2) (by show 32 ≤ 2 ^ 64; decide)).trans kd
  refine ⟨⟨Nat.zero_le _, hb.frame s5 fr fun r hr => (sd r hr).1, kd', kd', ?_, by simp [Spec.Rsa.bytesAt]⟩, ?_⟩
  · rw [mm, Mem.readW_writeW_self32]; rfl
  · rw [mm, Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]

theorem nb_val {K : Nat} (hK : K ≤ 1024) :
    (BitVec.ofNat 32 K + BitVec.ofNat 32 31) >>> 5 = BitVec.ofNat 32 ((K + 31) / 32) := by
  rw [BitVec.ofNat_add_ofNat]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

theorem amInit_wp {σ s : State} (hK : 64 ≤ P.K ∧ P.K ≤ 1024) (h : CI P (RCL P) 8 σ s) :
    WP isa (.block amInit) s (B0 P (RAM P hK) 0 σ) := by
  have hs := h.S
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  have r12 : t1.gpr .r12 = P.B := by rw [u1.gpr, hs.2.sp, BitVec.add_zero]
  refine wp_mov (op2_imm (by decide)) fun t2 u2 => ?_
  have s2 : P.lay.St σ t2 := s1.of_rest (u2.rest (ws := [.r0]) (by simp)) u2.mem
  refine s2.wp_strFr (d := oI) (by show oI + 4 ≤ frameBytes; decide) (by decide)
    (by rw [u2.other _ (by decide), r12]) fun t3 s3 m3 => ?_
  refine s3.wp_arg (j := 4) (by simp) (by dsimp only; decide) fun t4 s4 u4 => ?_
  refine wp_dp (op2_imm (by decide)) fun t5 u5 => ?_
  refine wp_mov (op2_lsr (by decide)) fun t6 u6 => ?_
  have s6 : P.lay.St σ t6 := (s4.of_rest (u5.rest (ws := [.r0]) (by simp)) u5.mem).of_rest
    (u6.rest (ws := [.r0]) (by simp)) u6.mem
  refine s6.wp_strFr (d := oNB) (by show oNB + 4 ≤ frameBytes; decide) (by decide)
    (by rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), m3.gpr,
      u2.other _ (by decide), r12]) fun t7 s7 m7 => WP.block_nil ?_
  have r0v : t6.gpr .r0 = BitVec.ofNat 32 ((P.K + 31) / 32) := by
    rw [u6.gpr, u5.gpr, dpVal, u4.gpr]; exact nb_val hK.2
  have mm : t7.mem = (s.mem.writeW (P.lay.fr oI) (BitVec.ofNat 32 0)).writeW (P.lay.fr oNB)
      (BitVec.ofNat 32 ((P.K + 31) / 32)) := by
    rw [m7.mem, r0v, u6.mem, u5.mem, u4.mem, m3.mem, u2.gpr, u2.mem, u1.mem]
  have fr : Frame [⟨P.lay.fr oI, 4⟩, ⟨P.lay.fr oNB, 4⟩] s.mem t7.mem := by
    rw [mm]
    exact ((Frame.refl _ _).writeW List.mem_cons_self (BitVec.ofNat 32 0) (Region.contains_self _ _)).writeW
      (List.mem_cons_of_mem _ List.mem_cons_self) (BitVec.ofNat 32 ((P.K + 31) / 32)) (Region.contains_self _ _)
  have sd : ∀ r ∈ [(⟨P.lay.fr oI, 4⟩ : Region), ⟨P.lay.fr oNB, 4⟩],
      Safe P r ∧ (sc P sKDK 32).Disjoint r ∧ (sc P sCL 256).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨hs.1.safe_fr (by decide) (by simp only [oR, oI]; decide),
        (hs.1.fr_sc (by simp only [oI, frameBytes]; decide) (by decide)).symm,
        (hs.1.fr_sc (by simp only [oI, frameBytes]; decide) (by decide)).symm⟩
    · exact ⟨hs.1.safe_fr (by decide) (by simp only [oR, oNB]; decide),
        (hs.1.fr_sc (by simp only [oNB, frameBytes]; decide) (by decide)).symm,
        (hs.1.fr_sc (by simp only [oNB, frameBytes]; decide) (by decide)).symm⟩
  refine ⟨⟨Nat.zero_le _, h.base.frame s7 fr fun r hr => (sd r hr).1,
    (bytes_frame fr (R := sc P sKDK 32) (fun r hr => (sd r hr).2.1) (by show 32 ≤ 2 ^ 64; decide)).trans h.kdk,
    (bytes_frame fr (R := sc P sCL 256) (fun r hr => (sd r hr).2.2) (by show 256 ≤ 2 ^ 64; decide)).trans h.blk,
    ?_, by simp [Spec.Rsa.bytesAt]⟩, ?_⟩
  · rw [mm, Mem.readW_writeW_self32]; rfl
  · rw [mm, Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]

/-! ## The loops -/

/-- `CL` and `AM` in `scratch`. -/
def IR (P : EP) (σ s : State) : Prop :=
  Base P σ s ∧ Spec.Rsa.bytesAt s.mem (sc P sCL 256).base 256 = clV P σ ∧
    Spec.Rsa.bytesAt s.mem (sc P sAM P.K).base P.K = amV P σ

theorem flatMap_blocks_length (kd lab : List Byte) (L : Nat) :
    ∀ n, ((List.range n).flatMap (prfBlock kd lab L)).length = 32 * n
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, List.length_append, flatMap_blocks_length kd lab L n,
      List.flatMap_singleton, prfBlock, hmac_len]
    omega

theorem bytesAt_take (m : Mem) (p : Addr) {k n : Nat} (h : k ≤ n) :
    Spec.Rsa.bytesAt m p k = (Spec.Rsa.bytesAt m p n).take k := by
  simp only [Spec.Rsa.bytesAt, ← List.map_take, List.take_range, Nat.min_eq_left h]

theorem clV_eq (P : EP) (σ : State) : clV P σ = clBlocks P σ := by
  rw [clV, Proof.RsaPkcs1Enc.irprf_eq, ascii_length]
  exact List.take_of_length_le (by rw [flatMap_blocks_length])

theorem ir_of {σ s : State} {hK : 64 ≤ P.K ∧ P.K ≤ 1024} (h : CI P (RAM P hK) ((P.K + 31) / 32) σ s) :
    IR P σ s := by
  refine ⟨h.base, by rw [clV_eq]; exact h.x, ?_⟩
  have hb := h.blk
  simp only [RAM] at hb
  rw [amV, Proof.RsaPkcs1Enc.irprf_eq, ascii_message, ← hb, ← bytesAt_take _ _ (by omega)]

theorem clLoop_vp : VP (K6 P) (clLoop decFns) (CI P (RCL P) 8) :=
  (VP.stk (code := [_, _, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.1 h₂.1.1)
    fun _ _ h => clInit_wp h).seq (loop_vp (R := RCL P) msgCL_taint)

theorem amLoop_vp : VP (CI P (RCL P) 8) (amLoop decFns) (IR P) := by
  by_cases hK : 64 ≤ P.K ∧ P.K ≤ 1024
  · exact (VP.stk (code := [_, _, _, _, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.S h₂.S)
      fun _ _ h => amInit_wp hK h).seq ((loop_vp (R := RAM P hK) msgAM_taint).mono (fun _ _ h => h)
        fun _ _ h => ir_of h)
  · exact VP.of_false fun _ _ h => hK ⟨h.S.1.k64, h.S.1.k1024⟩

end VG.Proof.RsaPkcs1Enc.Arm.Dec
