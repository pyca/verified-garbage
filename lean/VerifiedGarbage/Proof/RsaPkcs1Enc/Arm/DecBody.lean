module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecPrf
import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecPrfLoop
import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecTaint
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Vp
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import Mathlib.Data.Nat.Basic
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Select
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Encode
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import Mathlib.Order.Basic
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPkcs1Enc.Decrypt
import Mathlib.Data.List.Basic
import VerifiedGarbage.Proof.Bignum.Arm.MaskBytesCT
import VerifiedGarbage.Proof.Bignum.Arm.CopyBytesCT

/-! ### `RsaPkcs1Enc.Arm.DecSel`, which only this module used -/

section

/-! ### `RsaPkcs1Enc.Arm.DecValid`, which only this module used -/

section

/-! ### `RsaPkcs1Enc.Arm.DecScan`, which only this module used -/

section

/-! ### `RsaPkcs1Enc.Arm.DecAl`, which only this module used -/

section

/-! ### `RsaPkcs1Enc.Arm.DecIrprf`, which only this module used -/

section

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
  nb1 := by omega_using [hK]
  nb_le := by omega_using [hK]
  dst_lo := by decide
  dst_hi := by simp only [sAM]; omega_using [hK]
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
  omega_using [hK]

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
    omega_using []

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
  rw [amV, Proof.RsaPkcs1Enc.irprf_eq, ascii_message, ← hb, ← bytesAt_take _ _ (by omega_using [])]

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

end

end


/-!
# RSAES-PKCS1-v1_5 decryption on ARMv7: the alternative length

The mask of the candidates, `2^bitLength(k - 11) - 1`, by doublings
(`maskLoop_vp`), and `AL`, the last candidate not above `k - 11`, a fold over
the 128 candidates of `CL` (`alLoop_vp`), to its slot (`alPart_vp`, `AL`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.Arm.Dec

open VG VG.Arm VG.Impl.RsaPkcs1Enc.Arm.Decrypt VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_dp wp_cmp wp_subs wp_ldrb op2_imm op2_reg op2_lsl op2_lsr
  dpVal eval_ne)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.RsaPkcs1Enc (bitMask altStep)
open VG.Spec.RsaPkcs1Enc (bitLength)

variable {P : EP}

/-! ## Memory kept -/

theorem IR.of_mem {σ s t : State} (h : IR P σ s) (st : P.lay.St σ t) (hm : t.mem = s.mem) : IR P σ t :=
  ⟨h.1.frame st (rs := []) (by rw [hm]; exact Frame.refl _ _) fun _ h => absurd h List.not_mem_nil,
    by rw [hm]; exact h.2.1, by rw [hm]; exact h.2.2⟩

theorem IR.keep_fr {σ s t : State} (h : IR P σ s) (st : P.lay.St σ t) {d : Nat} {v : BitVec 32}
    (hm : t.mem = s.mem.writeW (P.lay.fr d) v) (hd : d + 4 ≤ frameBytes) (ho : d + 4 ≤ oR ∨ oR + 4 ≤ d) :
    IR P σ t := by
  have hs := h.1.1
  have hK := hs.1.k1024
  have fr : Frame [⟨P.lay.fr d, 4⟩] s.mem t.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) v (Region.contains_self _ _)
  have hd' : d + 4 ≤ frameBytes + 56 := by simp only [frameBytes] at hd ⊢; omega_arith
  refine ⟨h.1.frame st fr fun r hr => ?_, ?_, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact hs.1.safe_fr hd ho
  · rw [sc_keep_fr hs.1 hd (by decide) fr]; exact h.2.1
  · rw [sc_keep_fr hs.1 hd (by simp only [sAM]; omega_arith) fr]; exact h.2.2

/-! ## The mask -/

/-- The mask `2^j - 1`, and `k - 11`. -/
def MI (P : EP) (j : Nat) (σ s : State) : Prop :=
  IR P σ s ∧ s.gpr .r0 = BitVec.ofNat 32 (2 ^ j - 1) ∧ s.gpr .r1 = BitVec.ofNat 32 (P.K - 11)

/-- The mask. -/
def MK (P : EP) (σ s : State) : Prop := IR P σ s ∧ s.gpr .r0 = BitVec.ofNat 32 (bitMask (P.K - 11))

theorem maskInit_wp {σ s : State} (h : IR P σ s) : WP isa (.block maskInit) s (MI P 0 σ) := by
  have hs := h.1.1
  have hK := hs.1.k64
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  refine s1.wp_arg (j := 4) (by simp) (by dsimp only; decide) fun t2 s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun t3 u3 => ?_
  refine wp_mov (op2_imm (by decide)) fun t4 u4 => WP.block_nil ?_
  have s4 : P.lay.St σ t4 := (s2.of_rest (u3.rest (ws := [.r1]) (by simp)) u3.mem).of_rest
    (u4.rest (ws := [.r0]) (by simp)) u4.mem
  refine ⟨h.of_mem s4 (by rw [u4.mem, u3.mem, u2.mem, u1.mem]), u4.gpr, ?_⟩
  rw [u4.other _ (by decide), u3.gpr, dpVal, u2.gpr]
  exact Offset.ofNat_sub_ofNat (d := 11) (by omega_arith)

/-- The loop's stage, `m` doublings left. -/
def MLI (P : EP) (m : Nat) (σ s : State) : Prop := m ≤ bitLength (P.K - 11) ∧ MI P (bitLength (P.K - 11) - m) σ s

theorem bitLength_le {x : Nat} (hx : x ≠ 0) (hx' : x < 2 ^ 30) : 2 ^ bitLength x - 1 < 2 ^ 31 := by
  have := VG.Proof.RsaPkcs1Enc.bitMask_le hx
  simp only [bitMask] at this
  omega_arith

theorem maskBody_vp (n : Nat) : VP (MLI P (n + 1)) (.block maskBody) fun σ s =>
    isa.eval .ne s = some (decide (0 < n)) ∧ (n = 0 → MK P σ s) ∧ (0 < n → MLI P n σ s) := by
  refine VP.taint [.r0, .r1] maskBody_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s h => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2, h₂.2.2.2]
  obtain ⟨hn, hir, r0, r1⟩ := h
  have hs := hir.1.1
  have hK := hs.1.k64
  have hK' := hs.1.k1024
  have hx : P.K - 11 ≠ 0 := by omega_arith
  generalize hB : bitLength (P.K - 11) = B at hn r0
  have hj : B - (n + 1) < bitLength (P.K - 11) := by omega_arith
  have hlt := VG.Proof.RsaPkcs1Enc.bitMask_lt hx hj
  have hst := VG.Proof.RsaPkcs1Enc.bitMask_step (by omega_arith : 1 ≤ P.K - 11) hlt
  have hp : 2 ^ (B - (n + 1) + 1) - 1 ≤ 2 ^ B - 1 :=
    Nat.sub_le_sub_right (Nat.pow_le_pow_right (by decide) (by omega_arith)) _
  have hB31 : 2 ^ B - 1 < 2 ^ 31 := by rw [← hB]; exact bitLength_le hx (by omega_arith)
  refine wp_dp (op2_reg _ _) fun t1 u1 => ?_
  refine wp_dp (op2_imm (by decide)) fun t2 u2 => ?_
  refine wp_dp (op2_reg _ _) fun t3 u3 => ?_
  refine wp_mov (op2_lsr (by decide)) fun t4 u4 => ?_
  refine wp_cmp (op2_imm (by decide)) fun t5 u5 hz => WP.block_nil ?_
  have r0v : t2.gpr .r0 = BitVec.ofNat 32 (2 ^ (B - (n + 1) + 1) - 1) := by
    rw [u2.gpr, dpVal, u1.gpr, dpVal, r0, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat, ← hst.1]
    congr 1; omega_arith
  have r2v : t4.gpr .r2 = if 2 ^ (B - (n + 1) + 1) - 1 < P.K - 11 then 1 else 0 := by
    rw [u4.gpr, u3.gpr, dpVal, r0v, u2.other _ (by decide), u1.other _ (by decide), r1]
    exact top_sub (by omega_arith) (by omega_arith)
  have st : P.lay.St σ t5 := hs.2.of_rest ((((u1.rest (ws := [.r0, .r2]) (by simp)).trans
    (u2.rest (by simp))).trans (u3.rest (by simp))).trans (u4.rest (by simp)) |>.trans (u5.rest _))
    (by rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem])
  have ir := hir.of_mem st (by rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem])
  have r0t : t5.gpr .r0 = BitVec.ofNat 32 (2 ^ (B - (n + 1) + 1) - 1) := by
    rw [u5.gpr, u4.other _ (by decide), u3.other _ (by decide), r0v]
  have r1t : t5.gpr .r1 = BitVec.ofNat 32 (P.K - 11) := by
    rw [u5.gpr, u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), r1]
  have e : (2 ^ (B - (n + 1) + 1) - 1 < P.K - 11) = (0 < n) := by
    apply propext; constructor
    · intro h; by_contra h0
      have := VG.Proof.RsaPkcs1Enc.bitMask_ge hx
      rw [hB] at this
      rw [show B - (n + 1) + 1 = B by omega_arith] at h
      omega_arith
    · intro h0
      exact VG.Proof.RsaPkcs1Enc.bitMask_lt hx (by omega_arith)
  refine ⟨?_, fun h0 => ⟨ir, ?_⟩, fun h0 => ⟨by omega_arith, ir, ?_, r1t⟩⟩
  · rw [eval_ne, hz, r2v]
    by_cases h0 : 0 < n
    · have hc : 2 ^ (B - (n + 1) + 1) - 1 < P.K - 11 := e ▸ h0
      simp [hc, h0]
    · have hc : ¬ 2 ^ (B - (n + 1) + 1) - 1 < P.K - 11 := fun h => h0 (e ▸ h)
      simp [hc, h0]
  · rw [r0t, show B - (n + 1) + 1 = B by omega_arith, ← hB]; rfl
  · rw [r0t, show B - (n + 1) + 1 = B - n by omega_arith, hB]

theorem maskLoop_vp : VP (MI P 0) maskLoop (MK P) := by
  refine (VP.loop (I := MLI P) maskBody_vp (bitLength (P.K - 11) - 1)).mono (fun σ s h => ?_) fun _ _ h => h
  have hK := h.1.1.1.1.k64
  have : 1 ≤ bitLength (P.K - 11) := by
    simp only [bitLength, show P.K - 11 ≠ 0 by omega_arith, ↓reduceIte]; omega_arith
  refine ⟨by omega_arith, ?_⟩
  rw [show bitLength (P.K - 11) - (bitLength (P.K - 11) - 1 + 1) = 0 by omega_arith]; exact h

/-! ## The candidates -/

/-- Byte `i` of `CL`. -/
theorem cl_byte {σ s : State} (h : IR P σ s) {i : Nat} (hi : i < 256) :
    s.mem (State.addr P.scr + BitVec.ofNat 64 (sCL + i)) = (clV P σ).getD i 0 := by
  rw [← h.2.1, bytesAt_getD hi, Offset.add_add]

theorem altStep_and (K : Nat) (CL : List Byte) (al i : Nat) :
    altStep K CL al i =
      (let c := (256 * (CL.getD (2 * i) 0).toNat + (CL.getD (2 * i + 1) 0).toNat) &&& bitMask (K - 11);
        if c ≤ K - 11 then c else al) := by
  simp only [altStep, VG.Proof.RsaPkcs1Enc.cand_eq, bitMask, Nat.and_two_pow_sub_one_eq_mod]

theorem cand_bv (b0 b1 : Byte) :
    b1.setWidth 32 + b0.setWidth 32 <<< 8 = BitVec.ofNat 32 (256 * b0.toNat + b1.toNat) := by
  have := b0.isLt; have := b1.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq]
  omega_arith

theorem sel_bv (a c : BitVec 32) (p : Prop) [Decidable p] :
    a ^^^ ((a ^^^ c) &&& ((if p then 1 else 0) - 1)) = if p then a else c := by
  by_cases h : p
  · simp [h]
  · simp only [h, ↓reduceIte]
    rw [show (0 : BitVec 32) - 1 = BitVec.allOnes 32 by decide, BitVec.and_allOnes, ← BitVec.xor_assoc,
      BitVec.xor_self, BitVec.zero_xor]

theorem ofNat_beq_zero {n : Nat} (hn : n < 2 ^ 32) : (BitVec.ofNat 32 n == 0) = decide (n = 0) := by
  by_cases h : n = 0
  · subst h; rfl
  · have : BitVec.ofNat 32 n ≠ 0 := by
      intro e
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at this
      exact h this
    rw [beq_eq_false_iff_ne.mpr this, decide_eq_false h]

/-- The fold of the first `j` candidates. -/
abbrev alFold (P : EP) (σ : State) (j : Nat) : Nat := (List.range j).foldl (altStep P.K (clV P σ)) 0

/-- Before candidate `j`. -/
def ALI (P : EP) (j : Nat) (σ s : State) : Prop :=
  IR P σ s ∧ s.gpr .r0 = P.scr + BitVec.ofNat 32 (sCL + 2 * j) ∧
    s.gpr .r4 = BitVec.ofNat 32 (bitMask (P.K - 11)) ∧ s.gpr .r5 = BitVec.ofNat 32 (P.K - 11) ∧
    s.gpr .r6 = BitVec.ofNat 32 (alFold P σ j) ∧ s.gpr .lr = BitVec.ofNat 32 (128 - j)

/-- `AL` in `r6`. -/
def ALQ (P : EP) (σ s : State) : Prop :=
  IR P σ s ∧ s.gpr .r6 = BitVec.ofNat 32 (Spec.RsaPkcs1Enc.altLength P.K (clV P σ))

/-- `AL` in its slot. -/
def AL (P : EP) (σ s : State) : Prop :=
  IR P σ s ∧ s.mem.readW (P.lay.fr oAL) 32 = BitVec.ofNat 32 (Spec.RsaPkcs1Enc.altLength P.K (clV P σ))

theorem alInit_wp {σ s : State} (h : MK P σ s) : WP isa (.block alInit) s (ALI P 0 σ) := by
  obtain ⟨hir, r0⟩ := h
  have hs := hir.1.1
  have hK := hs.1.k64
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  have r12 : t1.gpr .r12 = P.B := by rw [u1.gpr, hs.2.sp, BitVec.add_zero]
  refine s1.wp_strFr (d := oMK) (by show oMK + 4 ≤ frameBytes; decide) (by decide) r12 fun t2 s2 m2 => ?_
  refine s2.wp_arg (j := 21) (by simp) (by dsimp only; decide) fun t3 s3 u3 => ?_
  refine wp_dp (op2_imm (by decide)) fun t4 u4 => ?_
  have s4 : P.lay.St σ t4 := s3.of_rest (u4.rest (ws := [.r0]) (by simp)) u4.mem
  refine s4.wp_slot (d := oMK) (by show oMK + 4 ≤ frameBytes; decide) (by decide) fun t5 s5 u5 => ?_
  refine s5.wp_arg (j := 4) (by simp) (by dsimp only; decide) fun t6 s6 u6 => ?_
  refine wp_dp (op2_imm (by decide)) fun t7 u7 => ?_
  refine wp_mov (op2_imm (by decide)) fun t8 u8 => ?_
  refine wp_mov (op2_imm (by decide)) fun t9 u9 => WP.block_nil ?_
  have s9 : P.lay.St σ t9 := ((s6.of_rest (u7.rest (ws := [.r5]) (by simp)) u7.mem).of_rest
    (u8.rest (ws := [.r6]) (by simp)) u8.mem).of_rest (u9.rest (ws := [.lr]) (by simp)) u9.mem
  have mm : t9.mem = s.mem.writeW (P.lay.fr oMK) (s.gpr .r0) := by
    rw [u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, m2.mem, u1.mem, u1.other _ (by decide)]
  refine ⟨hir.keep_fr s9 mm (by decide) (by simp only [oR, oMK]; decide), ?_, ?_, ?_, ?_, ?_⟩
  · rw [u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide),
      u5.other _ (by decide), u4.gpr, dpVal, u3.gpr]; rfl
  · rw [u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide), u5.gpr,
      u4.mem, u3.mem, m2.mem, Mem.readW_writeW_self32, u1.other _ (by decide), r0]
  · rw [u9.other _ (by decide), u8.other _ (by decide), u7.gpr, dpVal, u6.gpr]
    exact Offset.ofNat_sub_ofNat (d := 11) (by omega_arith)
  · rw [u9.other _ (by decide), u8.gpr]; rfl
  · rw [u9.gpr]

/-- `m` candidates left. -/
def ALM (P : EP) (m : Nat) (σ s : State) : Prop := m ≤ 128 ∧ ALI P (128 - m) σ s

theorem alBody_vp (n : Nat) : VP (ALM P (n + 1)) (.block alBody) fun σ s =>
    isa.eval .ne s = some (decide (0 < n)) ∧ (n = 0 → ALQ P σ s) ∧ (0 < n → ALM P n σ s) := by
  refine VP.taint [.r0, .r4, .r5, .lr] alBody_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s h => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2.1, h₂.2.2.2.1]
    · rw [h₁.2.2.2.2.1, h₂.2.2.2.2.1]
    · rw [h₁.2.2.2.2.2.2, h₂.2.2.2.2.2.2]
  obtain ⟨hn, hir, r0, r4, r5, r6, lr⟩ := h
  generalize hj : 128 - (n + 1) = j at r0 r6 lr
  have hjn : j + n + 1 = 128 := by omega_arith
  have hs := hir.1.1
  have hK := hs.1.k64
  have hK' := hs.1.k1024
  have hx : P.K - 11 ≠ 0 := by omega_arith
  have hm := VG.Proof.RsaPkcs1Enc.bitMask_le hx
  have ha : ∀ d < 2, State.addr (s.gpr .r0 + BitVec.ofNat 32 d) =
      State.addr P.scr + BitVec.ofNat 64 (sCL + (2 * j + d)) := by
    intro d hd
    rw [r0, BitVec.add_assoc, BitVec.ofNat_add_ofNat, hs.1.scrA (by simp only [sCL]; omega_arith), Nat.add_assoc]
  have e0 := cl_byte hir (i := 2 * j + 0) (by omega_arith)
  have e1 := cl_byte hir (i := 2 * j + 1) (by omega_arith)
  refine wp_ldrb (by decide) (ha 0 (by decide)) (St.sc_r hs (by simp only [sCL]; omega_arith)) fun t1 u1 => ?_
  refine wp_ldrb (by decide) (a := State.addr P.scr + BitVec.ofNat 64 (sCL + (2 * j + 1)))
    (by rw [u1.other _ (by decide)]; exact ha 1 (by decide))
    (by rw [u1.rd, u1.wr]; exact St.sc_r hs (by simp only [sCL]; omega_arith)) fun t2 u2 => ?_
  refine wp_dp (op2_lsl (by decide)) fun t3 u3 => ?_
  refine wp_dp (op2_reg _ _) fun t4 u4 => ?_
  refine wp_dp (op2_reg _ _) fun t5 u5 => ?_
  refine wp_mov (op2_lsr (by decide)) fun t6 u6 => ?_
  refine wp_dp (op2_imm (by decide)) fun t7 u7 => ?_
  refine wp_dp (op2_reg _ _) fun t8 u8 => ?_
  refine wp_dp (op2_reg _ _) fun t9 u9 => ?_
  refine wp_dp (op2_reg _ _) fun t10 u10 => ?_
  refine wp_dp (op2_imm (by decide)) fun t11 u11 => ?_
  refine wp_subs (op2_imm (by decide)) fun t12 u12 hz => WP.block_nil ?_
  have R7 : Rest [.r2, .r3] s t7 := ((((((u1.rest (by simp)).trans (u2.rest (by simp))).trans (u3.rest (by simp))).trans
    (u4.rest (by simp))).trans (u5.rest (by simp))).trans (u6.rest (by simp))).trans (u7.rest (by simp))
  have R10 : Rest [.r2, .r3, .r6, .r7] s t10 := (((R7.mono (by simp)).trans (u8.rest (by simp))).trans
    (u9.rest (by simp))).trans (u10.rest (by simp))
  have R12 : Rest [.r0, .r2, .r3, .r6, .r7, .lr] s t12 := ((R10.mono (by simp)).trans (u11.rest (by simp))).trans
    (u12.rest (by simp))
  have mm : t12.mem = s.mem := by
    rw [u12.mem, u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have st : P.lay.St σ t12 := hs.2.of_rest R12 mm
  generalize hb0 : (clV P σ).getD (2 * j) 0 = b0 at e0
  generalize hb1 : (clV P σ).getD (2 * j + 1) 0 = b1 at e1
  generalize hc : (256 * b0.toNat + b1.toNat) &&& bitMask (P.K - 11) = c
  have hcm : c ≤ bitMask (P.K - 11) := hc ▸ Nat.and_le_right
  have c3 : t3.gpr .r2 = BitVec.ofNat 32 (256 * b0.toNat + b1.toNat) := by
    rw [u3.gpr, dpVal, u2.gpr, u2.other _ (by decide), u1.gpr, u1.mem, ← e0, ← e1]
    exact cand_bv _ _
  have c4 : t4.gpr .r2 = BitVec.ofNat 32 c := by
    rw [u4.gpr, dpVal, c3, u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), r4, ← hc,
      BitVec.ofNat_and]
  have c6 : t6.gpr .r3 = if P.K - 11 < c then 1 else 0 := by
    rw [u6.gpr, u5.gpr, dpVal, c4, u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide),
      u1.other _ (by decide), r5]
    exact top_sub (by omega_arith) (by omega_arith)
  have c10 : t10.gpr .r6 = if P.K - 11 < c then BitVec.ofNat 32 (alFold P σ j) else BitVec.ofNat 32 c := by
    rw [u10.gpr, dpVal, u9.other _ (by decide), u8.other _ (by decide), R7.gpr _ (by decide), r6, u9.gpr, dpVal,
      u8.gpr, dpVal, R7.gpr _ (by decide), r6, u8.other _ (by decide), u7.other _ (by decide),
      u6.other _ (by decide), u5.other _ (by decide), c4, u7.gpr, dpVal, c6]
    exact sel_bv _ _ _
  have fold : alFold P σ (j + 1) = if P.K - 11 < c then alFold P σ j else c := by
    rw [alFold, VG.Proof.RsaPkcs1Enc.foldl_range_succ, altStep_and]
    simp only [hb0, hb1, hc]
    by_cases h : P.K - 11 < c
    · simp [h, show ¬ c ≤ P.K - 11 by omega_arith]
    · simp [h, show c ≤ P.K - 11 by omega_arith]
  have r6t : t12.gpr .r6 = BitVec.ofNat 32 (alFold P σ (j + 1)) := by
    rw [u12.other _ (by decide), u11.other _ (by decide), c10, fold]
    split <;> rfl
  have lrt : t12.gpr .lr = BitVec.ofNat 32 n := by
    rw [u12.gpr, u11.other _ (by decide), R10.gpr _ (by decide), lr, show 128 - j = n + 1 by omega_arith]
    exact sub_one_ofNat (by omega_arith)
  have ir := hir.of_mem st mm
  refine ⟨?_, fun h0 => ⟨ir, ?_⟩, fun h0 => ⟨by omega_arith, ir, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [eval_ne, hz, u12.gpr.symm, lrt, ofNat_beq_zero (by omega_arith)]
    by_cases h0 : n = 0 <;> simp [h0] <;> omega_arith
  · rw [r6t, show j + 1 = 128 by omega_arith]; rfl
  · rw [u12.other _ (by decide), u11.gpr, dpVal, R10.gpr _ (by decide), r0, BitVec.add_assoc,
      BitVec.ofNat_add_ofNat, show 128 - n = j + 1 by omega_arith, show sCL + 2 * j + 2 = sCL + 2 * (j + 1) by omega_arith]
  · rw [R12.gpr _ (by decide), r4]
  · rw [R12.gpr _ (by decide), r5]
  · rw [r6t, show 128 - n = j + 1 by omega_arith]
  · rw [lrt, show 128 - (128 - n) = n by omega_arith]

theorem alLoop_vp : VP (ALI P 0) alLoop (ALQ P) :=
  (VP.loop (I := ALM P) alBody_vp 127).mono (fun _ _ h => ⟨by decide, h⟩) fun _ _ h => h

theorem alSave_wp {σ s : State} (h : ALQ P σ s) : WP isa (.block alSave) s (AL P σ) := by
  obtain ⟨hir, r6⟩ := h
  have hs := hir.1.1
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  have r12 : t1.gpr .r12 = P.B := by rw [u1.gpr, hs.2.sp, BitVec.add_zero]
  refine s1.wp_strFr (d := oAL) (by show oAL + 4 ≤ frameBytes; decide) (by decide) r12 fun t2 s2 m2 =>
    WP.block_nil ?_
  have mm : t2.mem = s.mem.writeW (P.lay.fr oAL) (s.gpr .r6) := by rw [m2.mem, u1.mem, u1.other _ (by decide)]
  exact ⟨hir.keep_fr s2 mm (by decide) (by simp only [oR, oAL]; decide), by rw [mm, Mem.readW_writeW_self32, r6]⟩

theorem alPart_vp : VP (IR P) alPart (AL P) :=
  (VP.stk (code := [_, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.1 h₂.1.1)
    fun _ _ h => maskInit_wp h).seq (maskLoop_vp.seq
  ((VP.stk (code := [_, _, _, _, _, _, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.1.1 h₂.1.1.1)
    fun _ _ h => alInit_wp h).seq (alLoop_vp.seq
  (VP.stk (code := [_]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.1.1 h₂.1.1.1)
    fun _ _ h => alSave_wp h))))

end VG.Proof.RsaPkcs1Enc.Arm.Dec

end

end


/-!
# RSAES-PKCS1-v1_5 decryption on ARMv7: the scan of `EM`

What `out` holds after the private-key operation (`emOf`: `EM`, or zeros
for an error) and the call's result (`rcOf`). The scan of `EM` from index 2
for its first zero (`scanLoop_vp`): whether there is one, and where
(`Proof.RsaPkcs1Enc.firstZero`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.Arm.Dec

open VG VG.Arm VG.Impl.RsaPkcs1Enc.Arm.Decrypt VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_dp wp_cmp wp_subs wp_ldrb op2_imm op2_reg op2_lsl op2_lsr
  dpVal eval_ne)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.RsaPkcs1Enc (firstZero)

variable {P : EP}

/-! ## `out` and the result after the call -/

/-- `out` after the call: `EM`, or zeros. -/
def emOf (P : EP) (σ : State) : List Byte :=
  match privO P σ with
  | .ok y => y
  | _ => List.replicate P.K 0

/-- The call's result. -/
def rcOf (P : EP) (σ : State) : BitVec 32 :=
  match privO P σ with
  | .ok _ => 1
  | .invalid => 0
  | .fault => 2

theorem Priv.em {σ : State} {m : Mem} {rc : BitVec 32} (h : Priv P σ m rc) :
    Spec.Rsa.bytesAt m (State.addr P.out) P.K = emOf P σ ∧ rc = rcOf P σ := by
  unfold Priv at h
  unfold emOf rcOf
  generalize privO P σ = o at h ⊢
  cases o <;> exact ⟨h.2, h.1⟩

theorem rcOf_cases (P : EP) (σ : State) : rcOf P σ = 1 ∨ rcOf P σ = 0 ∨ rcOf P σ = 2 := by
  unfold rcOf; split <;> simp

/-- `out`, the result in its slot, and `AL` in its slot. -/
def SB (P : EP) (σ s : State) : Prop :=
  AL P σ s ∧ Spec.Rsa.bytesAt s.mem (State.addr P.out) P.K = emOf P σ ∧
    s.mem.readW (P.lay.fr oR) 32 = rcOf P σ

theorem AL.sb {σ s : State} (h : AL P σ s) : SB P σ s := by
  obtain ⟨rc, pr, sl⟩ := h.1.1.2
  have e := Priv.em pr
  exact ⟨h, e.1, by rw [sl, e.2]⟩

theorem emOf_length {σ s : State} (h : SB P σ s) : (emOf P σ).length = P.K := by
  rw [← h.2.1, bytesAt_length]

theorem SB.of_mem {σ s t : State} (h : SB P σ s) (st : P.lay.St σ t) (hm : t.mem = s.mem) : SB P σ t :=
  ⟨⟨h.1.1.of_mem st hm, by rw [hm]; exact h.1.2⟩, by rw [hm]; exact h.2.1, by rw [hm]; exact h.2.2⟩

theorem SB.S {σ s : State} (h : SB P σ s) : S P σ s := h.1.1.1.1

/-! ## Addresses in `out` -/

namespace In
variable {σ : State} (h : In P σ)
include h

theorem out_fit : P.out.toNat + P.K ≤ 2 ^ 32 := by
  have := h.ok.fits P.OUT (by simp); simpa [Proof.X25519.Arm.addr_toNat] using this

theorem outA {i : Nat} (hi : i < P.K) : State.addr (P.out + BitVec.ofNat 32 i) = State.addr P.out + BitVec.ofNat 64 i :=
  addr_add (by have := h.out_fit; omega_arith)

end In

theorem St.out_w {σ s : State} (hs : S P σ s) {i n : Nat} (hn : i + n ≤ P.K) :
    InRegions s.wr (State.addr P.out + BitVec.ofNat 64 i) n :=
  ⟨P.OUT, by rw [hs.2.wr, hs.1.ok.wr]; simp, Offset.contains_base _ hn (by have := hs.1.k1024; omega_arith)⟩

theorem St.out_r {σ s : State} (hs : S P σ s) {i n : Nat} (hn : i + n ≤ P.K) :
    InRegions (s.rd ++ s.wr) (State.addr P.out + BitVec.ofNat 64 i) n :=
  let ⟨r, hr, hc⟩ := St.out_w hs hn
  ⟨r, List.mem_append_right _ hr, hc⟩

/-- Byte `i` of `out`. -/
theorem SB.byte {σ s : State} (h : SB P σ s) {i : Nat} (hi : i < P.K) :
    s.mem (State.addr P.out + BitVec.ofNat 64 i) = (emOf P σ).getD i 1 := by
  rw [← h.2.1, bytesAt_getD hi]

/-! ## Bits -/

/-- `(x - 1) >> 31` for `x < 2^31`: whether `x` is zero. -/
theorem isZero_bit (x : BitVec 32) (hx : x.toNat < 2 ^ 31) : (x - 1) >>> 31 = if x = 0 then 1 else 0 := by
  by_cases h : x = 0
  · subst h; decide
  · have h0 : x.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
    simp only [h, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub,
      show (1 : BitVec 32).toNat = 1 from rfl]
    show _ = 0
    omega_arith

theorem byte_lt (b : Byte) : (b.setWidth 32).toNat < 2 ^ 31 := by
  have := b.isLt; simp only [BitVec.toNat_setWidth]; omega_arith

theorem setWidth_ne_zero {b : Byte} (h : b ≠ 0) : b.setWidth 32 ≠ 0 := by
  intro e
  have := congrArg (BitVec.setWidth 8) e
  simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32), BitVec.setWidth_eq] at this
  exact h (this.trans rfl)

/-- Whether a byte is zero, as a bit. -/
theorem zbit (b : Byte) :
    (if b.setWidth 32 = 0 then (1 : BitVec 32) else 0) = BitVec.ofNat 32 (decide (b = 0)).toNat := by
  by_cases h : b = 0
  · subst h; rfl
  · simp only [setWidth_ne_zero h, ↓reduceIte, h, decide_false]; rfl

/-! ## The scan -/

/-- The first zero of `EM` before index `i`. -/
abbrev fz (P : EP) (σ : State) (i : Nat) : Option Nat := firstZero (emOf P σ) i

/-- `j` bytes scanned, from index 2. -/
def SCI (P : EP) (j : Nat) (σ s : State) : Prop :=
  SB P σ s ∧ s.gpr .r0 = P.out + BitVec.ofNat 32 (2 + j) ∧ s.gpr .r1 = BitVec.ofNat 32 (2 + j) ∧
    s.gpr .lr = BitVec.ofNat 32 (P.K - 2 - j) ∧ s.gpr .r6 = 0 ∧
    s.gpr .r4 = BitVec.ofNat 32 (fz P σ (2 + j)).isSome.toNat ∧ s.gpr .r5 = BitVec.ofNat 32 ((fz P σ (2 + j)).getD 0)

theorem scanInit_wp {σ s : State} (h : AL P σ s) : WP isa (.block scanInit) s (SCI P 0 σ) := by
  have hb := h.sb
  have hs := hb.S
  have hK := hs.1.k64
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  refine s1.wp_arg (j := 0) (by simp) (by dsimp only; decide) fun t2 s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun t3 u3 => ?_
  have s3 : P.lay.St σ t3 := s2.of_rest (u3.rest (ws := [.r0]) (by simp)) u3.mem
  refine s3.wp_arg (j := 4) (by simp) (by dsimp only; decide) fun t4 s4 u4 => ?_
  refine wp_dp (op2_imm (by decide)) fun t5 u5 => ?_
  refine wp_mov (op2_imm (by decide)) fun t6 u6 => ?_
  refine wp_mov (op2_imm (by decide)) fun t7 u7 => ?_
  refine wp_mov (op2_imm (by decide)) fun t8 u8 => ?_
  refine wp_mov (op2_imm (by decide)) fun t9 u9 => WP.block_nil ?_
  have R : Rest [.lr, .r1, .r4, .r5, .r6] t4 t9 := ((((u5.rest (by simp)).trans (u6.rest (by simp))).trans
    (u7.rest (by simp))).trans (u8.rest (by simp))).trans (u9.rest (by simp))
  have s9 : P.lay.St σ t9 := s4.of_rest R (by rw [u9.mem, u8.mem, u7.mem, u6.mem, u5.mem])
  have mm : t9.mem = s.mem := by rw [u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  refine ⟨hb.of_mem s9 mm, ?_, ?_, ?_, u9.gpr, ?_, ?_⟩
  · rw [R.gpr _ (by decide), u4.other _ (by decide), u3.gpr, dpVal, u2.gpr]; rfl
  · rw [u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide), u6.gpr]
  · rw [u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide), u5.gpr,
      dpVal, u4.gpr]
    exact Offset.ofNat_sub_ofNat (d := 2) (by omega_arith)
  · rw [u9.other _ (by decide), u8.other _ (by decide), u7.gpr]; rfl
  · rw [u9.other _ (by decide), u8.gpr]; rfl

/-- `m` bytes left. -/
def SCM (P : EP) (m : Nat) (σ s : State) : Prop := m ≤ P.K - 2 ∧ SCI P (P.K - 2 - m) σ s

/-- The scan done. -/
def SCQ (P : EP) (σ s : State) : Prop :=
  SB P σ s ∧ s.gpr .r6 = 0 ∧ s.gpr .r4 = BitVec.ofNat 32 (fz P σ P.K).isSome.toNat ∧
    s.gpr .r5 = BitVec.ofNat 32 ((fz P σ P.K).getD 0)

/-- One step of the scan, at index `i`. -/
theorem scan_step (EM : List Byte) {i : Nat} (hi : 2 ≤ i) :
    (BitVec.ofNat 32 ((firstZero EM i).getD 0) ||| ((0 - ((BitVec.ofNat 32 (firstZero EM i).isSome.toNat ^^^ 1) &&&
      BitVec.ofNat 32 (decide (EM.getD i 1 = 0)).toNat)) &&& BitVec.ofNat 32 i) =
        BitVec.ofNat 32 ((firstZero EM (i + 1)).getD 0)) ∧
    ((BitVec.ofNat 32 (firstZero EM i).isSome.toNat ||| BitVec.ofNat 32 (decide (EM.getD i 1 = 0)).toNat) =
      BitVec.ofNat 32 (firstZero EM (i + 1)).isSome.toNat) := by
  rw [firstZero]
  cases hf : firstZero EM i with
  | some k =>
    simp only [Option.isSome_some, Option.getD_some, Bool.toNat_true]
    cases decide (EM.getD i 1 = 0) <;> simp
  | none =>
    simp only [Option.isSome_none, Option.getD_none, Bool.toNat_false]
    by_cases e : EM.getD i 1 = 0
    · rw [decide_eq_true e]
      simp only [e, hi, and_self, ↓reduceIte, Option.getD_some, Option.isSome_some,
        Bool.toNat_true]
      refine ⟨?_, by decide⟩
      rw [show (0 : BitVec 32) - ((BitVec.ofNat 32 0 ^^^ 1) &&& BitVec.ofNat 32 1) = BitVec.allOnes 32 by decide,
        BitVec.allOnes_and]
      exact BitVec.zero_or
    · rw [decide_eq_false e]
      simp only [e, and_false, ↓reduceIte, Option.getD_none, Option.isSome_none, Bool.toNat_false]
      refine ⟨?_, by decide⟩
      rw [show (0 : BitVec 32) - ((BitVec.ofNat 32 0 ^^^ 1) &&& BitVec.ofNat 32 0) = 0 by decide]
      simp

theorem scanBody_vp (n : Nat) : VP (SCM P (n + 1)) (.block scanBody) fun σ s =>
    isa.eval .ne s = some (decide (0 < n)) ∧ (n = 0 → SCQ P σ s) ∧ (0 < n → SCM P n σ s) := by
  refine VP.taint [.r0, .r1, .lr] scanBody_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s h => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2.1, h₂.2.2.2.1]
    · rw [h₁.2.2.2.2.1, h₂.2.2.2.2.1]
  obtain ⟨hn, hb, r0, r1, lr, r6, r4, r5⟩ := h
  generalize hj : P.K - 2 - (n + 1) = j at r0 r1 lr r4 r5
  have hs := hb.S
  have hK := hs.1.k64
  have hK' := hs.1.k1024
  have hjK : 2 + j < P.K := by omega_arith
  refine wp_ldrb (by decide) (a := State.addr P.out + BitVec.ofNat 64 (2 + j))
    (by rw [r0, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_zero, hs.1.outA hjK])
    (St.out_r hs (by omega_arith)) fun t1 u1 => ?_
  refine wp_dp (op2_imm (by decide)) fun t2 u2 => ?_
  refine wp_mov (op2_lsr (by decide)) fun t3 u3 => ?_
  refine wp_dp (op2_imm (by decide)) fun t4 u4 => ?_
  refine wp_dp (op2_reg _ _) fun t5 u5 => ?_
  refine wp_dp (op2_reg _ _) fun t6 u6 => ?_
  refine wp_dp (op2_reg _ _) fun t7 u7 => ?_
  refine wp_dp (op2_reg _ _) fun t8 u8 => ?_
  refine wp_dp (op2_reg _ _) fun t9 u9 => ?_
  refine wp_dp (op2_imm (by decide)) fun t10 u10 => ?_
  refine wp_dp (op2_imm (by decide)) fun t11 u11 => ?_
  refine wp_subs (op2_imm (by decide)) fun t12 u12 hz => WP.block_nil ?_
  have R3 : Rest [.r2] s t3 := ((u1.rest (by simp)).trans (u2.rest (by simp))).trans (u3.rest (by simp))
  have R7 : Rest [.r2, .r3] s t7 := ((((R3.mono (by simp)).trans (u4.rest (by simp))).trans (u5.rest (by simp))).trans
    (u6.rest (by simp))).trans (u7.rest (by simp))
  have R9 : Rest [.r2, .r3, .r4, .r5] s t9 := ((R7.mono (by simp)).trans (u8.rest (by simp))).trans
    (u9.rest (by simp))
  have R12 : Rest [.r0, .r1, .r2, .r3, .r4, .r5, .lr] s t12 := (((R9.mono (by simp)).trans (u10.rest (by simp))).trans
    (u11.rest (by simp))).trans (u12.rest (by simp))
  have mm : t12.mem = s.mem := by
    rw [u12.mem, u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have st : P.lay.St σ t12 := hs.2.of_rest R12 mm
  have z3 : t3.gpr .r2 = BitVec.ofNat 32 (decide ((emOf P σ).getD (2 + j) 1 = 0)).toNat := by
    rw [u3.gpr, u2.gpr, dpVal, u1.gpr, hb.byte hjK, isZero_bit _ (byte_lt _), zbit]
  have step := scan_step (emOf P σ) (i := 2 + j) (by omega_arith)
  have a4 : t3.gpr .r4 = BitVec.ofNat 32 (fz P σ (2 + j)).isSome.toNat := by rw [R3.gpr _ (by decide), r4]
  have v4 : t4.gpr .r3 = BitVec.ofNat 32 (fz P σ (2 + j)).isSome.toNat ^^^ 1 := by rw [u4.gpr, dpVal, a4]
  have v5 : t5.gpr .r3 = (BitVec.ofNat 32 (fz P σ (2 + j)).isSome.toNat ^^^ 1) &&&
      BitVec.ofNat 32 (decide ((emOf P σ).getD (2 + j) 1 = 0)).toNat := by
    rw [u5.gpr, dpVal, v4, u4.other _ (by decide), z3]
  have v6 : t6.gpr .r3 = 0 - ((BitVec.ofNat 32 (fz P σ (2 + j)).isSome.toNat ^^^ 1) &&&
      BitVec.ofNat 32 (decide ((emOf P σ).getD (2 + j) 1 = 0)).toNat) := by
    rw [u6.gpr, dpVal, v5, u5.other _ (by decide), u4.other _ (by decide), R3.gpr _ (by decide), r6]
  have v7 : t7.gpr .r3 = (0 - ((BitVec.ofNat 32 (fz P σ (2 + j)).isSome.toNat ^^^ 1) &&&
      BitVec.ofNat 32 (decide ((emOf P σ).getD (2 + j) 1 = 0)).toNat)) &&& BitVec.ofNat 32 (2 + j) := by
    rw [u7.gpr, dpVal, v6, u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      R3.gpr _ (by decide), r1]
  have r5t : t12.gpr .r5 = BitVec.ofNat 32 ((fz P σ (2 + j + 1)).getD 0) := by
    rw [u12.other _ (by decide), u11.other _ (by decide), u10.other _ (by decide), u9.other _ (by decide), u8.gpr,
      dpVal, v7, R7.gpr _ (by decide), r5]
    exact step.1
  have r4t : t12.gpr .r4 = BitVec.ofNat 32 (fz P σ (2 + j + 1)).isSome.toNat := by
    rw [u12.other _ (by decide), u11.other _ (by decide), u10.other _ (by decide), u9.gpr, dpVal,
      u8.other _ (by decide), R7.gpr _ (by decide), r4, u8.other _ (by decide), u7.other _ (by decide),
      u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), z3]
    exact step.2
  have r1t : t12.gpr .r1 = BitVec.ofNat 32 (2 + j + 1) := by
    rw [u12.other _ (by decide), u11.other _ (by decide), u10.gpr, dpVal, R9.gpr _ (by decide), r1,
      BitVec.ofNat_add_ofNat]
  have r0t : t12.gpr .r0 = P.out + BitVec.ofNat 32 (2 + j + 1) := by
    rw [u12.other _ (by decide), u11.gpr, dpVal, u10.other _ (by decide), R9.gpr _ (by decide), r0,
      BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have lrt : t12.gpr .lr = BitVec.ofNat 32 n := by
    rw [u12.gpr, u11.other _ (by decide), u10.other _ (by decide), R9.gpr _ (by decide), lr,
      show P.K - 2 - j = n + 1 by omega_arith]
    exact sub_one_ofNat (by omega_arith)
  have r6t : t12.gpr .r6 = 0 := by rw [R12.gpr _ (by decide), r6]
  have sb := hb.of_mem st mm
  refine ⟨?_, fun h0 => ⟨sb, r6t, ?_, ?_⟩, fun h0 => ⟨by omega_arith, sb, ?_, ?_, ?_, r6t, ?_, ?_⟩⟩
  · rw [eval_ne, hz, ← u12.gpr, lrt, ofNat_beq_zero (by omega_arith)]
    by_cases h0 : n = 0 <;> simp [h0] <;> omega_arith
  · rw [r4t, show 2 + j + 1 = P.K by omega_arith]
  · rw [r5t, show 2 + j + 1 = P.K by omega_arith]
  · rw [r0t, show 2 + (P.K - 2 - n) = 2 + j + 1 by omega_arith]
  · rw [r1t, show 2 + (P.K - 2 - n) = 2 + j + 1 by omega_arith]
  · rw [lrt, show P.K - 2 - (P.K - 2 - n) = n by omega_arith]
  · rw [r4t, show 2 + (P.K - 2 - n) = 2 + j + 1 by omega_arith]
  · rw [r5t, show 2 + (P.K - 2 - n) = 2 + j + 1 by omega_arith]

theorem scanLoop_vp : VP (SCI P 0) scanLoop (SCQ P) := by
  refine (VP.loop (I := SCM P) scanBody_vp (P.K - 2 - 1)).mono (fun σ s h => ?_) fun _ _ h => h
  have hK := h.1.S.1.k64
  exact ⟨by omega_arith, by rw [show P.K - 2 - (P.K - 2 - 1 + 1) = 0 by omega_arith]; exact h⟩

end VG.Proof.RsaPkcs1Enc.Arm.Dec

end

end


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

end

end


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
  · simp only [h, ↓reduceIte, show kl ≤ j by omega_using [h], true_and]
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
  have hjK : j < P.K := by omega_using [hn, hj]
  have hl := lsel_le P σ (by omega_using [hK])
  refine wp_ldrb (by decide) (a := State.addr P.out + BitVec.ofNat 64 j)
    (by rw [r0, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_zero, hs.1.outA hjK])
    (St.out_r hs (by omega_using [hn, hj])) fun t1 u1 => ?_
  refine wp_ldrb (by decide) (a := State.addr P.scr + BitVec.ofNat 64 (sAM + j))
    (by rw [u1.other _ (by decide), r1, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_zero,
      hs.1.scrA (by simp only [sAM]; omega_using [hj, hK'])])
    (by rw [u1.rd, u1.wr]; exact St.sc_r hs (by simp only [sAM]; omega_using [hj, hK'])) fun t2 u2 => ?_
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
  have hkl : P.K - lselV P σ < 2 ^ 31 := by omega_using [hK']
  have v10 : t10.gpr .r2 = (if vB P σ then ((emOf P σ).getD j 1).setWidth 32 else ((amV P σ).getD j 0).setWidth 32)
      &&& (if P.K - lselV P σ ≤ j ∧ okB P σ = true then BitVec.allOnes 32 else 0) := by
    rw [u10.gpr, dpVal, u9.gpr, dpVal, u8.gpr, dpVal, u7.gpr, u6.gpr, dpVal, u9.other .r2 (by decide),
      u8.other .r2 (by decide), u7.other .r2 (by decide), u6.other .r2 (by decide), v5,
      u8.other .r11 (by decide), u7.other .r11 (by decide), u6.other .r11 (by decide), R5.gpr .r11 (by decide), r11,
      R5.gpr .r4 (by decide), r4, R5.gpr .r9 (by decide), r9, mask_ge (by omega_using [hj, hK']) hkl]
  refine wp_strb (by decide) (a := State.addr P.out + BitVec.ofNat 64 j)
    (by rw [R10.gpr .r0 (by decide), r0, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_zero, hs.1.outA hjK])
    (by rw [R10.wr]; exact St.out_w hs (by omega_using [hn, hj])) fun t11 m11 => ?_
  refine wp_dp (op2_imm (by decide)) fun t12 u12 => ?_
  refine wp_dp (op2_imm (by decide)) fun t13 u13 => ?_
  refine wp_dp (op2_imm (by decide)) fun t14 u14 => ?_
  refine wp_subs (op2_imm (by decide)) fun t15 u15 hz => WP.block_nil ?_
  have R15 : Rest [.r0, .r1, .r2, .r3, .r4, .r5, .lr] s t15 := ((((((R10.mono (by simp)).trans (m11.rest _)).trans
    (u12.rest (by simp))).trans (u13.rest (by simp))).trans (u14.rest (by simp))).trans (u15.rest (by simp)))
  have bv : (t10.gpr .r2).setWidth 8 = obV P σ j := by rw [v10, selByte]; rfl
  have mm : t15.mem = s.mem.writeW (State.addr P.out + BitVec.ofNat 64 j) (obV P σ j) := by
    rw [u15.mem, u14.mem, u13.mem, u12.mem, m11.mem, m10, bv]
  have W1 : Region.Sub ⟨State.addr P.out + BitVec.ofNat 64 j, 1⟩ P.OUT := Offset.sub_base _ (by omega_using [hn, hj])
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
      R10.gpr .lr (by decide), lr, show P.K - j = n + 1 by omega_using [hn, hj]]
    exact sub_one_ofNat (by omega_using [hn, hK'])
  have obt : ∀ i < P.K, t15.mem (State.addr P.out + BitVec.ofNat 64 i) =
      if i < j + 1 then obV P σ i else (emOf P σ).getD i 1 := by
    intro i hi
    rw [mm, WriteBytes.writeW8_apply]
    by_cases e : i = j
    · subst e; simp
    · simp only [Offset.add_ofNat_ne (State.addr P.out) (by omega_using [hK', hi]) (by omega_using [hj, hK']) e, ↓reduceIte]
      rw [ob i hi]
      simp only [show (i < j + 1) = (i < j) by apply propext; omega_using [e]]
  have sl : SL P (j + 1) σ t15 :=
    ⟨⟨hs.1, st⟩, obt,
      (bytes_frame fr (R := sc P sAM P.K) (one (hs.1.sc_out (by simp only [sAM]; omega_using [hK'])))
        (by show P.K ≤ 2 ^ 64; omega_using [hK'])).trans am,
      by rw [slot_keep fr (one (hs.1.ok.stk_fr (R := P.OUT) (.inr (by simp))
        (by simp only [oR, frameBytes]; decide)))]; exact rc,
      (wordsAt_frame fr (one hs.1.out_ml.symm) (by decide)).trans ml,
      r0t, r1t, r4t, by rw [lrt, show P.K - (j + 1) = n by omega_using [hn, hj]], by rw [R15.gpr .r9 (by decide), r9],
      by rw [R15.gpr .r10 (by decide), r10], by rw [R15.gpr .r11 (by decide), r11], hEM⟩
  refine ⟨?_, fun h0 => ?_, fun h0 => ⟨by omega_using [hn], by rw [show P.K - n = j + 1 by omega_using [hn, hj]]; exact sl⟩⟩
  · rw [eval_ne, hz, ← u15.gpr, lrt, ofNat_beq_zero (by omega_using [hn, hK'])]
    by_cases h0 : n = 0 <;> simp [h0] <;> omega_using [h0]
  · rw [show P.K = j + 1 by omega_using [hn, hj, h0]]; exact sl

theorem selLoop_vp : VP (SL P 0) selLoop (SL P P.K) := by
  refine (VP.loop (I := SLM P) selBody_vp (P.K - 1)).mono (fun σ s h => ?_) fun _ _ h => h
  have hK := h.1.1.k64
  exact ⟨by omega_using [hK], by rw [show P.K - (P.K - 1 + 1) = 0 by omega_using []]; exact h⟩

/-! ## The result -/

/-- What the shared contract states of the result `r` and the memory `m`. -/
def Res (P : EP) (σ : State) (m : Mem) (r : BitVec 32) : Prop :=
  Spec.RsaPkcs1Enc.writtenMsg m (State.addr P.out) (State.addr P.ml) P.K r
    (Spec.RsaPkcs1Enc.decrypt P.nB P.eB (dB P σ) (pB P σ) (qB P σ) (dpB P σ) (dqB P σ) (qiB P σ) (cB P σ))

/-- The end of the body. -/
def Fin (P : EP) (σ s : State) : Prop := S P σ s ∧ Res P σ s.mem (s.gpr .r0)

theorem amV_length (P : EP) (σ : State) : (amV P σ).length = P.K := by
  rw [amV, VG.Proof.RsaPkcs1Enc.irprf_eq, List.length_take, flatMap_blocks_length]
  omega_using []

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
    rw [VG.Proof.RsaPkcs1Enc.decryptWith_of_ok hC (by omega_using [hK]) ho]
    obtain ⟨hl, hm⟩ := VG.Proof.RsaPkcs1Enc.sel_eq (EM := EM) (AM := amV P σ) (al := alV P σ) hEM'
      (amV_length P σ) (by omega_using [hK]) (alV_le P σ)
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
    rw [VG.Proof.RsaPkcs1Enc.decryptWith_of_fault hC (by omega_using [hK]) ho]
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

end

end


/-!
# RSAES-PKCS1-v1_5 decryption on ARMv7: the body

The pieces in order, each correct and constant time at once (`body_vp`):
from a state of the body to the result the shared contract states (`Fin`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.Arm.Dec

open VG VG.Arm VG.Impl.RsaPkcs1Enc.Arm.Decrypt VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.Rsa.Arm.Recover (VP)

variable {P : EP}

theorem Base.of_mem {σ s t : State} (h : Base P σ s) (st : P.lay.St σ t) (hm : t.mem = s.mem) : Base P σ t :=
  h.frame st (rs := []) (by rw [hm]; exact Frame.refl _ _) fun _ h => absurd h List.not_mem_nil

/-! ## The private-key operation and `D` -/

theorem privArgs_vp : VP (S P) (.block (privArgs P.pc)) (R1 P) :=
  VP.stk (code := (privArgs P.pc).tail) (by generalize P.pc = b; cases b <;> decide)
    (by generalize P.pc = b; cases b <;> decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁ h₂) fun _ _ h => privArgs_wp h

theorem dZero_vp : VP (R2 P) (.block dZero) (D1 P) :=
  VP.stk (code := [_, _, _, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1 h₂.1)
    fun _ _ h => dZero_wp h

theorem zero_vp : VP (D1 P) Impl.Bignum.Arm.maskBytes (D2 P) :=
  VP.ct Bignum.Arm.maskBytes_ct (fun _ _ _ _ h₁ h₂ => ⟨by rw [h₁.2.1, h₂.2.1], by rw [h₁.2.2.1, h₂.2.2.1]⟩)
    fun _ _ h => zero_wp h

theorem dCopy_vp : VP (D2 P) (.block dCopy) (D3 P) :=
  VP.stk (code := [_, _, _, _, _, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.1 h₂.1.1)
    fun _ _ h => dCopy_wp h

theorem copy_vp : VP (D3 P) Impl.Bignum.Arm.copyBytes (D4 P) :=
  VP.ct Bignum.Arm.copyBytes_ct (fun _ _ _ _ h₁ h₂ => ⟨by rw [h₁.2.1, h₂.2.1], by rw [h₁.2.2.1, h₂.2.2.1],
    by rw [h₁.2.2.2, h₂.2.2.2]⟩) fun _ _ h => copy_wp h

/-! ## `DH` and `KDK` -/

theorem hashD_vp : VP (D4 P) (hashD decFns) (H6 P) :=
  ((VP.stk (code := [_]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.1 h₂.1.1)
    fun _ _ h => shaInitArgs_wp h).seq shaInit_vp).seq
  (((VP.stk (code := [_, _, _, _, _, _, _]) (by decide) (by decide)
    (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.1.1 h₂.1.1.1) fun _ _ h => shaUpdArgs_wp h).seq shaUpd_vp).seq
  ((VP.stk (code := [_, _, _, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.1 h₂.1.1)
    fun _ _ h => shaFinArgs_wp h).seq shaFin_vp))

theorem kdkInitArgs_vp : VP (H6 P) (.block (macInitArgs sDH)) (K1 P) :=
  VP.stk (code := [_, _, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.1 h₂.1.1)
    fun _ _ h => macInitArgs_wp (by decide) h.1.1 fun t st hm ha =>
      ⟨⟨h.1.of_mem st hm, by rw [hm]; exact h.2⟩, ha⟩

theorem kdkMac_vp : VP (H6 P) (kdkMac decFns) (K6 P) :=
  (kdkInitArgs_vp.seq kdkInit_vp).seq
  (((VP.stk (code := [_, _, _, _, _, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.1 h₂.1.1)
    fun _ _ h => kdkUpdArgs_wp h).seq kdkUpd_vp).seq
  ((VP.stk (code := [_, _, _, _, _, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.1 h₂.1.1)
    fun _ _ h => kdkFinArgs_wp h).seq kdkFin_vp))

/-! ## The padding and the output -/

theorem selPart_vp : VP (AL P) selPart (Fin P) :=
  (VP.stk (code := [_, _, _, _, _, _, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.sb.S h₂.sb.S)
    fun _ _ h => scanInit_wp h).seq (scanLoop_vp.seq
  ((VP.stk (code := [_, _, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.S h₂.1.S)
    fun _ _ h => validLoads_wp h).seq
  ((VP.taint [.r0] validBlock_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1, h₂.2.1]) fun _ _ h => validBlock_wp h).seq
  ((VP.stk (code := [_]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.S h₂.1.S)
    fun _ _ h => mlLoad_wp h).seq
  ((VP.taint [.r1] mlStore_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2]) fun _ _ h => mlStore_wp h).seq
  ((VP.stk (code := [_, _, _, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.1.S h₂.1.1.S)
    fun _ _ h => selInit_wp h).seq (selLoop_vp.seq
  (VP.stk (code := [_]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1 h₂.1)
    fun _ _ h => fin_wp h))))))))

/-! ## The body -/

theorem body_vp (v : Proof.Rsa.Arm.CrtImpl) :
    VP (S P) (body decFns P.pc (privN P.pc v) (privC P.pc v)) (Fin P) :=
  privArgs_vp.seq ((call_vpG v).seq (dZero_vp.seq (zero_vp.seq (dCopy_vp.seq (copy_vp.seq (hashD_vp.seq
    (kdkMac_vp.seq (clLoop_vp.seq (amLoop_vp.seq (alPart_vp.seq selPart_vp))))))))))

end VG.Proof.RsaPkcs1Enc.Arm.Dec
