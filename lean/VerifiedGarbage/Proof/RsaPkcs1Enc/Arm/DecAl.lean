module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecIrprf
import VerifiedGarbage.Proof.RsaPkcs1Enc.Select
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Encode
import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecTaint
import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecPrfLoop
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Vp
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry

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
  have hd' : d + 4 ≤ frameBytes + 56 := by simp only [frameBytes] at hd ⊢; omega
  refine ⟨h.1.frame st fr fun r hr => ?_, ?_, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact hs.1.safe_fr hd ho
  · rw [sc_keep_fr hs.1 hd (by decide) fr]; exact h.2.1
  · rw [sc_keep_fr hs.1 hd (by simp only [sAM]; omega) fr]; exact h.2.2

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
  exact Offset.ofNat_sub_ofNat (d := 11) (by omega)

/-- The loop's stage, `m` doublings left. -/
def MLI (P : EP) (m : Nat) (σ s : State) : Prop := m ≤ bitLength (P.K - 11) ∧ MI P (bitLength (P.K - 11) - m) σ s

theorem bitLength_le {x : Nat} (hx : x ≠ 0) (hx' : x < 2 ^ 30) : 2 ^ bitLength x - 1 < 2 ^ 31 := by
  have := VG.Proof.RsaPkcs1Enc.bitMask_le hx
  simp only [bitMask] at this
  omega

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
  have hx : P.K - 11 ≠ 0 := by omega
  generalize hB : bitLength (P.K - 11) = B at hn r0
  have hj : B - (n + 1) < bitLength (P.K - 11) := by omega
  have hlt := VG.Proof.RsaPkcs1Enc.bitMask_lt hx hj
  have hst := VG.Proof.RsaPkcs1Enc.bitMask_step (by omega : 1 ≤ P.K - 11) hlt
  have hp : 2 ^ (B - (n + 1) + 1) - 1 ≤ 2 ^ B - 1 :=
    Nat.sub_le_sub_right (Nat.pow_le_pow_right (by decide) (by omega)) _
  have hB31 : 2 ^ B - 1 < 2 ^ 31 := by rw [← hB]; exact bitLength_le hx (by omega)
  refine wp_dp (op2_reg _ _) fun t1 u1 => ?_
  refine wp_dp (op2_imm (by decide)) fun t2 u2 => ?_
  refine wp_dp (op2_reg _ _) fun t3 u3 => ?_
  refine wp_mov (op2_lsr (by decide)) fun t4 u4 => ?_
  refine wp_cmp (op2_imm (by decide)) fun t5 u5 hz => WP.block_nil ?_
  have r0v : t2.gpr .r0 = BitVec.ofNat 32 (2 ^ (B - (n + 1) + 1) - 1) := by
    rw [u2.gpr, dpVal, u1.gpr, dpVal, r0, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat, ← hst.1]
    congr 1; omega
  have r2v : t4.gpr .r2 = if 2 ^ (B - (n + 1) + 1) - 1 < P.K - 11 then 1 else 0 := by
    rw [u4.gpr, u3.gpr, dpVal, r0v, u2.other _ (by decide), u1.other _ (by decide), r1]
    exact top_sub (by omega) (by omega)
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
      rw [show B - (n + 1) + 1 = B by omega] at h
      omega
    · intro h0
      exact VG.Proof.RsaPkcs1Enc.bitMask_lt hx (by omega)
  refine ⟨?_, fun h0 => ⟨ir, ?_⟩, fun h0 => ⟨by omega, ir, ?_, r1t⟩⟩
  · rw [eval_ne, hz, r2v]
    by_cases h0 : 0 < n
    · have hc : 2 ^ (B - (n + 1) + 1) - 1 < P.K - 11 := e ▸ h0
      simp [hc, h0]
    · have hc : ¬ 2 ^ (B - (n + 1) + 1) - 1 < P.K - 11 := fun h => h0 (e ▸ h)
      simp [hc, h0]
  · rw [r0t, show B - (n + 1) + 1 = B by omega, ← hB]; rfl
  · rw [r0t, show B - (n + 1) + 1 = B - n by omega, hB]

theorem maskLoop_vp : VP (MI P 0) maskLoop (MK P) := by
  refine (VP.loop (I := MLI P) maskBody_vp (bitLength (P.K - 11) - 1)).mono (fun σ s h => ?_) fun _ _ h => h
  have hK := h.1.1.1.1.k64
  have : 1 ≤ bitLength (P.K - 11) := by
    simp only [bitLength, show P.K - 11 ≠ 0 by omega, ↓reduceIte]; omega
  refine ⟨by omega, ?_⟩
  rw [show bitLength (P.K - 11) - (bitLength (P.K - 11) - 1 + 1) = 0 by omega]; exact h

/-! ## The candidates -/

theorem clV_length (P : EP) (σ : State) : (clV P σ).length = 256 := by
  rw [clV_eq, flatMap_blocks_length]

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
  omega

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
    exact Offset.ofNat_sub_ofNat (d := 11) (by omega)
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
  have hjn : j + n + 1 = 128 := by omega
  have hs := hir.1.1
  have hK := hs.1.k64
  have hK' := hs.1.k1024
  have hx : P.K - 11 ≠ 0 := by omega
  have hm := VG.Proof.RsaPkcs1Enc.bitMask_le hx
  have ha : ∀ d < 2, State.addr (s.gpr .r0 + BitVec.ofNat 32 d) =
      State.addr P.scr + BitVec.ofNat 64 (sCL + (2 * j + d)) := by
    intro d hd
    rw [r0, BitVec.add_assoc, BitVec.ofNat_add_ofNat, hs.1.scrA (by simp only [sCL]; omega), Nat.add_assoc]
  have e0 := cl_byte hir (i := 2 * j + 0) (by omega)
  have e1 := cl_byte hir (i := 2 * j + 1) (by omega)
  refine wp_ldrb (by decide) (ha 0 (by decide)) (St.sc_r hs (by simp only [sCL]; omega)) fun t1 u1 => ?_
  refine wp_ldrb (by decide) (a := State.addr P.scr + BitVec.ofNat 64 (sCL + (2 * j + 1)))
    (by rw [u1.other _ (by decide)]; exact ha 1 (by decide))
    (by rw [u1.rd, u1.wr]; exact St.sc_r hs (by simp only [sCL]; omega)) fun t2 u2 => ?_
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
    exact top_sub (by omega) (by omega)
  have c10 : t10.gpr .r6 = if P.K - 11 < c then BitVec.ofNat 32 (alFold P σ j) else BitVec.ofNat 32 c := by
    rw [u10.gpr, dpVal, u9.other _ (by decide), u8.other _ (by decide), R7.gpr _ (by decide), r6, u9.gpr, dpVal,
      u8.gpr, dpVal, R7.gpr _ (by decide), r6, u8.other _ (by decide), u7.other _ (by decide),
      u6.other _ (by decide), u5.other _ (by decide), c4, u7.gpr, dpVal, c6]
    exact sel_bv _ _ _
  have fold : alFold P σ (j + 1) = if P.K - 11 < c then alFold P σ j else c := by
    rw [alFold, VG.Proof.RsaPkcs1Enc.foldl_range_succ, altStep_and]
    simp only [hb0, hb1, hc]
    by_cases h : P.K - 11 < c
    · simp [h, show ¬ c ≤ P.K - 11 by omega]
    · simp [h, show c ≤ P.K - 11 by omega]
  have r6t : t12.gpr .r6 = BitVec.ofNat 32 (alFold P σ (j + 1)) := by
    rw [u12.other _ (by decide), u11.other _ (by decide), c10, fold]
    split <;> rfl
  have lrt : t12.gpr .lr = BitVec.ofNat 32 n := by
    rw [u12.gpr, u11.other _ (by decide), R10.gpr _ (by decide), lr, show 128 - j = n + 1 by omega]
    exact sub_one_ofNat (by omega)
  have ir := hir.of_mem st mm
  refine ⟨?_, fun h0 => ⟨ir, ?_⟩, fun h0 => ⟨by omega, ir, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [eval_ne, hz, u12.gpr.symm, lrt, ofNat_beq_zero (by omega)]
    by_cases h0 : n = 0 <;> simp [h0] <;> omega
  · rw [r6t, show j + 1 = 128 by omega]; rfl
  · rw [u12.other _ (by decide), u11.gpr, dpVal, R10.gpr _ (by decide), r0, BitVec.add_assoc,
      BitVec.ofNat_add_ofNat, show 128 - n = j + 1 by omega, show sCL + 2 * j + 2 = sCL + 2 * (j + 1) by omega]
  · rw [R12.gpr _ (by decide), r4]
  · rw [R12.gpr _ (by decide), r5]
  · rw [r6t, show 128 - n = j + 1 by omega]
  · rw [lrt, show 128 - (128 - n) = n by omega]

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
