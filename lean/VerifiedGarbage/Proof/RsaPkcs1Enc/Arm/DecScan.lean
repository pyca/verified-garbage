module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecAl
import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecTaint
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

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

theorem bit_toNat (p : Bool) : (if p = true then (1 : BitVec 32) else 0) = BitVec.ofNat 32 p.toNat := by
  cases p <;> rfl

/-! ## The scan -/

/-- The first zero of `EM` before index `i`. -/
abbrev fz (P : EP) (σ : State) (i : Nat) : Option Nat := firstZero (emOf P σ) i

/-- `j` bytes scanned, from index 2. -/
def SCI (P : EP) (j : Nat) (σ s : State) : Prop :=
  SB P σ s ∧ s.gpr .r0 = P.out + BitVec.ofNat 32 (2 + j) ∧ s.gpr .r1 = BitVec.ofNat 32 (2 + j) ∧
    s.gpr .lr = BitVec.ofNat 32 (P.K - 2 - j) ∧ s.gpr .r6 = 0 ∧
    s.gpr .r4 = BitVec.ofNat 32 (fz P σ (2 + j)).isSome.toNat ∧ s.gpr .r5 = BitVec.ofNat 32 ((fz P σ (2 + j)).getD 0)

theorem firstZero_two (EM : List Byte) : firstZero EM 2 = none := rfl

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
