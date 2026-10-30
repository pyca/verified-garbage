module

public import VerifiedGarbage.Impl.Ed25519.Arm.Comb
public import VerifiedGarbage.Proof.Ed25519.Arm.Field
public import VerifiedGarbage.Proof.Ed25519.Arm.FieldProg
public import VerifiedGarbage.Proof.Ed25519.Arm.PointKeep
public import VerifiedGarbage.Proof.Ed25519.CombDigits64
public import VerifiedGarbage.Proof.Ed25519.Group.Extended
public import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Ed25519.Arm.AccumulateStep
import VerifiedGarbage.Proof.Ed25519.Arm.Points
import VerifiedGarbage.Proof.Ed25519.CombDigits
import VerifiedGarbage.Proof.Ed25519.ScalarBytes
import VerifiedGarbage.Proof.Ed25519.WindowNibble
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.ReadHalves
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.X25519.Arm.Limbs
import VerifiedGarbage.Proof.X25519.Arm.Setup
import VerifiedGarbage.Proof.X25519.Field

/-!
# Ed25519's base-point multiplication on ARMv7: the comb

What `combMultiply` computes, in three parts.

*The digits.* Digit `i` of the scalar at `p` is the nibble `n` of byte `i / 2` (its high
nibble for odd `i`), `nibAt`; `combDigit` leaves the mask of its sign (all ones for `n < 8`)
at byte `SGN` of the workspace, and in `r1`–`r8` the masks of the magnitudes `1 … 8` of
`n - 8`, all ones exactly for `magOf n` (`combDigit_ok`). The bit arithmetic is checked by
`decide` over the 256 bytes, the 16 nibbles and the 9 magnitudes.

*The selection.* The static `combSym` at `T` holds, as 32-bit words, the limbs of the comb's
entries (`tbl_read`, from the 64-bit words a contract states). `combSelect` stores into
slots 4–6 the limbs of coordinate `c` of entry `a` of table `i`, `selLimb`, for the magnitude
`a ≤ 8` whose mask is the one set among `r1`–`r8` (`combSelect_ok`); entry 0 is the
identity's `[1, 1, 0]`.

*The loop.* After the selection, slots 4–6 hold the entry's coordinates (`sel_env`);
`combNeg` negates it for a negative digit, and `addAffineOps` adds it to the accumulator
exactly as the specification's `pointAdd` (`mixedResult_eq`). After step `j` of the loop, the
accumulator (slots 0–3) represents `[17 G + Σ_{i < j} d_i 16^i]B` (`digitSum64`); after the
64 steps, the scalar's multiple (`comb64_total`). Before the loop, the scalar is copied into
the workspace (`combCopy_ok`) and the accumulator set to `[17 G]B` (`combStart_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.Arm

open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

/-- Digit `i`'s nibble of the scalar at `p`. -/
def nibAt (m : Mem) (p : Addr) (i : Nat) : Nat :=
  (m (p + BitVec.ofNat 64 (i / 2))).toNat / 16 ^ (i % 2) % 16

theorem nibAt_lt (m : Mem) (p : Addr) (i : Nat) : nibAt m p i < 16 := Nat.mod_lt _ (by decide)

/-- The magnitude of the digit `n - 8`. -/
def magOf (n : Nat) : Nat := if n < 8 then 8 - n else n - 8

theorem magOf_le {n : Nat} (hn : n < 16) : magOf n ≤ 8 := by
  unfold magOf; split <;> omega

/-- All ones for `true`, zero for `false`. -/
def maskB (b : Bool) : BitVec 32 := if b then BitVec.allOnes 32 else 0

private theorem counter_fact : ∀ i < 64,
    BitVec.ofNat 32 i >>> 1 = BitVec.ofNat 32 (i / 2) ∧
      (BitVec.ofNat 32 i &&& (1 : BitVec 32)) = BitVec.ofNat 32 (i % 2) := by decide

private theorem nibble_fact : ∀ v < 256, ∀ o < 2,
    (BitVec.ofNat 32 v &&& (15 : BitVec 32)) ^^^
        ((BitVec.ofNat 32 v >>> 4 ^^^ (BitVec.ofNat 32 v &&& (15 : BitVec 32))) &&&
          ((0 : BitVec 32) - BitVec.ofNat 32 o)) =
      BitVec.ofNat 32 (v / 16 ^ o % 16) := by decide +kernel

private theorem sign_fact : ∀ n < 16,
    (0 : BitVec 32) - ((BitVec.ofNat 32 n - (8 : BitVec 32)) >>> 31) = maskB (decide (n < 8)) ∧
      ((BitVec.ofNat 32 n - (8 : BitVec 32)) ^^^ maskB (decide (n < 8))) - maskB (decide (n < 8)) =
        BitVec.ofNat 32 (magOf n) := by decide

private theorem mask_fact : ∀ a ≤ 8, ∀ k < 8,
    (0 : BitVec 32) - (((BitVec.ofNat 32 a ^^^ BitVec.ofNat 32 (k + 1)) - (1 : BitVec 32)) >>> 31) =
      maskB (decide (a = k + 1)) := by decide

private theorem enc_fact : ∀ k < 8, encodable (BitVec.ofNat 32 (k + 1)) = true := by decide

private theorem maskReg_fact : ∀ k < 8,
    maskReg (k + 1) ≠ .r9 ∧ maskReg (k + 1) ≠ .r10 ∧
      maskReg (k + 1) ∈ [Reg.r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8] := by decide

private theorem maskReg_ne : ∀ k < 8, ∀ k' < 8, k' ≠ k → maskReg (k' + 1) ≠ maskReg (k + 1) := by
  decide

/-- The masks of the magnitudes, from the magnitude `a` in `r10` and zero in `r9`. -/
structure MaskInv (s₀ : State) (a : Nat) (k : Nat) (s : State) : Prop where
  rest : Rest [.r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8] s₀ s
  mem : s.mem = s₀.mem
  masks : ∀ k' < k, s.gpr (maskReg (k' + 1)) = maskB (decide (a = k' + 1))

theorem combMasks_ok {s₀ : State} {a : Nat} (ha : a ≤ 8) (h9 : s₀.gpr .r9 = 0)
    (h10 : s₀.gpr .r10 = BitVec.ofNat 32 a) :
    WP isa (.block ((List.range 8).flatMap fun k => combMask (k + 1))) s₀ (MaskInv s₀ a 8) := by
  refine wp_range_flatMap (M := isa) (MaskInv s₀ a) (fun k s hk h => ?_) 8 (Nat.le_refl _) s₀
    ⟨Rest.refl _ _, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  have m := maskReg_fact k hk
  have g9 : s.gpr .r9 = 0 := (h.rest.gpr _ (by decide)).trans h9
  have g10 : s.gpr .r10 = BitVec.ofNat 32 a := (h.rest.gpr _ (by decide)).trans h10
  unfold combMask
  refine wp_dp (op2_imm (enc_fact k hk)) fun s₁ u₁ => wp_dp (op2_imm (by decide)) fun s₂ u₂ =>
    wp_mov (op2_lsr (by decide)) fun s₃ u₃ => wp_dp (op2_reg _ _) fun s₄ u₄ => WP.block_nil ?_
  have hr : ∀ {t t' : State} {v : BitVec 32}, Upd t t' (maskReg (k + 1)) v →
      Rest [.r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8] t t' := fun u => u.rest m.2.2
  refine ⟨h.rest.trans ((hr u₁).trans ((hr u₂).trans ((hr u₃).trans (hr u₄)))), ?_, fun k' hk' => ?_⟩
  · rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem, h.mem]
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hk' with hk' | rfl
    · have ne := maskReg_ne k hk k' (by omega) (by omega)
      rw [u₄.other _ ne, u₃.other _ ne, u₂.other _ ne, u₁.other _ ne]
      exact h.masks k' hk'
    · rw [u₄.gpr, dpVal, u₃.other _ m.1.symm, u₂.other _ m.1.symm, u₁.other _ m.1.symm, g9, u₃.gpr,
        u₂.gpr, dpVal, u₁.gpr, dpVal, g10]
      exact mask_fact a ha k' hk

theorem combDigit_ok {b p : BitVec 32} {s : State} (hc : Ctx b s) {i : Nat} (hi : i < 64)
    (hp : b + BitVec.ofNat 32 SCAL = p)
    (h11 : s.gpr .r11 = BitVec.ofNat 32 i) (hfit : p.toNat + 32 ≤ 2 ^ 32)
    (hr : InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 (i / 2)) 1) :
    WP isa (.block combDigit) s fun t =>
      Rest [.r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r12] s t ∧
      t.mem = s.mem.writeW (State.addr b + BitVec.ofNat 64 SGN)
        (maskB (decide (nibAt s.mem (State.addr p) i < 8))) ∧
      t.gpr .r9 = 0 ∧ t.gpr .r10 = BitVec.ofNat 32 (magOf (nibAt s.mem (State.addr p) i)) ∧
      ∀ k < 8, t.gpr (maskReg (k + 1)) = maskB (decide (magOf (nibAt s.mem (State.addr p) i) = k + 1)) := by
  have cf := counter_fact i hi
  unfold combDigit
  rw [WP.block_append_iff]
  refine wp_dp (op2_imm (by decide)) fun s₁ u₁ => wp_mov (op2_lsr (by decide)) fun s₂ u₂ =>
    wp_dp (op2_reg _ _) fun s₃ u₃ => ?_
  have e3 : s₃.gpr .r12 = p + BitVec.ofNat 32 (i / 2) := by
    rw [u₃.gpr, dpVal, u₂.other _ (by decide), u₁.gpr, dpVal, hc.r0, hp, u₂.gpr, u₁.other _ (by decide), h11, cf.1]
  have r3 : Rest [.r2, .r12] s s₃ :=
    (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans (u₃.rest (by decide)))
  have m3 : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  let a := State.addr p + BitVec.ofNat 64 (i / 2)
  refine wp_ldrb (a := a) (by decide)
    (by rw [e3]; exact (congrArg State.addr (BitVec.add_zero _)).trans (addr_add (by omega)))
    (by rw [r3.rd, r3.wr]; exact hr) fun s₄ u₄ => ?_
  have v_lt := (s.mem a).isLt
  have e4 : s₄.gpr .r3 = BitVec.ofNat 32 (s.mem a).toNat := by
    rw [u₄.gpr, m3]
    exact BitVec.eq_of_toNat_eq (by rw [toNat_setWidth8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
  refine wp_dp (op2_imm (by decide)) fun s₅ u₅ => wp_mov (op2_lsr (by decide)) fun s₆ u₆ =>
    wp_mov (op2_imm (by decide)) fun s₇ u₇ => wp_dp (op2_imm (by decide)) fun s₈ u₈ =>
    wp_dp (op2_reg _ _) fun s₉ u₉ => wp_dp (op2_reg _ _) fun s₁₀ u₁₀ =>
    wp_dp (op2_reg _ _) fun s₁₁ u₁₁ => wp_dp (op2_reg _ _) fun s₁₂ u₁₂ => ?_
  -- The nibble, in `r4`.
  have e12 : s₁₂.gpr .r4 = BitVec.ofNat 32 (nibAt s.mem (State.addr p) i) := by
    simp (disch := decide) only [u₁₂.gpr, dpVal, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other,
      u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, e4,
      u₄.other, u₃.other, u₂.other, u₁.other, h11, cf.2]
    exact nibble_fact _ v_lt _ (Nat.mod_lt _ (by decide))
  have g9 : s₁₂.gpr .r9 = 0 := by
    simp (disch := decide) only [u₁₂.other, u₁₁.other, u₁₀.other, u₉.other, u₈.other, u₇.gpr]
  have r12 : Rest [.r2, .r3, .r4, .r5, .r6, .r9, .r12] s s₁₂ :=
    (r3.mono (by decide)).trans ((u₄.rest (by decide)).trans ((u₅.rest (by decide)).trans
      ((u₆.rest (by decide)).trans ((u₇.rest (by decide)).trans ((u₈.rest (by decide)).trans
      ((u₉.rest (by decide)).trans ((u₁₀.rest (by decide)).trans ((u₁₁.rest (by decide)).trans
      (u₁₂.rest (by decide))))))))))
  have m12 : s₁₂.mem = s.mem := by
    rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, m3]
  -- The sign and the magnitude.
  have sf := sign_fact _ (nibAt_lt s.mem (State.addr p) i)
  refine wp_dp (op2_imm (by decide)) fun s₁₃ u₁₃ => wp_mov (op2_lsr (by decide)) fun s₁₄ u₁₄ =>
    wp_dp (op2_reg _ _) fun s₁₅ u₁₅ => ?_
  have r15 : Rest [.r2, .r3, .r4, .r5, .r6, .r9, .r12] s s₁₅ :=
    r12.trans ((u₁₃.rest (by decide)).trans ((u₁₄.rest (by decide)).trans (u₁₅.rest (by decide))))
  refine str0_ok (hc.of_rest r15 (by decide)) (by decide)
      fun s₁₆ u₁₆ => wp_dp (op2_reg _ _) fun s₁₇ u₁₇ => wp_dp (op2_reg _ _) fun s₁₈ u₁₈ => ?_
  have g15 : s₁₅.gpr .r5 = maskB (decide (nibAt s.mem (State.addr p) i < 8)) := by
    simp (disch := decide) only [u₁₅.gpr, dpVal, u₁₄.gpr, u₁₄.other, u₁₃.gpr,
      u₁₃.other, g9, e12]
    exact sf.1
  have g18 : s₁₈.gpr .r10 = BitVec.ofNat 32 (magOf (nibAt s.mem (State.addr p) i)) := by
    simp (disch := decide) only [u₁₈.gpr, dpVal, u₁₇.gpr, u₁₇.other, u₁₆.gpr, g15,
      u₁₅.other, u₁₄.other, u₁₃.gpr, e12]
    exact sf.2
  have g9' : s₁₈.gpr .r9 = 0 := by
    simp (disch := decide) only [u₁₈.other, u₁₇.other, u₁₆.gpr, u₁₅.other, u₁₄.other, u₁₃.other, g9]
  have m18 : s₁₈.mem = s.mem.writeW (State.addr b + BitVec.ofNat 64 SGN)
      (maskB (decide (nibAt s.mem (State.addr p) i < 8))) := by
    rw [u₁₈.mem, u₁₇.mem, u₁₆.mem, g15, u₁₅.mem, u₁₄.mem, u₁₃.mem, m12]
  have r18 : Rest [.r2, .r3, .r4, .r5, .r6, .r9, .r10, .r12] s s₁₈ :=
    (r15.mono (by decide)).trans ((u₁₆.rest _).trans ((u₁₇.rest (by decide)).trans
      (u₁₈.rest (by decide))))
  refine WP.block_nil (WP.mono (combMasks_ok (magOf_le (nibAt_lt _ _ _)) g9' g18) fun t h => ?_)
  refine ⟨(r18.mono (by decide)).trans (h.rest.mono (by decide)), h.mem.trans m18,
    (h.rest.gpr _ (by decide)).trans g9', (h.rest.gpr _ (by decide)).trans g18, h.masks⟩

end VG.Proof.Ed25519.Arm

namespace VG.Proof.Ed25519.Arm

open VG VG.Arm VG.Impl.Ed25519 VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

/-- The comb's tables at `T` in `s`: not wrapping around, readable, and their words. -/
structure TblAt (s : State) (T : BitVec 32) : Prop where
  fit : T.toNat + 98304 ≤ 2 ^ 32
  rd : InRegions (s.rd ++ s.wr) (State.addr T) 98304
  words : ∀ j < 64 * 192, s.mem.readW (State.addr T + BitVec.ofNat 64 (8 * j)) 64 = combWord j

/-- The region of the comb's tables at `T`. -/
abbrev TBL (T : BitVec 32) : Region := ⟨State.addr T, 98304⟩

theorem TblAt.of_frame {s t : State} {T : BitVec 32} {L : List Region} (h : TblAt s T)
    (hr : t.rd ++ t.wr = s.rd ++ s.wr) (hf : Frame L s.mem t.mem) (hd : ∀ r ∈ L, (TBL T).Disjoint r) :
    TblAt t T :=
  ⟨h.fit, hr ▸ h.rd, fun j hj => by
    rw [← h.words j hj]
    refine hf.readW (r := TBL T) ?_ hd (by decide)
    simp only [Region.Contains]
    rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega⟩

theorem combLimb_lt (i m c k : Nat) : combLimb i m c k < 2 ^ 16 := Nat.mod_lt _ (by decide)

theorem combLimbAt_lt (q : Nat) : combLimbAt q < 2 ^ 16 := combLimb_lt _ _ _ _

/-- Word `q` (of 32 bits) of the tables. -/
theorem tbl_read {m : Mem} {T : Addr}
    (hw : ∀ j < 64 * 192, m.readW (T + BitVec.ofNat 64 (8 * j)) 64 = combWord j) {q : Nat}
    (hq : q < 64 * 384) : m.readW (T + BitVec.ofNat 64 (4 * q)) 32 = BitVec.ofNat 32 (combLimbAt q) := by
  have lo := combLimbAt_lt (2 * (q / 2))
  have hi := combLimbAt_lt (2 * (q / 2) + 1)
  have w := hw (q / 2) (by omega)
  rcases Nat.mod_two_eq_zero_or_one q with h | h
  · have e : 4 * q = 8 * (q / 2) := by omega
    rw [e, Mem.readW_lo32 w, combWord]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [show 2 * (q / 2) = q by omega] at lo ⊢
    omega
  · have e : T + BitVec.ofNat 64 (4 * q) = T + BitVec.ofNat 64 (8 * (q / 2)) + BitVec.ofNat 64 4 := by
      rw [Offset.add_add]; congr 2; omega
    rw [e, Mem.readW_hi32 w, combWord]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [show 2 * (q / 2) + 1 = q by omega] at hi ⊢
    omega

/-- Limb `k` of coordinate `c` of entry `a` of table `i`: the identity's `[1, 1, 0]` for
`a = 0`. -/
def selLimb (i a c k : Nat) : Nat := (combCoord (combCached64 i a) c).val / 2 ^ (16 * k) % 2 ^ 16

theorem selLimb_lt (i a c k : Nat) : selLimb i a c k < 2 ^ 16 := Nat.mod_lt _ (by decide)

theorem selLimb_succ (i m c k : Nat) : selLimb i (m + 1) c k = combLimb i m c k := rfl

private theorem selLimb_zero_fact : ∀ c < 3, ∀ k < 16,
    (combCoord ⟨1, 1, 0, 2⟩ c).val / 2 ^ (16 * k) % 2 ^ 16 = if c < 2 ∧ k = 0 then 1 else 0 := by
  decide

theorem selLimb_zero (i c k : Nat) (hc : c < 3) (hk : k < 16) :
    selLimb i 0 c k = if c < 2 ∧ k = 0 then 1 else 0 := by
  have e : combCached64 i 0 = ⟨1, 1, 0, 2⟩ := by
    unfold combCached64 combCached combCached16; split <;> rfl
  rw [selLimb, e]
  exact selLimb_zero_fact c hc k hk

private theorem identity_fact : ∀ a ≤ 8,
    ((((((((maskB (decide (a = 1)) ||| maskB (decide (a = 2))) ||| maskB (decide (a = 3))) |||
      maskB (decide (a = 4))) ||| maskB (decide (a = 5))) ||| maskB (decide (a = 6))) |||
      maskB (decide (a = 7))) ||| maskB (decide (a = 8))) &&& (1 : BitVec 32)) ^^^ (1 : BitVec 32) =
      if a = 0 then 1 else 0 := by decide

private theorem cand_fact : ∀ a ≤ 8, ∀ m < 8, ∀ x w : BitVec 32,
    x ||| (w &&& maskB (decide (a = m + 1))) = if a = m + 1 then x ||| w else x := by
  intro a _ m _ x w
  by_cases h : a = m + 1
  · rw [ite_eq_left h, maskB, ite_eq_left (decide_eq_true h), BitVec.and_allOnes]
  · rw [ite_eq_right h, maskB, ite_eq_right (by simp [h])]
    show x ||| (w &&& 0#32) = x
    rw [BitVec.and_zero, BitVec.or_zero]

private theorem maskReg_r10 : ∀ m < 8, maskReg (m + 1) ≠ .r10 := by decide

private theorem maskReg_out : ∀ m < 8, maskReg (m + 1) ∉ [Reg.r9, .r10] := by decide

/-- The registers and table the selection reads. -/
structure SelCtx (b T : BitVec 32) (i a : Nat) (s : State) : Prop where
  ctx : Ctx b s
  r12 : s.gpr .r12 = T + BitVec.ofNat 32 (1536 * i)
  masks : ∀ k < 8, s.gpr (maskReg (k + 1)) = maskB (decide (a = k + 1))
  tbl : TblAt s T
  apart : (TBL T).Disjoint ⟨State.addr b, 8192⟩

theorem SelCtx.of_rest {b T : BitVec 32} {i a : Nat} {s t : State} (h : SelCtx b T i a s)
    (hr : Rest [.r9, .r10] s t) (hf : Frame [⟨State.addr b, 8192⟩] s.mem t.mem) : SelCtx b T i a t :=
  ⟨h.ctx.of_rest hr (by decide), (hr.gpr _ (by decide)).trans h.r12,
    fun k hk => (hr.gpr _ (maskReg_out k hk)).trans (h.masks k hk),
    h.tbl.of_frame (by rw [hr.rd, hr.wr]) hf (by simpa only [List.mem_singleton, forall_eq] using h.apart),
    h.apart⟩

theorem selectCand_ok {b T : BitVec 32} {i a c k m : Nat} {s : State} (h : SelCtx b T i a s)
    (hi : i < 64) (hc : c < 3) (hk : k < 16) (hm : m < 8) :
    WP isa (.block (selectCand (192 * m + 64 * c + 4 * k) m)) s fun t =>
      t.gpr .r9 = s.gpr .r9 ||| (BitVec.ofNat 32 (combLimb i m c k) &&& maskB (decide (a = m + 1))) ∧
      Rest [.r9, .r10] s t ∧ t.mem = s.mem := by
  have fit := h.tbl.fit
  have q_lt : 384 * i + 48 * m + 16 * c + k < 64 * 384 := by omega
  have e : 1536 * i + (192 * m + 64 * c + 4 * k) = 4 * (384 * i + 48 * m + 16 * c + k) := by omega
  have ha : State.addr (s.gpr .r12 + BitVec.ofNat 32 (192 * m + 64 * c + 4 * k)) =
      State.addr T + BitVec.ofNat 64 (4 * (384 * i + 48 * m + 16 * c + k)) := by
    rw [h.r12, BitVec.add_assoc, ← BitVec.ofNat_add, e, addr_add (by omega)]
  have hv := tbl_read h.tbl.words q_lt
  have lv : combLimbAt (384 * i + 48 * m + 16 * c + k) = combLimb i m c k := by
    unfold combLimbAt; congr 1 <;> omega
  unfold selectCand
  refine wp_ldr (by omega) ha (CallLay.inRegions_sub h.tbl.rd (by omega) (by decide)) fun s₁ u₁ =>
    wp_dp (op2_reg _ _) fun s₂ u₂ => wp_dp (op2_reg _ _) fun s₃ u₃ => WP.block_nil ?_
  have mm := h.masks m hm
  have hne : maskReg (m + 1) ≠ .r10 := maskReg_r10 m hm
  refine ⟨?_, (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans (u₃.rest (by decide))),
    by rw [u₃.mem, u₂.mem, u₁.mem]⟩
  rw [u₃.gpr, dpVal, u₂.other _ (by decide), u₁.other _ (by decide), u₂.gpr, dpVal, u₁.gpr, hv, lv,
    u₁.other _ hne, mm]

theorem selectLimb_ok {b T : BitVec 32} {i a c k : Nat} {s : State} (h : SelCtx b T i a s)
    (hi : i < 64) (ha : a ≤ 8) (hc : c < 3) (hk : k < 16) :
    WP isa (.block (selectLimb c k)) s fun t =>
      Rest [.r9, .r10] s t ∧
      t.mem = s.mem.writeW (State.addr b + BitVec.ofNat 64 (64 + 64 * (4 + c) + 4 * k))
        (BitVec.ofNat 32 (selLimb i a c k)) := by
  unfold selectLimb
  rw [WP.block_append_iff, WP.block_append_iff]
  -- The start: the identity's limb.
  have start : WP isa (.block (if c < 2 ∧ k = 0 then identityLimb else [.mov .r9 (.imm 0)])) s fun t =>
      t.gpr .r9 = BitVec.ofNat 32 (if a = 0 ∧ c < 2 ∧ k = 0 then 1 else 0) ∧ Rest [.r9, .r10] s t ∧
        t.mem = s.mem := by
    split
    · rename_i hck
      unfold identityLimb
      refine wp_dp (op2_reg _ _) fun s₁ u₁ => wp_dp (op2_reg _ _) fun s₂ u₂ =>
        wp_dp (op2_reg _ _) fun s₃ u₃ => wp_dp (op2_reg _ _) fun s₄ u₄ =>
        wp_dp (op2_reg _ _) fun s₅ u₅ => wp_dp (op2_reg _ _) fun s₆ u₆ =>
        wp_dp (op2_reg _ _) fun s₇ u₇ => wp_dp (op2_imm (by decide)) fun s₈ u₈ =>
        wp_dp (op2_imm (by decide)) fun s₉ u₉ => WP.block_nil ?_
      refine ⟨?_, (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans ((u₃.rest (by decide)).trans
        ((u₄.rest (by decide)).trans ((u₅.rest (by decide)).trans ((u₆.rest (by decide)).trans
        ((u₇.rest (by decide)).trans ((u₈.rest (by decide)).trans (u₉.rest (by decide))))))))), by
          rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
      have m := h.masks
      simp (disch := decide) only [u₉.gpr, dpVal, u₈.gpr, u₇.gpr, u₆.gpr, u₆.other, u₅.gpr,
        u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
      rw [show Reg.r1 = maskReg (0 + 1) from rfl, show Reg.r2 = maskReg (1 + 1) from rfl,
        show Reg.r3 = maskReg (2 + 1) from rfl, show Reg.r4 = maskReg (3 + 1) from rfl,
        show Reg.r5 = maskReg (4 + 1) from rfl, show Reg.r6 = maskReg (5 + 1) from rfl,
        show Reg.r7 = maskReg (6 + 1) from rfl, show Reg.r8 = maskReg (7 + 1) from rfl,
        m 0 (by decide), m 1 (by decide), m 2 (by decide), m 3 (by decide), m 4 (by decide),
        m 5 (by decide), m 6 (by decide), m 7 (by decide), identity_fact a ha]
      by_cases a0 : a = 0 <;> simp [a0, hck]
    · rename_i hck
      refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => WP.block_nil ⟨?_, u₁.rest (by decide), u₁.mem⟩
      rw [u₁.gpr]
      simp only [hck, and_false, ↓reduceIte]
      rfl
  refine WP.mono start fun s₀ ⟨g₀, r₀, m₀⟩ => ?_
  -- The candidates.
  have h₀ := h.of_rest r₀ (by rw [m₀]; exact Frame.refl _ _)
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n t => SelCtx b T i a t ∧ Rest [.r9, .r10] s₀ t ∧ t.mem = s₀.mem ∧
      t.gpr .r9 = BitVec.ofNat 32 (if 1 ≤ a ∧ a ≤ n then selLimb i a c k else
        if a = 0 ∧ c < 2 ∧ k = 0 then 1 else 0))
    (fun n t hn ⟨ht, rt, mt, gt⟩ => ?_) 8 (Nat.le_refl _) s₀
    ⟨h₀, Rest.refl _ _, rfl, by rw [g₀, ite_eq_right (show ¬(1 ≤ a ∧ a ≤ 0) by omega)]⟩) fun s₁ ⟨h₁, r₁, m₁, g₁⟩ => ?_
  · refine WP.mono (selectCand_ok ht hi hc hk hn) fun u ⟨gu, ru, mu⟩ =>
      ⟨ht.of_rest ru (by rw [mu]; exact Frame.refl _ _), rt.trans ru, mu.trans mt, ?_⟩
    rw [gu, gt, cand_fact a ha n hn]
    by_cases e : a = n + 1
    · subst e
      rw [ite_eq_left rfl, ite_eq_right (show ¬(1 ≤ n + 1 ∧ n + 1 ≤ n) by omega),
        ite_eq_right (show ¬(n + 1 = 0 ∧ c < 2 ∧ k = 0) by omega),
        ite_eq_left (show 1 ≤ n + 1 ∧ n + 1 ≤ n + 1 from ⟨by omega, Nat.le_refl _⟩), selLimb_succ]
      exact BitVec.zero_or
    · rw [ite_eq_right e]
      congr 1
      by_cases h1 : 1 ≤ a ∧ a ≤ n
      · rw [ite_eq_left h1, ite_eq_left (show 1 ≤ a ∧ a ≤ n + 1 from ⟨h1.1, by omega⟩)]
      · rw [ite_eq_right h1, ite_eq_right (show ¬(1 ≤ a ∧ a ≤ n + 1) by omega)]
  -- The store.
  refine str0_ok h₁.ctx (by omega) fun t ut => WP.block_nil ⟨r₀.trans (r₁.trans (ut.rest _)), ?_⟩
  have sel : (if 1 ≤ a ∧ a ≤ 8 then selLimb i a c k else if a = 0 ∧ c < 2 ∧ k = 0 then 1 else 0) =
      selLimb i a c k := by
    rcases Nat.eq_zero_or_pos a with a0 | apos
    · subst a0
      rw [ite_eq_right (show ¬(1 ≤ 0 ∧ 0 ≤ 8) by omega), selLimb_zero i c k hc hk]
      by_cases hck : c < 2 ∧ k = 0
      · rw [ite_eq_left ⟨rfl, hck⟩, ite_eq_left hck]
      · rw [ite_eq_right (fun h => hck h.2), ite_eq_right hck]
    · rw [ite_eq_left ⟨apos, ha⟩]
  rw [ut.mem, m₁, m₀, g₁, sel]

private theorem tbl_offset_fact : ∀ i < 64,
    ((1536 : BitVec 16).setWidth 32) * BitVec.ofNat 32 i = BitVec.ofNat 32 (1536 * i) := by
  decide +kernel

/-- The slots 4–6 the selection writes. -/
abbrev selR (b : BitVec 32) : Region := ⟨State.addr b + BitVec.ofNat 64 320, 192⟩

/-- The selection's invariant after `q` limbs. -/
structure SelInv (b T : BitVec 32) (i a : Nat) (s₀ : State) (q : Nat) (s : State) : Prop where
  sel : SelCtx b T i a s
  rest : Rest [.r9, .r10] s₀ s
  frame : Frame [selR b] s₀.mem s.mem
  limbs : ∀ q' < q, wd s.mem (State.addr b) (320 + 4 * q') = selLimb i a (q' / 16) (q' % 16)

theorem combSelect_ok {b T : BitVec 32} {i a : Nat} {s : State} (hc : Ctx b s) (hi : i < 64)
    (ha : a ≤ 8) (h11 : s.gpr .r11 = BitVec.ofNat 32 i)
    (masks : ∀ k < 8, s.gpr (maskReg (k + 1)) = maskB (decide (a = k + 1)))
    (hT : TblAt s T) (hsym : s.syms combSym = T) (apart : (TBL T).Disjoint ⟨State.addr b, 8192⟩) :
    WP isa (.block combSelect) s fun t =>
      Rest [.r9, .r10, .r12] s t ∧ Frame [selR b] s.mem t.mem ∧
      ∀ q < 48, wd t.mem (State.addr b) (320 + 4 * q) = selLimb i a (q / 16) (q % 16) := by
  unfold combSelect tblAddr
  simp only [List.cons_append, List.nil_append]
  refine WP.cons (s' := s.setReg .r12 (s.syms combSym)) rfl ?_
  have u₁ := Upd.setReg s .r12 (s.syms combSym)
  refine wp_movw fun s₂ u₂ => wp_mul fun s₃ u₃ => wp_dp (op2_reg _ _) fun s₄ u₄ => ?_
  have r4 : Rest [.r10, .r12] s s₄ := (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans
    ((u₃.rest (by decide)).trans (u₄.rest (by decide))))
  have m4 : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have g12 : s₄.gpr .r12 = T + BitVec.ofNat 32 (1536 * i) := by
    rw [u₄.gpr, dpVal, u₃.gpr, u₂.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hsym,
      u₂.other _ (by decide), u₁.other _ (by decide), h11, tbl_offset_fact i hi]
  have h₄ : SelCtx b T i a s₄ :=
    ⟨hc.of_rest r4 (by decide), g12, fun k hk => (r4.gpr _ (by revert k; decide)).trans (masks k hk),
      hT.of_frame (by rw [r4.rd, r4.wr]) (L := []) (by rw [m4]; exact Frame.refl _ _) (by simp),
      apart⟩
  refine WP.mono (wp_range_flatMap (M := isa) (SelInv b T i a s₄) (fun q t hq h => ?_) 48
    (Nat.le_refl _) s₄ ⟨h₄, Rest.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun t h => ⟨(r4.mono (by decide)).trans (h.rest.mono (by decide)), by rw [← m4]; exact h.frame,
      h.limbs⟩
  have fit := h.sel.ctx.fit
  have e : 64 + 64 * (4 + q / 16) + 4 * (q % 16) = 320 + 4 * q := by omega
  refine WP.mono (selectLimb_ok h.sel hi ha (by omega) (Nat.mod_lt _ (by decide))) fun u ⟨ru, mu⟩ => ?_
  rw [e] at mu
  have fw : Frame [selR b] t.mem u.mem := by
    rw [mu]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains (State.addr b) (by omega) (by omega) (by omega))
  refine ⟨h.sel.of_rest ru (fw.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub_base (State.addr b) (by decide)⟩),
    h.rest.trans ru, h.frame.trans fw, fun q' hq' => ?_⟩
  rw [mu]
  rcases Nat.lt_succ_iff_lt_or_eq.mp hq' with hq' | rfl
  · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]
    exact h.limbs q' hq'
  · rw [wd_write_self, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (selLimb_lt i a _ _) (by decide))]

end VG.Proof.Ed25519.Arm

namespace VG.Proof.Ed25519.Arm

open VG VG.Arm VG.Impl.Ed25519 VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm VG.Proof.Ed25519 Edwards

theorem maskB_eq (b : Bool) : maskB b = 0 - BitVec.ofNat 32 b.toNat := by cases b <;> decide

theorem magOf_eq (n : Nat) : magOf n = mag n := rfl

/-! ## Limbs and slots -/

theorem val16_digits16 (v : Nat) : ∀ n, val16 (fun k => v / 2 ^ (16 * k) % 2 ^ 16) n = v % 2 ^ (16 * n)
  | 0 => by simp [val16, Nat.mod_one]
  | n + 1 => by
    rw [val16_succ, val16_digits16 v n, show 16 * (n + 1) = 16 * n + 16 by omega, Nat.pow_add,
      Nat.mod_mul]

/-- The selected entry's coordinate `c` in slot `4 + c`, with limbs below `2¹⁶`. -/
theorem sel_env {m : Mem} {b : BitVec 32} {i a : Nat}
    (h : ∀ q < 48, wd m (State.addr b) (320 + 4 * q) = selLimb i a (q / 16) (q % 16))
    (sl : Slot) (c : Nat) (hc : c < 3) (hs : sl.val = 4 + c) :
    env m b sl = combCoord (combCached64 i a) c ∧ Lim m (State.addr b) (offset sl) := by
  have hl : ∀ k < 16, limb m (State.addr b) (offset sl) k = selLimb i a c k := fun k hk => by
    have e := h (16 * c + k) (by omega)
    rw [show (16 * c + k) / 16 = c by omega, show (16 * c + k) % 16 = k by omega,
      show 320 + 4 * (16 * c + k) = offset sl + 4 * k by simp only [offset, hs]; omega] at e
    exact e
  refine ⟨?_, fun k hk => by rw [hl k hk]; exact selLimb_lt _ _ _ _⟩
  have hv : V m (State.addr b) (offset sl) = (combCoord (combCached64 i a) c).val := by
    rw [V, val16_congr hl]
    unfold selLimb
    rw [val16_digits16, Nat.mod_eq_of_lt (Nat.lt_trans (combCoord (combCached64 i a) c).isLt (by decide))]
  simp only [env, FS, hv, VG.Proof.X25519.toFe_self]

/-- The slots apart from `R` are as they were. -/
theorem env_frame {m m' : Mem} {b : BitVec 32} {R : Region} (hf : Frame [R] m m') (sl : Slot)
    (hd : ∀ k < 16, (⟨State.addr b + BitVec.ofNat 64 (offset sl + 4 * k), 4⟩ : Region).Disjoint R) :
    env m' b sl = env m b sl ∧ (Lim m (State.addr b) (offset sl) → Lim m' (State.addr b) (offset sl)) := by
  have hl : ∀ k < 16, limb m' (State.addr b) (offset sl) k = limb m (State.addr b) (offset sl) k :=
    fun k hk => wd_frame hf fun r hr => by rw [List.mem_singleton.mp hr]; exact hd k hk
  exact ⟨by simp only [env, FS, V, val16_congr hl], fun h k hk => by rw [hl k hk]; exact h k hk⟩

/-- The region `[d, d + n)` of the workspace is apart from slot `sl` unless they meet. -/
theorem slot_apart {b : BitVec 32} (sl : Slot) {d n : Nat} (h : d + n ≤ offset sl ∨ offset sl + 64 ≤ d)
    (hn : d + n ≤ 8192) :
    ∀ k < 16, (⟨State.addr b + BitVec.ofNat 64 (offset sl + 4 * k), 4⟩ : Region).Disjoint
      ⟨State.addr b + BitVec.ofNat 64 d, n⟩ := fun k hk =>
  Offset.disjoint _ (by omega) (by simp only [offset] at h ⊢; have := sl.isLt; omega) (by omega)

/-- Nibble `i` of the scalar's bytes is the decoded scalar's. -/
theorem nibAt_eq (m : Mem) (p : Addr) {i : Nat} (hi : i < 64) :
    nibAt m p i = nib (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p 32)) i := by
  rw [nib, decodeLE_nibble, nibbleOf, nibAt]
  have hg : (Spec.Ed25519.bytesAt m p 32).getD (i / 2) 0 = m (p + BitVec.ofNat 64 (i / 2)) := by
    simp [Spec.Ed25519.bytesAt, List.getD_eq_getElem?_getD, show i / 2 < 32 by omega]
  rw [hg]
  have := (m (p + BitVec.ofNat 64 (i / 2))).isLt
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · rw [h, ite_eq_right (by decide), pow_zero, Nat.div_one]
  · rw [h, ite_eq_left rfl, pow_one]; omega

/-! ## The addition -/

/-- What `addAffineOps` computes, from the point's coordinates and the cached entry's. -/
def mixedResult (x y z t q₀ q₁ q₂ : Spec.X25519.Fe) : Spec.Ed25519.Point :=
  let a := (y - x) * q₀
  let b := (y + x) * q₁
  let c := t * q₂
  let dd := z + z
  ⟨(b - a) * (dd - c), (dd + c) * (b + a), (dd - c) * (dd + c), (b - a) * (b + a)⟩

theorem mixedResult_eq (p q : Spec.Ed25519.Point) (hz : q.Z = 1) :
    mixedResult p.X p.Y p.Z p.T (q.Y - q.X) (q.Y + q.X) (q.T * 2 * Spec.Ed25519.d) =
      Spec.Ed25519.pointAdd p q := by
  simp only [mixedResult, Spec.Ed25519.pointAdd, hz]
  congr 1 <;> grind

theorem addAffineOps_formula (e : Env) :
    point (evalOps addAffineOps e) 0 1 2 3 = mixedResult (e 0) (e 1) (e 2) (e 3) (e 4) (e 5) (e 6) :=
  rfl

/-! ## The step -/

/-- The regions a step writes: the sign's mask and the field area. -/
abbrev stepRegions (b : BitVec 32) : List Region := [⟨State.addr b + BitVec.ofNat 64 56, 4⟩, FA b]

/-- What the loop never changes: where the scalar's copy is, and the tables. -/
structure CombEnv (s₀ : State) (b p T : BitVec 32) : Prop where
  hp : b + BitVec.ofNat 32 SCAL = p
  fit : p.toNat + 32 ≤ 2 ^ 32
  readable : ∀ k < 32, InRegions (s₀.rd ++ s₀.wr) (State.addr p + BitVec.ofNat 64 k) 1
  sep : ∀ r ∈ stepRegions b, (⟨State.addr p, 32⟩ : Region).Disjoint r
  tbl : TblAt s₀ T
  apart : (TBL T).Disjoint ⟨State.addr b, 8192⟩

/-- The loop's invariant, after `j` steps. -/
structure CombInv (s₀ : State) (b p T : BitVec 32) (S : Nat) (j : Nat) (s : State) : Prop where
  bound : j ≤ 64
  ctx : Ctx b s
  r11 : s.gpr .r11 = BitVec.ofNat 32 j
  lim : AllLim s.mem b
  zero : env s.mem b 21 = 0
  acc : Rep (point (env s.mem b) 0 1 2 3) ((((17 * combGVal : Nat) : ℤ) + digitSum64 S j) • baseAff)
  keep : PointKeep b s₀ s
  scalar : S = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr p) 32)
  syms : s.syms combSym = T

theorem stepRegions_keep {b : BitVec 32} {s t : State} (hr : Rest powersClob s t)
    (hf : Frame (stepRegions b) s.mem t.mem) : PointKeep b s t :=
  ⟨hr, hf.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.sub _ (by decide) (by decide)
    · exact Offset.sub _ (by decide) (by decide)⟩⟩

theorem stepRegions_ws {b : BitVec 32} {m m' : Mem} (hf : Frame (stepRegions b) m m') :
    Frame [⟨State.addr b, 8192⟩] m m' :=
  hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.sub_base _ (by decide)⟩

private theorem next_fact : ∀ j < 64, BitVec.ofNat 32 j + (1 : BitVec 32) = BitVec.ofNat 32 (j + 1) ∧
    (BitVec.ofNat 32 (j + 1) - (64 : BitVec 32) == 0) = decide (j + 1 = 64) := by decide

private theorem slot_cases : ∀ sl : Slot, sl.val = 4 ∨ sl.val = 5 ∨ sl.val = 6 ∨
    sl.val < 4 ∨ 7 ≤ sl.val := by decide

private theorem swap_low : ∀ i : Slot, (i.val < 4 ∨ 8 ≤ i.val) →
    swapSlot 4 5 true (swapSlot 6 7 true i) = i := by decide

/-- The negation's exchanges leave the slots outside 4–7 alone. -/
theorem swapNeg_low (sw : Bool) (e : Env) (i : Slot) (hi : i.val < 4 ∨ 8 ≤ i.val) :
    swapEnvs [(4, 5), (6, 7)] sw e i = e i := by
  cases sw
  · rfl
  · exact congrArg e (swap_low i hi)

theorem swapNeg_vals (sw : Bool) (e : Env) :
    swapEnvs [(4, 5), (6, 7)] sw e 4 = (if sw then e 5 else e 4) ∧
      swapEnvs [(4, 5), (6, 7)] sw e 5 = (if sw then e 4 else e 5) ∧
      swapEnvs [(4, 5), (6, 7)] sw e 6 = (if sw then e 7 else e 6) := by
  cases sw <;> exact ⟨rfl, rfl, rfl⟩

theorem combStep_ok {s₀ s : State} {b p T : BitVec 32} {S j : Nat} (E : CombEnv s₀ b p T)
    (h : CombInv s₀ b p T S j s) (hj : j < 64) :
    WP isa combStep s fun t => isa.eval .ne t = some (decide (j + 1 ≠ 64)) ∧
      CombInv s₀ b p T S (j + 1) t := by
  suffices H : WP isa combStep s fun t => t.syms = s.syms →
      isa.eval .ne t = some (decide (j + 1 ≠ 64)) ∧ CombInv s₀ b p T S (j + 1) t from
    WP.mono_syms H fun t k hs => k hs
  have nf := next_fact j hj
  have n_lt := nibAt_lt s.mem (State.addr p) j
  -- The scalar and the tables, as at the start.
  have ws₀ : Frame [⟨State.addr b, 8192⟩] s₀.mem s.mem := h.keep.frame.sub fun r hr =>
    ⟨_, List.mem_singleton_self _, by
      simp only [pointRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Offset.sub_base _ (by decide)⟩
  have hrr : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.keep.rest.rd, h.keep.rest.wr]
  have hT : TblAt s T := E.tbl.of_frame hrr ws₀ (by simpa only [List.mem_singleton, forall_eq] using E.apart)
  have hnib : nibAt s.mem (State.addr p) j = nib S j := by rw [nibAt_eq _ _ hj, ← h.scalar]
  -- The digit and the selection.
  rw [combStep]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono_syms (combDigit_ok h.ctx hj E.hp h.r11 E.fit (by rw [hrr]; exact E.readable _ (by omega)))
    fun u ⟨ru, mu, _, _, gm⟩ syu => ?_
  have fu : Frame [⟨State.addr b + BitVec.ofNat 64 56, 4⟩] s.mem u.mem := by
    rw [mu]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have cu := h.ctx.of_rest ru (by decide)
  have hTu : TblAt u T := hT.of_frame (by rw [ru.rd, ru.wr])
    (fu.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (show 56 + 4 ≤ 8192 by decide)⟩)
    (by simpa only [List.mem_singleton, forall_eq] using E.apart)
  refine WP.mono (combSelect_ok (a := magOf (nibAt s.mem (State.addr p) j)) cu hj
    (magOf_le n_lt) ((ru.gpr _ (by decide)).trans h.r11) gm hTu (by rw [syu]; exact h.syms) E.apart)
    fun v ⟨rv, fv, lv⟩ => ?_
  -- The slots after the selection.
  have envu : ∀ sl : Slot, env u.mem b sl = env s.mem b sl ∧ Lim u.mem (State.addr b) (offset sl) := fun sl =>
    let e := env_frame fu sl (slot_apart sl (by have := sl.isLt; simp only [offset]; omega) (by decide))
    ⟨e.1, e.2 (h.lim sl)⟩
  have envv : ∀ sl : Slot, (sl.val < 4 ∨ 7 ≤ sl.val) → env v.mem b sl = env s.mem b sl ∧
      Lim v.mem (State.addr b) (offset sl) := fun sl hs => by
    have e := env_frame fv sl (slot_apart sl (by simp only [offset]; have := sl.isLt; omega) (by decide))
    exact ⟨e.1.trans (envu sl).1, e.2 (envu sl).2⟩
  have ent : ∀ c < 3, ∀ sl : Slot, sl.val = 4 + c →
      env v.mem b sl = combCoord (combCached64 j (magOf (nibAt s.mem (State.addr p) j))) c ∧
        Lim v.mem (State.addr b) (offset sl) := fun c hc sl hs => sel_env lv sl c hc hs
  have limv : AllLim v.mem b := fun sl => by
    rcases slot_cases sl with h4 | h5 | h6 | hl | hh
    · exact (ent 0 (by decide) sl h4).2
    · exact (ent 1 (by decide) sl h5).2
    · exact (ent 2 (by decide) sl h6).2
    · exact (envv sl (.inl hl)).2
    · exact (envv sl (.inr hh)).2
  have cv := cu.of_rest rv (by decide)
  have sgn : v.mem.readW (State.addr b + BitVec.ofNat 64 SGN) 32 =
      maskB (decide (nibAt s.mem (State.addr p) j < 8)) := by
    rw [fv.readW (r := ⟨State.addr b + BitVec.ofNat 64 56, 4⟩) (Region.contains_self _ _)
      (by simp only [List.mem_singleton, forall_eq]; exact Offset.disjoint _ (by decide) (by decide) (by decide))
      (by decide), mu, Mem.readW_writeW_self32]
  -- The negation.
  refine WP.seq ?_
  rw [combNeg, List.singleton_append, WP.seq_iff]
  refine WP.mono (fieldCode_ok [.sub 7 21 6] cv limv) fun w ⟨kw, lw, ew⟩ => ?_
  have cw := kw.ctx cv
  refine ldr0_ok cw (by decide) fun x₀ ux => ?_
  have sgnw : w.mem.readW (State.addr b + BitVec.ofNat 64 SGN) 32 =
      maskB (decide (nibAt s.mem (State.addr p) j < 8)) := by
    rw [kw.frame.readW (r := ⟨State.addr b + BitVec.ofNat 64 56, 4⟩) (Region.contains_self _ _)
      (by simp only [List.mem_singleton, forall_eq]; exact Offset.disjoint _ (by decide) (by decide) (by decide))
      (by decide), sgn]
  have cx₀ := cw.of_rest (ux.rest (ws := [.r9]) (by decide)) (by decide)
  refine WP.mono (swapFields_ok cx₀ (by rw [ux.mem]; exact lw) [(4, 5), (6, 7)] (by decide)
    (sw := decide (nibAt s.mem (State.addr p) j < 8)) (by rw [ux.gpr, sgnw, maskB_eq]))
    fun x ⟨kx, lx, _, ex⟩ => ?_
  have cx := kx.ctx cx₀
  -- The addition.
  refine WP.seq (WP.mono (fieldCode_ok addAffineOps cx lx) fun y ⟨ky, ly, ey⟩ => ?_)
  have cy := ky.ctx cx
  -- The counter.
  refine wp_dp (op2_imm (by decide)) fun z₀ uz => wp_cmp (op2_imm (by decide)) fun z fz zz => WP.block_nil ?_
  have r11y : y.gpr .r11 = BitVec.ofNat 32 j := by
    rw [ky.rest.gpr _ (by decide), kx.rest.gpr _ (by decide), ux.other _ (by decide),
      kw.rest.gpr _ (by decide), rv.gpr _ (by decide), ru.gpr _ (by decide), h.r11]
  have r11z : z.gpr .r11 = BitVec.ofNat 32 (j + 1) := by
    rw [fz.gpr, uz.gpr, dpVal, r11y, nf.1]
  -- What the step changed.
  have restz : Rest powersClob s z :=
    (ru.mono (by decide)).trans ((rv.mono (by decide)).trans (kw.rest.mono (by decide) |>.trans
      ((ux.rest (ws := powersClob) (by decide)).trans ((kx.rest.mono (by decide)).trans
      ((ky.rest.mono (by decide)).trans ((uz.rest (ws := powersClob) (by decide)).trans
      (fz.rest _)))))))
  have memz : z.mem = y.mem := by rw [fz.mem, uz.mem]
  have fz' : Frame (stepRegions b) s.mem z.mem := by
    rw [memz]
    refine (fu.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]).trans ?_
    refine ((fv.sub fun r hr => ⟨FA b, by simp, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by decide) (by decide)⟩).trans ?_)
    refine (kw.frame.mono (by simp)).trans ?_
    have kxf := kx.frame
    rw [ux.mem] at kxf
    exact (kxf.mono (by simp)).trans (ky.frame.mono (by simp))
  have pk := stepRegions_keep restz fz'
  -- The entry's coordinates.
  obtain ⟨q, hq, hqz, hrq⟩ := combEntry64_ok j (nib S j) hj (nib_lt S j)
  rw [hnib] at ent sgn
  have e4 := (ent 0 (by decide) 4 rfl).1
  have e5 := (ent 1 (by decide) 5 rfl).1
  have e6 := (ent 2 (by decide) 6 rfl).1
  have e21 : env v.mem b 21 = 0 := (envv 21 (.inr (by decide))).1.trans h.zero
  have ex' : env x.mem b = swapEnvs [(4, 5), (6, 7)] (decide (nib S j < 8)) (env w.mem b) := by
    rw [ex, ux.mem, hnib]
  have w4 : env w.mem b 4 = env v.mem b 4 := by rw [ew]; rfl
  have w5 : env w.mem b 5 = env v.mem b 5 := by rw [ew]; rfl
  have w6 : env w.mem b 6 = env v.mem b 6 := by rw [ew]; rfl
  have w7 : env w.mem b 7 = env v.mem b 21 - env v.mem b 6 := by rw [ew]; rfl
  have hx : ∀ i : Slot, i.val < 4 → env x.mem b i = env s.mem b i := fun i hi => by
    rw [ex', swapNeg_low _ _ _ (.inl hi), ew,
      evalOps_unchanged _ _ _ (by
        simp only [List.mem_singleton, forall_eq, fieldDest]; intro e; subst e; exact absurd hi (by decide))]
    exact (envv i (.inl hi)).1
  have cq : env x.mem b 4 = q.Y - q.X ∧ env x.mem b 5 = q.Y + q.X ∧
      env x.mem b 6 = q.T * 2 * Spec.Ed25519.d := by
    obtain ⟨s4, s5, s6⟩ := swapNeg_vals (decide (nib S j < 8)) (env w.mem b)
    have c0 : ∀ p, combCoord p 0 = p.X := fun _ => rfl
    have c1 : ∀ p, combCoord p 1 = p.Y := fun _ => rfl
    have c2 : ∀ p, combCoord p 2 = p.Z := fun _ => rfl
    rw [c0, magOf_eq] at e4
    rw [c1, magOf_eq] at e5
    rw [c2, magOf_eq] at e6
    rw [ex', s4, s5, s6, w4, w5, w6, w7, e4, e5, e6, e21]
    have hc := congrArg (fun p => (p.X, p.Y, p.Z)) hq
    simp only [cache, Prod.mk.injEq] at hc
    by_cases hlt : nib S j < 8
    · simp only [hlt, decide_true, ↓reduceIte, negCached] at hc ⊢
      exact hc
    · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte] at hc ⊢
      exact hc
  refine fun hsz => ⟨?_, ⟨by omega, cy.of_rest ((uz.rest (ws := [.r11]) (by decide)).trans (fz.rest _)) (by decide), r11z,
    by rw [memz]; exact ly, ?_, ?_, h.keep.trans pk, ?_, ?_⟩⟩
  · rw [eval_ne, zz, uz.gpr, dpVal, r11y, nf.1, nf.2]
    simp
  · -- Slot 21 is still zero.
    rw [memz, ey, evalOps_unchanged _ _ _ (by simp only [addAffineOps, List.mem_cons,
      forall_eq_or_imp, fieldDest, List.not_mem_nil, false_implies, implies_true]; decide), ex']
    rw [swapNeg_low _ _ _ (.inr (by decide)), ew, evalOps_unchanged _ _ _ (by simp only [List.mem_singleton, forall_eq, fieldDest]; decide)]
    exact e21
  · -- The accumulator.
    rw [memz, ey, addAffineOps_formula, cq.1, cq.2.1, cq.2.2, hx 0 (by decide), hx 1 (by decide),
      hx 2 (by decide), hx 3 (by decide)]
    have e := mixedResult_eq (point (env s.mem b) 0 1 2 3) q hqz
    simp only [point] at e
    rw [e, digitSum64, ← add_assoc, add_smul]
    exact pointAdd_rep h.acc (by simpa only [sdig] using hrq)
  · rw [h.scalar]
    unfold Spec.Ed25519.bytesAt
    exact congrArg _ (List.map_congr_left fun n hn => (fz'.bytes (R := ⟨State.addr p, 32⟩) E.sep
      (by decide : 32 ≤ 2 ^ 64) (List.mem_range.mp hn)).symm)
  · rw [hsz]; exact h.syms

/-- The loop, from step `j₀ < 64` to the end. -/
theorem combSteps_ok {s₀ s : State} {b p T : BitVec 32} {S j₀ : Nat} (E : CombEnv s₀ b p T)
    (h : CombInv s₀ b p T S j₀ s) (hj₀ : j₀ < 64) :
    WP isa (.loop combStep .ne) s fun t => CombInv s₀ b p T S 64 t := by
  apply WP.loop (fun n t => CombInv s₀ b p T S (64 - n) t ∧ 0 < n ∧ n ≤ 64) (n := 64 - j₀)
  · intro n t ⟨ht, hn0, hn⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    refine WP.mono (combStep_ok E ht (by omega)) fun u ⟨ue, hu⟩ => ?_
    by_cases hk : k = 0
    · subst hk
      exact Or.inl ⟨by rw [ue]; rfl, hu⟩
    · refine Or.inr ⟨by rw [ue]; simp only [show 64 - (k + 1) + 1 ≠ 64 by omega, ne_eq,
        not_false_eq_true, decide_true], k, by omega, ?_, by omega, by omega⟩
      rw [show 64 - k = 64 - (k + 1) + 1 by omega]; exact hu
  · exact ⟨by rw [show 64 - (64 - j₀) = j₀ by omega]; exact h, by omega, by omega⟩

/-! ## The scalar's copy -/

/-- The scalar's copy in the workspace. -/
abbrev scalR (b : BitVec 32) : Region := ⟨State.addr b + BitVec.ofNat 64 SCAL, 32⟩

private theorem byte_rt (x : BitVec 8) : (x.setWidth 32).setWidth 8 = x := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_setWidth]
  omega_arith

theorem combCopy_ok {s : State} {b P : BitVec 32} (hc : Ctx b s) (hp : s.gpr .r12 = P)
    (hfit : P.toNat + 32 ≤ 2 ^ 32)
    (hr : ∀ k < 32, InRegions (s.rd ++ s.wr) (State.addr P + BitVec.ofNat 64 k) 1)
    (hsep : (⟨State.addr P, 32⟩ : Region).Disjoint (scalR b)) :
    WP isa (.block combCopy) s fun t => Rest [.r1] s t ∧ Frame [scalR b] s.mem t.mem ∧
      ∀ k < 32, t.mem (State.addr b + BitVec.ofNat 64 (SCAL + k)) =
        s.mem (State.addr P + BitVec.ofNat 64 k) := by
  have hfb := hc.fit
  have src : ∀ k < 32, ∀ m : Mem, Frame [scalR b] s.mem m →
      m (State.addr P + BitVec.ofNat 64 k) = s.mem (State.addr P + BitVec.ofNat 64 k) := fun k hk m hf =>
    hf.bytes (R := ⟨State.addr P, 32⟩) (by simpa only [List.mem_singleton, forall_eq] using hsep)
      (show (32 : Nat) ≤ 2 ^ 64 by decide) hk
  refine wp_range_flatMap (M := isa) (fun (k : Nat) (t : State) => Rest [.r1] s t ∧ Frame [scalR b] s.mem t.mem ∧
      ∀ i < k, t.mem (State.addr b + BitVec.ofNat 64 (SCAL + i)) = s.mem (State.addr P + BitVec.ofNat 64 i))
    (fun (k : Nat) (t : State) hk ⟨rt, ft, ct⟩ => ?_) 32 le_rfl s
    ⟨Rest.refl _ _, Frame.refl _ _, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  refine wp_ldrb (a := State.addr P + BitVec.ofNat 64 k) (by omega)
    (by rw [rt.gpr _ (by decide), hp]; exact addr_add (by omega))
    (by rw [rt.rd, rt.wr]; exact hr k hk) fun t₁ u₁ => ?_
  refine wp_strb (a := State.addr b + BitVec.ofNat 64 (SCAL + k)) (by simp only [SCAL]; omega)
    (by rw [u₁.other _ (by decide), rt.gpr _ (by decide), hc.r0]; exact addr_add (by simp only [SCAL]; omega))
    (by rw [u₁.wr, rt.wr]; exact in_base hc.wr (by simp only [SCAL]; omega) (by simp only [SCAL]; omega))
    fun t₂ u₂ => WP.block_nil ?_
  have m2 : t₂.mem = t.mem.writeW (State.addr b + BitVec.ofNat 64 (SCAL + k))
      (t.mem (State.addr P + BitVec.ofNat 64 k)) := by
    rw [u₂.mem, u₁.gpr, u₁.mem, byte_rt]
  refine ⟨rt.trans ((u₁.rest (by decide)).trans (u₂.rest _)), ?_, fun i hi => ?_⟩
  · rw [m2]
    exact ft.writeW (List.mem_singleton_self _) _
      (Offset.contains _ (by simp only [SCAL]; omega) (by simp only [SCAL]; omega) (by simp only [SCAL]; omega))
  · rw [m2, VG.WriteBytes.writeW8_apply]
    by_cases hik : i = k
    · subst hik
      rw [ite_eq_left rfl]
      exact src i hk _ ft
    · have hne : State.addr b + BitVec.ofNat 64 (SCAL + i) ≠ State.addr b + BitVec.ofNat 64 (SCAL + k) :=
        fun he => Offset.disjoint (State.addr b) (d := SCAL + i) (n := 1) (e := SCAL + k) (k := 1)
          (by omega) (by simp only [SCAL]; omega) (by simp only [SCAL]; omega) _
          (Region.contains_self _ _) (he ▸ Region.contains_self _ _)
      rw [ite_eq_right hne]
      exact ct i (by omega)

/-! ## The start -/

private def combStartCheck (p : Spec.Ed25519.Point) : Bool :=
  combStart.X * p.Z == p.X && combStart.Y * p.Z == p.Y && p.Z != 0

private theorem combStart_check :
    combStartCheck (Spec.Ed25519.pointMul (17 * combGVal) Spec.Ed25519.basePoint) = true := by
  decide +kernel

theorem combStart_ok : Rep combStart ((17 * combGVal) • baseAff) := by
  have hp := pointMul_rep (17 * combGVal) basePoint_rep
  have hc := combStart_check
  simp only [combStartCheck, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
  obtain ⟨⟨hx, hy⟩, _⟩ := hc
  exact combPt_rep (q := combStartAff) hp hx hy

/-! ## The multiplication -/

theorem combPrepare_ok {s : State} {b P T : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b)
    (hp : s.gpr .r12 = P) (hfit : P.toNat + 32 ≤ 2 ^ 32)
    (hr : ∀ k < 32, InRegions (s.rd ++ s.wr) (State.addr P + BitVec.ofNat 64 k) 1)
    (hsep : (⟨State.addr P, 32⟩ : Region).Disjoint ⟨State.addr b, 8192⟩)
    (hT : TblAt s T) (hsym : s.syms combSym = T) (apart : (TBL T).Disjoint ⟨State.addr b, 8192⟩) :
    WP isa combPrepare s fun w => PointKeep b s w ∧ CombEnv w b (b + BitVec.ofNat 32 SCAL) T ∧
      CombInv w b (b + BitVec.ofNat 32 SCAL) T
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr P) 32)) 0 w := by
  have hfb := hc.fit
  have sub : (scalR b).Sub ⟨State.addr b, 8192⟩ := Offset.sub_base _ (by decide)
  rw [combPrepare]
  refine WP.seq (WP.mono_syms (combCopy_ok hc hp hfit hr (hsep.sub_right sub)) fun u ⟨ru, fu, cu⟩ syu => ?_)
  have ku : PointKeep b s u := PointKeep.of_small ru (by decide) fu (by decide) (by decide)
  have hcu := ku.ctx hc
  have lu : AllLim u.mem b := fun sl =>
    (env_frame fu sl (slot_apart sl (.inr (by simp only [offset, SCAL]; have := sl.isLt; omega))
      (by decide))).2 (hl sl)
  rw [combInit, WP.seq_iff]
  refine WP.mono_syms (fieldCode_ok _ hcu lu) fun v ⟨kv, lv, ev⟩ syv => ?_
  refine WP.mono_syms (Q := fun w => Upd v w .r11 ((0 : BitVec 16).setWidth 32))
    (wp_movw fun w uw => WP.block_nil uw) fun w uw syw => ?_
  -- Where the loop starts.
  let p := b + BitVec.ofNat 32 SCAL
  have hpa : State.addr p = State.addr b + BitVec.ofNat 64 SCAL := addr_add (by simp only [SCAL]; omega)
  have hpn : p.toNat = b.toNat + SCAL := by
    simp only [p, BitVec.toNat_add, BitVec.toNat_ofNat, SCAL]
    rw [Nat.mod_eq_of_lt (by omega : 2048 < 2 ^ 32), Nat.mod_eq_of_lt (by omega)]
  have frw : Frame [FA b] u.mem w.mem := by rw [uw.mem]; exact kv.frame
  have tu : TblAt u T := hT.of_frame (by rw [ru.rd, ru.wr]) fu fun r hr => by
    rw [List.mem_singleton.mp hr]; exact apart.sub_right sub
  have tw : TblAt w T := tu.of_frame (by rw [uw.rd, uw.wr, kv.rest.rd, kv.rest.wr]) frw fun r hr => by
    rw [List.mem_singleton.mp hr]; exact apart.sub_right (Offset.sub_base _ (by decide))
  have scal : Spec.Ed25519.bytesAt w.mem (State.addr p) 32 = Spec.Ed25519.bytesAt s.mem (State.addr P) 32 := by
    unfold Spec.Ed25519.bytesAt
    refine List.map_congr_left fun n hn => ?_
    have hn := List.mem_range.mp hn
    rw [hpa, frw.bytes (R := ⟨State.addr b + BitVec.ofNat 64 SCAL, 32⟩)
      (by simp only [List.mem_singleton, forall_eq]
          exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide))
      (show (32 : Nat) ≤ 2 ^ 64 by decide) hn, Offset.add_add]
    exact cu n hn
  have E : CombEnv w b p T := by
    refine ⟨rfl, by rw [hpn]; simp only [SCAL]; omega, fun k hk => ?_, ?_, tw, apart⟩
    · rw [hpa, Offset.add_add, uw.rd, uw.wr, kv.rest.rd, kv.rest.wr]
      have hw : (⟨State.addr b, 4096 + 4096⟩ : Region) ∈ u.wr := hcu.wr
      exact in_base (List.mem_append_right _ hw) (by simp only [SCAL]; omega) (by simp only [SCAL]; omega)
    · intro r hr
      rw [hpa]
      simp only [stepRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
  have hcw : Ctx b w := (kv.ctx hcu).of_rest (uw.rest (ws := [.r11]) (by decide)) (by decide)
  have kvw : PointKeep b v w := ⟨uw.rest (by decide), by rw [uw.mem]; exact Frame.refl _ _⟩
  have I : CombInv w b p T (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr P) 32)) 0 w := by
    refine ⟨by decide, hcw, by rw [uw.gpr]; rfl, by rw [uw.mem]; exact lv, by rw [uw.mem, ev]; rfl, ?_,
      PointKeep.refl _ _, by rw [scal], by rw [syw, syv, syu]; exact hsym⟩
    rw [uw.mem, ev, evalOps, List.foldl_append, ← evalOps, ← evalOps, constPoint_eval]
    simpa only [digitSum64, add_zero, natCast_zsmul] using combStart_ok
  exact ⟨ku.trans ((PointKeep.of_keep kv).trans kvw), E, I⟩

theorem combMultiply_ok {s : State} {b P T : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b)
    (hp : s.gpr .r12 = P) (hfit : P.toNat + 32 ≤ 2 ^ 32)
    (hr : ∀ k < 32, InRegions (s.rd ++ s.wr) (State.addr P + BitVec.ofNat 64 k) 1)
    (hsep : (⟨State.addr P, 32⟩ : Region).Disjoint ⟨State.addr b, 8192⟩)
    (hT : TblAt s T) (hsym : s.syms combSym = T) (apart : (TBL T).Disjoint ⟨State.addr b, 8192⟩) :
    WP isa combMultiply s fun t => PointKeep b s t ∧ AllLim t.mem b ∧
      Rep (point (env t.mem b) 0 1 2 3)
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr P) 32) • baseAff) := by
  rw [combMultiply]
  refine WP.seq (WP.mono (combPrepare_ok hc hl hp hfit hr hsep hT hsym apart) fun w ⟨kw, E, I⟩ => ?_)
  refine WP.mono (combSteps_ok E I (by decide)) fun t ht => ⟨kw.trans ht.keep, ht.lim, ?_⟩
  have hS := decodeLE_lt32 s.mem (State.addr P)
  have e := comb64_total (S := Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr P) 32))
    (by simpa using hS)
  have := ht.acc
  rw [e, natCast_zsmul] at this
  exact this

end VG.Proof.Ed25519.Arm
