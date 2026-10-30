module

public import VerifiedGarbage.Proof.Ed25519.Arm.CombDigit
public import VerifiedGarbage.Proof.Ed25519.Arm.FieldProg
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.ReadHalves
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# The ARMv7 comb's selection

The static `combSym` at `T` holds, as 32-bit words, the limbs of the comb's entries
(`tbl_read`, from the 64-bit words a contract states). `combSelect` stores into slots 4–6 the
limbs of coordinate `c` of entry `a` of table `i`, `selLimb`, for the magnitude `a ≤ 8` whose
mask is the one set among `r1`–`r8` (`combSelect_ok`); entry 0 is the identity's
`[1, 1, 0]`.
-/

@[expose] public section

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
