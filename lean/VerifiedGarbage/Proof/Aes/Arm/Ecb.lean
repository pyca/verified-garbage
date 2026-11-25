module

public import VerifiedGarbage.Impl.Aes.Arm.Blocks
public import VerifiedGarbage.Proof.Aes.Arm.Group
public import VerifiedGarbage.Spec.Aes.Contract
import VerifiedGarbage.Proof.Framework.Arm.Bytes
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### Two blocks -/

section

/-!
# Decrypting two blocks, bitsliced, on ARMv7

`decrypt2_ok`: from two blocks in the registers (`InRel`), with the
bitsliced round keys in the scratch buffer (`EncPre`) and the first one's
address in slot `fkSlot`, `decrypt2` leaves the two plaintexts, having written
only the first 128 bytes of the scratch buffer. The layers are those of
`Layers.lean`, composed as `encrypt2_ok` does. The loop's invariant is the
specification's `foldl` over the rounds done, with the pointer in slot
`kpSlot` stepping down from the last round key, two at a time.
-/

@[expose] public section

namespace VG.Proof.Aes.Arm

open VG VG.Arm VG.Arm.Straight VG.Bitslice VG.Impl.Aes.Arm
open VG.Proof.Aes (irnd invMid invMid_succ invCipher_eq)
open VG.Spec.Aes (roundKey invShiftRows addRoundKey invCipher)
open VG.Proof.MdStream.Arm (Upd Fupd op2_imm op2_reg wp_sub wp_cmp wp_and wp_add)

/-- The first round key's address, in slot `fkSlot`. -/
abbrev FirstKey (s₀ : State) (m : Mem) : Prop :=
  m.readW (slotA (State.addr (s₀.gpr sb)) fkSlot) 32 = s₀.gpr kp

theorem firstKey_ctx {s₀ s : State} (hc : Ctx s₀ s)
    (h : FirstKey s₀ s₀.mem) : FirstKey s₀ s.mem := by
  rw [FirstKey, hc.frame.readW (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (scr_disj _ (lx := 128) (y := 4 * fkSlot) (ly := 32 / 8) (by decide) (by decide)).symm)
    (by decide)]
  exact h

section
variable {s₀ s : State} {R a : Nat} {w : List Byte} {rest : List Instr} {Z : State → Prop}

/-- InvShiftRows and InvSubBytes, of a state with `{63}` added. -/
theorem St.invSub (hp : EncPre s₀ R w) (h : St s₀ a s) {f : Nat} {T : Nat → Spec.Aes.State}
    (hb : BsRel (f + 1) (Q s) fun b => add63 (T b))
    (hQ : ∀ s', St s₀ a s' → BsRel f (P s') (fun b => Spec.Aes.invSubBytes (invShiftRows (T b))) →
      WP isa (.block rest) s' Z) : WP isa (.block (invSubBytes ++ rest)) s Z := by
  obtain ⟨s', h1, h2, h3, h4, h5, h6, h7⟩ := invSubBytes_ok (hp.spillOk h.ctx)
  refine h.layer (X := fun s' => ∀ x < 32, bsByte (P s') x = Spec.Aes.invSbox (bsByte (Q s) x ^^^ 0x63))
    ⟨s', h1, h2, h3, h4, h5, h6 sb (by decide) (by decide), h7⟩ fun s' hs' hx => hQ s' hs' ?_
  exact bs_invSubBytes hx ((bs_invShiftRows hb).of_eq fun b => add63_invShiftRows _)

/-- InvMixColumns. -/
theorem St.invMix (h : St s₀ a s) {f g : Nat} (hf : f < 4) (hg : g % 4 = f) {T : Nat → Spec.Aes.State}
    (hb : BsRel g (P s) fun b => add63 (T b))
    (hQ : ∀ s', St s₀ a s' → BsRel g (Q s') (fun b => add63 (Spec.Aes.invMixColumns (T b))) →
      WP isa (.block rest) s' Z) :
    WP isa (.block (invMixColumns f ++ rest)) s Z := by
  obtain ⟨s', h1, h2, h3, h4, h5, h6, h7⟩ := invMix_ok hf s
  refine h.layer (X := fun s' => BsRel g (Q s') (fun b => add63 (Spec.Aes.invMixColumns (T b))))
    ⟨s', h1, ?_, h3, h4, h5, h7, by rw [h6]; exact Frame.refl _ _⟩ hQ
  have := h2 _ (by rw [← hg]; exact BsRel.mod.mpr hb)
  rw [← hg] at this
  exact (BsRel.mod.mp this).of_eq fun b => invMix_add63 _

/-- The pointer stored. -/
theorem St.store (hp : EncPre s₀ R w) (h : St s₀ a s) {a' : Nat}
    (hk : s.gpr kp = s₀.gpr kp + BitVec.ofNat 32 (32 * a'))
    (hQ : ∀ s', St s₀ a' s' → s'.gpr = s.gpr → WP isa (.block rest) s' Z) :
    WP isa (.block (stS kpSlot kp :: rest)) s Z := by
  refine wp_stS h.ctx.base (h.wr hp) hp.fit (by decide) fun s' u => hQ s' ⟨?_, ?_⟩ u.gpr
  · refine h.ctx.step u.rd u.wr u.sp (by rw [u.gpr]) ?_
    rw [u.mem, h.ctx.base]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (VG.Offset.contains_base _ (by decide) (by decide))
  · rw [u.mem, Mem.readW_writeW_self32, hk]

/-- The pointer two round keys back. -/
theorem St.back (hp : EncPre s₀ R w) (h : St s₀ (a + 2) s)
    (hQ : ∀ s', St s₀ a s' → s'.gpr kp = s₀.gpr kp + BitVec.ofNat 32 (32 * a) → (∀ i, P s' i = P s i) →
      WP isa (.block rest) s' Z) : WP isa (.block (kpBack ++ rest)) s Z := by
  refine wp_ldS h.ctx.base (h.wr hp) hp.fit (by decide) fun s₁ u₁ => wp_sub (op2_imm (by decide)) fun s₂ u₂ => ?_
  have k₂ : s₂.gpr kp = s₀.gpr kp + BitVec.ofNat 32 (32 * a) := by
    rw [u₂.gpr, u₁.gpr, h.kpm, show 32 * (a + 2) = 32 * a + 64 by omega_using [], BitVec.ofNat_add, ← BitVec.add_assoc]
    exact BitVec.add_sub_cancel _ _
  refine ((h.upd u₁ (by decide)).upd u₂ (by decide)).store hp k₂ fun s₃ h₃ g₃ => hQ s₃ h₃ (by rw [g₃, k₂]) fun i => ?_
  rw [P, P, g₃, u₂.other _ (p_ne_kp i), u₁.other _ (p_ne_kp i)]

theorem kp_diff (K : BitVec 32) (n : Nat) : K + BitVec.ofNat 32 n - K = BitVec.ofNat 32 n := by
  bv_omega

theorem test_head : ∀ a < 15, (BitVec.ofNat 32 (32 * a) &&& 64) - 0 = 0 ↔ a / 2 % 2 = 0 := by decide

/-- Whether the number of round keys left is a multiple of 4. -/
theorem St.head (hp : EncPre s₀ R w) (hfk : FirstKey s₀ s₀.mem) (h : St s₀ a s) (ha : a ≤ R)
    (hQ : ∀ s', St s₀ a s' → (∀ i, Q s' i = Q s i) → Arm.eval .eq s' = some (decide (a / 2 % 2 = 0)) → Z s') :
    WP isa (.block decHead) s Z := by
  have hR := hp.le
  refine wp_ldS h.ctx.base (h.wr hp) hp.fit (by decide) fun s₁ u₁ => ?_
  have h₁ := h.upd u₁ (by decide)
  refine wp_ldS h₁.ctx.base (h₁.wr hp) hp.fit (by decide) fun s₂ u₂ => wp_sub (op2_reg _ _) fun s₃ u₃ =>
    wp_and (op2_imm (by decide)) fun s₄ u₄ => wp_cmp (op2_imm (by decide)) fun s₅ f₅ z₅ => WP.block_nil ?_
  refine hQ s₅ ((((h₁.upd u₂ (by decide)).upd u₃ (by decide)).upd u₄ (by decide)).fupd f₅) (fun i => ?_) ?_
  · rw [Q, Q, f₅.gpr, u₄.other _ (q_ne_t0 i), u₃.other _ (q_ne_t0 i), u₂.other _ (q_ne_t0 i), u₁.other _ (q_ne_kp i)]
  · show some s₅.z = _
    rw [z₅, u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, firstKey_ctx h₁.ctx hfk, h.kpm, kp_diff]
    have e := test_head a (by omega_using [ha, hR])
    by_cases hc : a / 2 % 2 = 0
    · rw [decide_eq_true hc, e.mpr hc]; rfl
    · rw [decide_eq_false hc, beq_eq_false_iff_ne.mpr (mt e.mp hc)]

/-- Whether the pointer is at the first round key. -/
theorem St.first (hp : EncPre s₀ R w) (hfk : FirstKey s₀ s₀.mem) (h : St s₀ a s) (ha : a ≤ R)
    (hQ : ∀ s', St s₀ a s' → s'.gpr kp = s₀.gpr kp + BitVec.ofNat 32 (32 * a) → (∀ i, P s' i = P s i) →
      s'.z = decide (a = 0) → Z s') :
    WP isa (.block [ldS kp kpSlot, ldS t0 fkSlot, .cmp kp (.reg t0)]) s Z := by
  have hR := hp.le
  refine wp_ldS h.ctx.base (h.wr hp) hp.fit (by decide) fun s₁ u₁ => ?_
  have h₁ := h.upd u₁ (by decide)
  refine wp_ldS h₁.ctx.base (h₁.wr hp) hp.fit (by decide) fun s₂ u₂ => wp_cmp (op2_reg _ _) fun s₃ f₃ z₃ =>
    WP.block_nil (hQ s₃ ((h₁.upd u₂ (by decide)).fupd f₃) ?_ (fun i => ?_) ?_)
  · rw [f₃.gpr, u₂.other _ (by decide), u₁.gpr, h.kpm]
  · rw [P, P, f₃.gpr, u₂.other _ (p_ne_t0 i), u₁.other _ (p_ne_kp i)]
  · rw [z₃, u₂.gpr, u₂.other _ (by decide), u₁.gpr, firstKey_ctx h₁.ctx hfk, h.kpm, kp_diff]
    by_cases hc : a = 0
    · subst hc; rfl
    · rw [decide_eq_false hc, beq_eq_false_iff_ne]
      intro he
      bv_omega_using [he, hc, ha, hR]

end

/-! ## The rounds -/

theorem keepZ_dec : decLast.all keepsZ = true ∧ decEnd.all keepsZ = true := by decide +kernel

theorem irnd_eq {R a : Nat} (w : List Byte) (x : Spec.Aes.State) (h : a + 1 ≤ R) :
    Spec.Aes.invMixColumns (addRoundKey (Spec.Aes.invSubBytes (invShiftRows (invMid R w (R - (a + 1)) x)))
      (roundKey w a)) = invMid R w (R - a) x := by
  rw [show R - a = R - (a + 1) + 1 by omega_using [h], invMid_succ, irnd,
    show R - 1 - (R - (a + 1)) = a by omega_using [h]]

/-- The state before the rounds from round key `a` down. -/
abbrev DecRel (R : Nat) (w : List Byte) (A : Nat → Spec.Aes.State) (a : Nat) (s : State) : Prop :=
  BsRel a (Q s) fun b => add63 (invMid R w (R - a) (A b))

theorem decHi_ok {s₀ s : State} {R a : Nat} {w : List Byte} {A : Nat → Spec.Aes.State} (hp : EncPre s₀ R w)
    (h : St s₀ (a + 2) s) (ha : a % 4 = 2) (haR : a + 2 ≤ R) (hb : DecRel R w A (a + 2) s) :
    WP isa (.block decHi) s fun s' => St s₀ a s' ∧ DecRel R w A a s' := by
  simp only [decHi, List.append_assoc]
  refine h.invSub hp (f := a + 1) hb fun s₁ h₁ b₁ => h₁.back hp fun s₂ h₂ k₂ p₂ => ?_
  refine h₂.ark hp (j := a + 1) k₂ (arkP_check 32 (by decide)) rfl (by decide) (by decide) (by omega_using [haR])
    (b₁.congr (Q' := P s₂) fun j _ => p₂ j) (fun b _ i hi => ark_add63 (by omega_using []) hi) fun s₃ h₃ b₃ _ => ?_
  refine h₃.invMix (by decide) (by omega_using [ha]) b₃ fun s₄ h₄ b₄ => ?_
  refine h₄.invSub hp (f := a) (b₄.of_eq fun b => by rw [irnd_eq w _ haR]) fun s₅ h₅ b₅ =>
    h₅.ldKp hp fun s₆ h₆ k₆ o₆ => ?_
  refine h₆.ark hp (j := a) k₆ (arkP_check 0 (by decide)) rfl (by decide) (by decide) (by omega_using [haR])
    (b₅.congr (Q' := P s₆) fun j _ => o₆ _ (p_ne_kp j)) (fun b _ i hi => ark_add63 (by omega_using [ha]) hi)
    fun s₇ h₇ b₇ _ => ?_
  rw [← List.append_nil (invMixColumns 2)]
  refine h₇.invMix (by decide) (by omega_using [ha]) b₇ fun s₈ h₈ b₈ => WP.block_nil ⟨h₈, ?_⟩
  exact b₈.of_eq fun b => by rw [irnd_eq w _ (by omega_using [haR])]

/-- Up to four rounds. -/
theorem decBody_ok {s₀ s : State} {R a : Nat} {w : List Byte} {X : Nat → Spec.Aes.State} (hp : EncPre s₀ R w)
    (hfk : FirstKey s₀ s₀.mem) (h : St s₀ a s) (ha : a % 2 = 0) (ha0 : 0 < a) (haR : a ≤ R)
    (hb : DecRel R w (fun b => addRoundKey (X b) (roundKey w R)) a s) :
    WP isa decBody s fun s' =>
      (Arm.eval .ne s' = some false ∧ Ctx s₀ s' ∧ InRel (Q s') fun b => invCipher R w (X b)) ∨
      (Arm.eval .ne s' = some true ∧ ∃ a', a' < a ∧ a' % 2 = 0 ∧ 0 < a' ∧ St s₀ a' s' ∧
        DecRel R w (fun b => addRoundKey (X b) (roundKey w R)) a' s') := by
  refine WP.seq (h.head hp hfk haR fun s₁ h₁ q₁ ev₁ => ?_)
  have b₁ : DecRel R w (fun b => addRoundKey (X b) (roundKey w R)) a s₁ := hb.congr fun j _ => q₁ j
  refine WP.seq (WP.mono (Q := fun s' => ∃ c, c % 4 = 0 ∧ c + 2 ≤ a ∧ St s₀ (c + 2) s' ∧
      DecRel R w (fun b => addRoundKey (X b) (roundKey w R)) (c + 2) s')
    (WP.ite _ ev₁ (fun he => ?_) (fun he => ?_)) fun s₂ ⟨c, hc, hca, h₂, b₂⟩ => ?_)
  · simp only [decide_eq_true_eq] at he
    obtain ⟨c, rfl⟩ : ∃ c, a = c + 2 + 2 := ⟨a - 4, by omega_using [he, ha, ha0]⟩
    exact WP.mono (decHi_ok hp h₁ (by omega_using [he, ha]) haR b₁) fun s' hs' =>
      ⟨c, by omega_using [he, ha], by omega_using [], hs'.1, hs'.2⟩
  · simp only [decide_eq_false_iff_not] at he
    obtain ⟨c, rfl⟩ : ∃ c, a = c + 2 := ⟨a - 2, by omega_using [he, ha, ha0]⟩
    exact WP.block_nil ⟨c, by omega_using [he, ha], Nat.le_refl _, h₁, b₁⟩
  have hcR : c + 2 ≤ R := Nat.le_trans hca haR
  simp only [decLo, List.append_assoc]
  refine WP.seq ?_
  refine h₂.invSub hp (f := c + 1) b₂ fun s₃ h₃ b₃ => h₃.back hp fun s₄ h₄ k₄ p₄ => ?_
  refine h₄.ark hp (j := c + 1) k₄ (arkP_check 32 (by decide)) rfl (by decide) (by decide) (by omega_using [hcR])
    (b₃.congr (Q' := P s₄) fun j _ => p₄ j) (fun b _ i hi => ark_add63 (by omega_using []) hi) fun s₅ h₅ b₅ _ => ?_
  refine h₅.invMix (by decide) (by omega_using [hc]) b₅ fun s₆ h₆ b₆ => ?_
  refine h₆.invSub hp (f := c) (b₆.of_eq fun b => by rw [irnd_eq w _ hcR]) fun s₇ h₇ b₇ => ?_
  refine h₇.first hp hfk (by omega_using [hcR]) fun s₈ h₈ k₈ p₈ z₈ => ?_
  have b₈ := b₇.congr (Q' := P s₈) fun j _ => p₈ j
  refine WP.ite (decide (c = 0)) (by show some s₈.z = _; rw [z₈]) (fun he => ?_) (fun he => ?_)
  · have he : c = 0 := by simpa using he
    subst he
    refine WP.mono (WP.keepZ (Q := fun s' => Ctx s₀ s' ∧ InRel (Q s') fun b => invCipher R w (X b)) ?_ keepZ_dec.1)
      fun s' hs' => .inl ⟨by simp only [Arm.eval, hs'.2, z₈]; rfl, hs'.1⟩
    simp only [decLast]
    refine h₈.ark hp (j := 0) k₈ (arkQP_check 0 (by decide)) rfl (by decide) (by decide) (Nat.zero_le _) b₈
      (fun b _ i hi => ark_first hi) fun s₉ h₉ b₉ _ => ?_
    rw [← List.append_nil ortho]
    exact h₉.ortho b₉ fun s₁₀ h₁₀ w₁₀ => WP.block_nil ⟨h₁₀.ctx, inRel_iff.mp w₁₀⟩
  · have he : c ≠ 0 := by simpa using he
    refine WP.mono (WP.keepZ (Q := fun s' => St s₀ c s' ∧
        DecRel R w (fun b => addRoundKey (X b) (roundKey w R)) c s') ?_ keepZ_dec.2) fun s' hs' =>
      .inr ⟨by simp only [Arm.eval, hs'.2, z₈]; simp [he], c, by omega_using [hca], by omega_using [hc],
        by omega_using [he], hs'.1⟩
    simp only [decEnd]
    refine h₈.ark hp (j := c) k₈ (arkP_check 0 (by decide)) rfl (by decide) (by decide) (by omega_using [hcR]) b₈
      (fun b _ i hi => ark_add63 he hi) fun s₉ h₉ b₉ _ => ?_
    rw [← List.append_nil (invMixColumns 0)]
    refine h₉.invMix (by decide) hc b₉ fun s₁₀ h₁₀ b₁₀ => WP.block_nil ⟨h₁₀, ?_⟩
    exact b₁₀.of_eq fun b => by rw [irnd_eq w _ (by omega_using [hcR])]

theorem test_start : ∀ R, R = 10 ∨ R = 12 ∨ R = 14 →
    ((BitVec.ofNat 32 (lastKey - 32 * R) &&& 64) - 0 = 0 ↔ R % 4 = 0) := by
  intro R h; rcases h with rfl | rfl | rfl <;> decide

/-- Two blocks, from `InRel` to `InRel` of their decryptions. -/
theorem decrypt2_ok {s₀ : State} {R : Nat} {w : List Byte} {S : Nat → Spec.Aes.State}
    (hp : EncPre s₀ R w) (hfk : FirstKey s₀ s₀.mem) (hin : InRel (Q s₀) S) :
    WP isa decrypt2 s₀ fun s => Ctx s₀ s ∧ InRel (Q s) (fun b => invCipher R w (S b)) := by
  have hev := hp.even
  let Inv : Nat → State → Prop := fun a s => a % 2 = 0 ∧ 0 < a ∧ a ≤ R ∧ St s₀ a s ∧
    DecRel R w (fun b => addRoundKey (S b) (roundKey w R)) a s
  refine WP.seq (wp_sub (op2_reg _ _) fun s₁ u₁ => wp_and (op2_imm (by decide)) fun s₂ u₂ =>
    wp_cmp (op2_imm (by decide)) fun s₃ f₃ z₃ => WP.block_nil ?_)
  have c₃ : Ctx s₀ s₃ := (Ctx.refl s₀).step (by rw [f₃.rd, u₂.rd, u₁.rd]) (by rw [f₃.wr, u₂.wr, u₁.wr])
    (by rw [f₃.sp, u₂.sp, u₁.sp]) (by rw [f₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)])
    (by rw [f₃.mem, u₂.mem, u₁.mem]; exact Frame.refl _ _)
  have q₃ : ∀ i, Q s₃ i = Q s₀ i := fun i => by
    rw [Q, Q, f₃.gpr, u₂.other _ (q_ne_t0 i), u₁.other _ (q_ne_t0 i)]
  have w₃ : WRel 0 (Q s₃) S := by
    rw [show Q s₃ = Q s₀ from funext q₃]; exact inRel_iff.mpr hin
  have hz : Arm.eval .ne s₃ = some (decide ¬ R % 4 = 0) := by
    have e : s₃.z = ((BitVec.ofNat 32 (lastKey - 32 * R) &&& 64) - 0 == 0) := by
      rw [z₃, u₂.gpr, u₁.gpr, hp.k0, kp_diff]
    have t := test_start R hp.rounds
    simp only [Arm.eval, e]
    by_cases hc : R % 4 = 0
    · rw [t.mpr hc]; simp [hc]
    · rw [beq_eq_false_iff_ne.mpr (mt t.mp hc)]; simp [hc]
  refine WP.seq (WP.mono (Q := fun s' => Ctx s₀ s' ∧ WRel R (Q s') S) (WP.ite _ hz (fun hc => ?_) (fun hc => ?_))
    fun s₄ ⟨c₄, w₄⟩ => ?_)
  · obtain ⟨s', h1, h2, h3, h4, h5, h6, h7⟩ := sr2Words_ok s₃
    refine WP.of_runBlock ⟨s', h1, c₃.step h3 h4 h5 (h6 _ (by decide)) (by rw [h7]; exact Frame.refl _ _), ?_⟩
    have := words_sr2 h2 w₃
    simp only [decide_eq_true_eq] at hc
    rw [show 0 + 2 = R % 4 by omega_using [hc, hev]] at this
    exact WRel.mod.mp this
  · refine WP.block_nil ⟨c₃, WRel.mod.mp ?_⟩
    simp only [decide_eq_false_iff_not, Decidable.not_not] at hc
    rw [hc]; exact w₃
  refine WP.seq (WP.mono (Q := Inv R) ?_ fun s h => WP.loop (M := isa) Inv (fun n s hs => ?_) R s h)
  · simp only [decStart, List.append_assoc]
    rw [WP.block_append_iff (M := isa)]
    obtain ⟨s₅, h1, h2, h3, h4, h5, h6, h7⟩ := ortho_ok' s₄
    refine WP.of_runBlock ⟨s₅, h1, ?_⟩
    have c₅ : Ctx s₀ s₅ := c₄.step h3 h4 h5 (h6 _ (by decide)) (by rw [h7]; exact Frame.refl _ _)
    simp only [List.cons_append, List.nil_append]
    refine wp_add (op2_imm (by decide)) fun s₆ u₆ => ?_
    have k₆ : s₆.gpr kp = s₀.gpr kp + BitVec.ofNat 32 (32 * R) := by
      have hR := hp.le
      rw [u₆.gpr, c₅.base, kp_off _ _ hp.k0, show lastKey - 32 * R + 32 * R = lastKey by
        simp only [lastKey]; omega_using [hR]]
    have c₆ : Ctx s₀ s₆ := c₅.step u₆.rd u₆.wr u₆.sp (u₆.other _ (by decide)) (by rw [u₆.mem]; exact Frame.refl _ _)
    refine wp_stS c₆.base (by rw [c₆.wr]; exact hp.scr) hp.fit (by decide) fun s₇ u₇ => ?_
    have h₇ : St s₀ R s₇ := by
      refine ⟨c₆.step u₇.rd u₇.wr u₇.sp (by rw [u₇.gpr]) ?_, by rw [u₇.mem, Mem.readW_writeW_self32, k₆]⟩
      rw [u₇.mem, c₆.base]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (VG.Offset.contains_base _ (by decide) (by decide))
    have b₇ : BsRel R (Q s₇) S := (bs_of_words h2 w₄).congr fun j _ => by
      show s₇.gpr (q j) = s₅.gpr (q j); rw [u₇.gpr, u₆.other _ (q_ne_kp j)]
    rw [← List.append_nil (addKey 0 q q)]
    refine h₇.ark hp (j := R) (by rw [u₇.gpr, k₆]) (arkQ_check 0 (by decide)) rfl (by decide) (by decide)
      (Nat.le_refl _) b₇ (fun b _ i hi => ark_add63 (by omega_using [hev]) hi) fun s₈ h₈ b₈ _ =>
      WP.block_nil ⟨hev.1, by omega_using [hev], Nat.le_refl _, h₈, b₈.of_eq fun b => ?_⟩
    rw [Nat.sub_self]; rfl
  · obtain ⟨ha, ha0, haR, hst, hb⟩ := hs
    refine WP.mono (decBody_ok hp hfk hst ha ha0 haR hb) fun s' h => ?_
    rcases h with ⟨e, h⟩ | ⟨e, a', h1, h2, h3, h4, h5⟩
    · exact .inl ⟨e, h⟩
    · exact .inr ⟨e, a', h1, h2, h3, by omega_using [h1, haR], h4, h5⟩

end VG.Proof.Aes.Arm

end

end


/-!
# AES on whole blocks on ARMv7: the groups

A group of `blocks` loads (up to) two blocks of the data into the state
registers as `ortho` takes them, runs a transformation of two blocks
(`encrypt2` or `decrypt2`, whose proofs give `CryptOk`), and stores the
results back in place. The loaded blocks are named by the bytes of the
registers (`regBlock`), so that the last group needs no padding: its unused
block is whatever the registers held. The data's invariant (`EcbInv`) says
that the first `k` words hold the transformation of the original blocks,
and the others are still the original ones.
-/

@[expose] public section

namespace VG.Proof.Aes.Arm.Ecb

open VG VG.Arm VG.Arm.Straight VG.Bitslice VG.Impl.Aes.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg op2_lsr wp_mov wp_add wp_sub wp_cmp
  wp_ldr wp_str)

/-- The state made of the bytes of the words: byte `i` of block `c` is byte
`i mod 4` of word `2 ⌊i / 4⌋ + c`, as `InRel` places them. -/
def regBlock (Q : Nat → BitVec 32) (c : Nat) : Spec.Aes.State :=
  Vector.ofFn fun i => (Q (2 * (i.1 / 4) + c)).extractLsb' (8 * (i.1 % 4)) 8

theorem inRel_regBlock (Q : Nat → BitVec 32) : InRel Q (regBlock Q) := by
  intro b _ i hi j hj
  rw [getD_eq _ hi]
  simp [regBlock, hj]

/-- What a transformation of two blocks does: `f R w` to each, with the
round keys as `EncPre` has them and the first one's address in slot
`fkSlot`. -/
def CryptOk (crypt2 : Prog isa) (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) : Prop :=
  ∀ {s₀ : State} {R : Nat} {w : List Byte} {S : Nat → Spec.Aes.State}, EncPre s₀ R w →
    FirstKey s₀ s₀.mem → InRel (Q s₀) S →
    WP isa crypt2 s₀ fun s => Ctx s₀ s ∧ InRel (Q s) (fun b => f R w (S b))

theorem encrypt2_cryptOk : CryptOk encrypt2 Spec.Aes.cipher := fun hp _ hin => encrypt2_ok hp hin
theorem decrypt2_cryptOk : CryptOk decrypt2 Spec.Aes.invCipher := fun hp hfk hin => decrypt2_ok hp hfk hin

/-! ## The data -/

/-- The data after `k` words: the first `4 k` of the `16 n` bytes at `D` are
`F`'s (block by block), the others are still `m₀`'s. -/
def EcbInv (m₀ m : Mem) (D : Addr) (n k : Nat) (F : Nat → Spec.Aes.State) : Prop :=
  ∀ i < 16 * n, m (D + BitVec.ofNat 64 i) =
    if i < 4 * k then (F (i / 16)).getD (i % 16) 0 else m₀ (D + BitVec.ofNat 64 i)

theorem writeW32_apply (m : Mem) (a x : Addr) (v : BitVec 32) :
    m.writeW a v x = if (x - a).toNat < 4 then v.extractLsb' (8 * (x - a).toNat) 8 else m x := by
  rw [show m.writeW a v x = if (x - a).toNat < 32 / 8 then
      (v.setWidth (8 * (32 / 8))).extractLsb' (8 * (x - a).toNat) 8 else m x from rfl]
  rfl

/-- One more word stored. -/
theorem ecbInv_step {m₀ m : Mem} {D : Addr} {n k : Nat} {F : Nat → Spec.Aes.State} {v : BitVec 32}
    (hn : 16 * n ≤ 2 ^ 32) (hk : k < 4 * n) (h : EcbInv m₀ m D n k F)
    (hv : ∀ t < 4, v.extractLsb' (8 * t) 8 = (F ((4 * k + t) / 16)).getD ((4 * k + t) % 16) 0) :
    EcbInv m₀ (m.writeW (D + BitVec.ofNat 64 (4 * k)) v) D n (k + 1) F ∧
      Frame [⟨D, 16 * n⟩] m (m.writeW (D + BitVec.ofNat 64 (4 * k)) v) := by
  refine ⟨fun i hi => ?_, fun x hx => ?_⟩
  · rw [writeW32_apply, off_toNat D (by omega_arith) (by omega_arith)]
    by_cases h1 : 4 * k ≤ i
    · rw [ite_eq_left h1]
      by_cases h2 : i - 4 * k < 4
      · rw [ite_eq_left h2, hv _ h2, ite_eq_left (show i < 4 * (k + 1) by omega_arith),
          show 4 * k + (i - 4 * k) = i by omega_arith]
      · rw [ite_eq_right h2, h i hi, ite_eq_right (show ¬ i < 4 * k by omega_arith),
          ite_eq_right (show ¬ i < 4 * (k + 1) by omega_arith)]
    · rw [ite_eq_right h1, ite_eq_right (show ¬ 2 ^ 64 + i - 4 * k < 4 by omega_arith), h i hi,
        ite_eq_left (show i < 4 * k by omega_arith), ite_eq_left (show i < 4 * (k + 1) by omega_arith)]
  · have hx' : ¬ (x - D).toNat + 1 ≤ 16 * n := hx _ (List.mem_singleton_self _)
    rw [writeW32_apply, ite_eq_right]
    have : 4 * k < 2 ^ 64 := by omega_arith
    have : (BitVec.ofNat 64 (4 * k)).toNat = 4 * k := by simp; omega_arith
    bv_omega

theorem ecbInv_mono {m₀ m : Mem} {D : Addr} {n k k' : Nat} {F : Nat → Spec.Aes.State}
    (h : EcbInv m₀ m D n k F) (hk : 4 * n ≤ k) (hk' : 4 * n ≤ k') : EcbInv m₀ m D n k' F := by
  intro i hi
  rw [h i hi, ite_eq_left (show i < 4 * k by omega_arith), ite_eq_left (show i < 4 * k' by omega_arith)]

theorem ecbInv_frame {m₀ m m' : Mem} {D : Addr} {n k : Nat} {F : Nat → Spec.Aes.State}
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨D, 16 * n⟩ r)
    (hn : 16 * n < 2 ^ 64) (h : EcbInv m₀ m D n k F) : EcbInv m₀ m' D n k F := fun i hi => by
  rw [← h i hi]
  exact hf.bytes (R := ⟨D, 16 * n⟩) hd (by simp only; omega_arith) hi

/-- The output blocks: `f R w` of the original ones. -/
def ecbOut (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (m₀ : Mem) (D : Addr) (R : Nat)
    (w : List Byte) (j : Nat) : Spec.Aes.State :=
  f R w (Spec.Aes.stateAt m₀ (D + BitVec.ofNat 64 (16 * j)))

/-! ## Loading -/

theorem regBlock_load {Q : Nat → BitVec 32} {m : Mem} {A : Addr} {c : Nat}
    (h : ∀ k < 4, Q (2 * k + c) = m.readW (A + BitVec.ofNat 64 (4 * k)) 32) :
    regBlock Q c = Spec.Aes.stateAt m A := by
  apply Vector.ext
  intro i hi
  refine byte_ext fun j hj => ?_
  simp only [regBlock, Spec.Aes.stateAt, Vector.getElem_ofFn, BitVec.getLsbD_extractLsb', hj,
    decide_true, Bool.true_and]
  rw [h _ (by omega_arith), readW_bit _ _ (by omega_arith) hj, Offset.add_add,
    show 4 * (i / 4) + i % 4 = i by omega_arith]

/-- Block `j` of the data, while the first `k ≤ 4 j` words are written, is the original one. -/
theorem stateAt_ecbInv {m₀ m : Mem} {D : Addr} {n k j : Nat} {F : Nat → Spec.Aes.State}
    (h : EcbInv m₀ m D n k F) (hj : j < n) (hk : k ≤ 4 * j) :
    Spec.Aes.stateAt m (D + BitVec.ofNat 64 (16 * j)) = Spec.Aes.stateAt m₀ (D + BitVec.ofNat 64 (16 * j)) := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Aes.stateAt, Vector.getElem_ofFn]
  rw [Offset.add_add, h _ (by omega_arith), ite_eq_right (by omega_arith)]

theorem q_blk : ∀ c < 2, ∀ k < 4, q (2 * k + c) ≠ .r10 ∧ q (2 * k + c) ≠ .r11 ∧ q (2 * k + c) ≠ .r12 ∧
    q (2 * k + c) ≠ sb ∧ q (2 * k + c) ≠ kp ∧ q (2 * k + c) ≠ .lr := by
  decide

theorem loadBlock_wp {s : State} {Dp : BitVec 32} {n g c : Nat} (hc : c < 2) (hgc : 2 * g + c < n)
    (hfit : Dp.toNat + 16 * n ≤ 2 ^ 32) (hdat : (⟨State.addr Dp, 16 * n⟩ : Region) ∈ s.wr)
    (h10 : s.gpr .r10 = Dp + BitVec.ofNat 32 (32 * g)) {P : State → Prop}
    (h : ∀ s', (∀ k < 4, s'.gpr (q (2 * k + c)) =
        s.mem.readW (State.addr Dp + BitVec.ofNat 64 (16 * (2 * g + c)) + BitVec.ofNat 64 (4 * k)) 32) →
      (∀ r, (∀ k < 4, r ≠ q (2 * k + c)) → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → P s') :
    WP isa (.block (loadBlock c)) s P := by
  obtain ha : ∀ (s' : State), s'.gpr .r10 = s.gpr .r10 → s'.wr = s.wr → ∀ k < 4,
      State.addr (s'.gpr .r10 + BitVec.ofNat 32 (16 * c + 4 * k)) =
        State.addr Dp + BitVec.ofNat 64 (16 * (2 * g + c)) + BitVec.ofNat 64 (4 * k) ∧
      InRegions (s'.rd ++ s'.wr)
        (State.addr Dp + BitVec.ofNat 64 (16 * (2 * g + c)) + BitVec.ofNat 64 (4 * k)) 4 := by
    intro s' h1 h2 k hk
    obtain e : State.addr (s'.gpr .r10 + BitVec.ofNat 32 (16 * c + 4 * k)) =
        State.addr Dp + BitVec.ofNat 64 (16 * (2 * g + c)) + BitVec.ofNat 64 (4 * k) := by
      rw [h1, h10, add_ofNat_ofNat, addr_add (by omega_arith), Offset.add_add]
      congr 2; omega_arith
    refine ⟨e, ?_⟩
    have := in_off (List.mem_append_right s'.rd (h2 ▸ hdat)) hfit
      (off := 16 * (2 * g + c) + 4 * k) (n := 4) (by omega_arith) (by omega_arith)
    rwa [addr_add (by omega_arith), ← Offset.add_add] at this
  obtain qb := q_blk c hc
  simp only [loadBlock, List.range, List.range.loop, List.map_cons, List.map_nil]
  obtain ⟨a0, i0⟩ := ha s rfl rfl 0 (by omega_arith)
  refine wp_ldr (by omega_arith) a0 i0 fun s₁ u₁ => ?_
  obtain ⟨a1, i1⟩ := ha s₁ (u₁.other _ (qb 0 (by omega_arith)).1.symm) u₁.wr 1 (by omega_arith)
  refine wp_ldr (by omega_arith) a1 i1 fun s₂ u₂ => ?_
  obtain ⟨a2, i2⟩ := ha s₂ (by rw [u₂.other _ (qb 1 (by omega_arith)).1.symm,
    u₁.other _ (qb 0 (by omega_arith)).1.symm]) (by rw [u₂.wr, u₁.wr]) 2 (by omega_arith)
  refine wp_ldr (by omega_arith) a2 i2 fun s₃ u₃ => ?_
  obtain ⟨a3, i3⟩ := ha s₃ (by rw [u₃.other _ (qb 2 (by omega_arith)).1.symm,
    u₂.other _ (qb 1 (by omega_arith)).1.symm, u₁.other _ (qb 0 (by omega_arith)).1.symm])
    (by rw [u₃.wr, u₂.wr, u₁.wr]) 3 (by omega_arith)
  refine wp_ldr (by omega_arith) a3 i3 fun s₄ u₄ => WP.block_nil (h s₄ (fun k hk => ?_) (fun r hr => ?_)
    (by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]) (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]) (by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]))
  · have hne : ∀ j < 4, j ≠ k → q (2 * k + c) ≠ q (2 * j + c) := fun j hj hjk =>
      q_inj c hc k (by omega_arith) j hj (Ne.symm hjk)
    obtain m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega_arith) with rfl | rfl | rfl | rfl
    · rw [u₄.other _ (hne 3 (by omega_arith) (by omega_arith)), u₃.other _ (hne 2 (by omega_arith) (by omega_arith)),
        u₂.other _ (hne 1 (by omega_arith) (by omega_arith)), u₁.gpr]
    · rw [u₄.other _ (hne 3 (by omega_arith) (by omega_arith)), u₃.other _ (hne 2 (by omega_arith) (by omega_arith)),
        u₂.gpr, u₁.mem]
    · rw [u₄.other _ (hne 3 (by omega_arith) (by omega_arith)), u₃.gpr, u₂.mem, u₁.mem]
    · rw [u₄.gpr, m₃]
  · rw [u₄.other _ (hr 3 (by omega_arith)), u₃.other _ (hr 2 (by omega_arith)), u₂.other _ (hr 1 (by omega_arith)),
      u₁.other _ (hr 0 (by omega_arith))]

/-! ## Storing -/

/-- Word `k` of a group of two blocks: data word `k` from `q (2 (k mod 4) + ⌊k / 4⌋)`. -/
def stw (k : Nat) : List Instr := [.str (q (2 * (k % 4) + k / 4)) .r10 (4 * k)]

theorem storeFull_eq : storeFull = stw 0 ++ stw 1 ++ stw 2 ++ stw 3 ++ stw 4 ++ stw 5 ++ stw 6 ++
    stw 7 ++ ([.dp .add .r10 .r10 (.imm 32), .dp .sub .r11 .r11 (.imm 2)] : List Instr) := rfl

theorem storeTail_eq : storeTail = stw 0 ++ stw 1 ++ stw 2 ++ stw 3 ++
    ([.mov .r11 (.imm 0)] : List Instr) := rfl

/-- After `k` words of the group have been stored, from `s₃`. -/
structure SS (m₀ : Mem) (D : Addr) (n g : Nat) (F : Nat → Spec.Aes.State) (s₃ : State) (k : Nat)
    (s : State) : Prop where
  data : EcbInv m₀ s.mem D n (8 * g + k) F
  frame : Frame [⟨D, 16 * n⟩] s₃.mem s.mem
  gpr : s.gpr = s₃.gpr
  rd : s.rd = s₃.rd
  wr : s.wr = s₃.wr
  sp : s.sp = s₃.sp

/-- Before the stores of group `g`: the results are in the words. -/
structure SPre (m₀ : Mem) (Dp : BitVec 32) (n g : Nat) (F : Nat → Spec.Aes.State) (s₃ : State) :
    Prop where
  hg : 2 * g < n
  fit : Dp.toNat + 16 * n ≤ 2 ^ 32
  dat : (⟨State.addr Dp, 16 * n⟩ : Region) ∈ s₃.wr
  r10 : s₃.gpr .r10 = Dp + BitVec.ofNat 32 (32 * g)
  r11 : s₃.gpr .r11 = BitVec.ofNat 32 (n - 2 * g)
  data : EcbInv m₀ s₃.mem (State.addr Dp) n (8 * g) F
  vals : ∀ k < 8, 8 * g + k < 4 * n → ∀ t < 4,
    (s₃.gpr (q (2 * (k % 4) + k / 4))).extractLsb' (8 * t) 8 =
      (F ((4 * (8 * g + k) + t) / 16)).getD ((4 * (8 * g + k) + t) % 16) 0

section Store

variable {m₀ : Mem} {Dp : BitVec 32} {n g : Nat} {F : Nat → Spec.Aes.State} {s₃ : State}

theorem ss_step (hp : SPre m₀ Dp n g F s₃) {k : Nat} (hk : k < 8) (hkn : 8 * g + k < 4 * n) {s : State}
    (hs : SS m₀ (State.addr Dp) n g F s₃ k s) {is : List Instr} {P : State → Prop}
    (h : ∀ s', SS m₀ (State.addr Dp) n g F s₃ (k + 1) s' → WP isa (.block is) s' P) :
    WP isa (.block (stw k ++ is)) s P := by
  have hn := hp.fit
  obtain ha : State.addr (s.gpr .r10 + BitVec.ofNat 32 (4 * k)) =
      State.addr Dp + BitVec.ofNat 64 (4 * (8 * g + k)) := by
    rw [hs.gpr, hp.r10, add_ofNat_ofNat, addr_add (by omega_arith)]
    congr 2; omega_arith
  obtain hin : InRegions s.wr (State.addr Dp + BitVec.ofNat 64 (4 * (8 * g + k))) 4 := by
    have := in_off (hs.wr ▸ hp.dat) hp.fit (off := 4 * (8 * g + k)) (n := 4) (by omega_arith) (by omega_arith)
    rwa [addr_add (by omega_arith)] at this
  simp only [stw, List.cons_append, List.nil_append]
  refine wp_str (by omega_arith) ha hin fun s' u => ?_
  obtain hst := ecbInv_step (v := s.gpr (q (2 * (k % 4) + k / 4))) (by omega_arith) hkn hs.data
    (fun t ht => by rw [hs.gpr]; exact hp.vals k hk hkn t ht)
  rw [← u.mem] at hst
  exact h s' ⟨by rw [show 8 * g + (k + 1) = 8 * g + k + 1 by omega_arith]; exact hst.1,
    hs.frame.trans hst.2, by rw [u.gpr, hs.gpr], by rw [u.rd, hs.rd], by rw [u.wr, hs.wr],
    by rw [u.sp, hs.sp]⟩

/-- After the stores: `r11` is zero if no data is left. -/
def SDone (m₀ : Mem) (Dp : BitVec 32) (n g : Nat) (F : Nat → Spec.Aes.State) (s₃ s : State) : Prop :=
  Frame [⟨State.addr Dp, 16 * n⟩] s₃.mem s.mem ∧
    (∀ r, r ≠ kp → r ≠ .r10 → r ≠ .r11 → s.gpr r = s₃.gpr r) ∧
    s.rd = s₃.rd ∧ s.wr = s₃.wr ∧ s.sp = s₃.sp ∧
    ((s.gpr .r11 = 0 ∧ EcbInv m₀ s.mem (State.addr Dp) n (4 * n) F) ∨
     (2 * g + 2 < n ∧ EcbInv m₀ s.mem (State.addr Dp) n (8 * (g + 1)) F ∧
      s.gpr .r10 = Dp + BitVec.ofNat 32 (32 * (g + 1)) ∧
      s.gpr .r11 = BitVec.ofNat 32 (n - 2 * (g + 1))))

theorem storePhase_wp (hp : SPre m₀ Dp n g F s₃) :
    WP isa (.block [.mov kp (lsrOp .r11 1), .cmp kp (.imm 0)]) s₃ fun s =>
      WP isa (.ite .ne (.block storeFull) (.block storeTail)) s (SDone m₀ Dp n g F s₃) := by
  have hg := hp.hg
  have hn := hp.fit
  refine wp_mov (op2_lsr (by decide)) fun s₄ u₄ => wp_cmp (op2_imm (by decide)) fun s₅ f₅ z₅ =>
    WP.block_nil ?_
  obtain ev₅ : Arm.eval .ne s₅ = some (decide (2 ≤ n - 2 * g)) := by
    rw [Arm.eval, z₅, u₄.gpr, hp.r11, shr1_eq _ (by omega_arith)]
  -- The stores start from `s₅`, which differs from `s₃` only in `kp` and the flags.
  let s₃' := s₅
  obtain x₀ : SS m₀ (State.addr Dp) n g F s₃' 0 s₅ :=
    ⟨by rw [f₅.mem, u₄.mem]; exact hp.data, Frame.refl _ _, rfl, rfl, rfl, rfl⟩
  obtain g₅ : ∀ r, r ≠ kp → s₅.gpr r = s₃.gpr r := fun r hr => by rw [f₅.gpr, u₄.other r hr]
  obtain hp' : SPre m₀ Dp n g F s₃' :=
    { hg := hg, fit := hn, dat := by rw [f₅.wr, u₄.wr]; exact hp.dat
      r10 := by rw [g₅ _ (by decide)]; exact hp.r10
      r11 := by rw [g₅ _ (by decide)]; exact hp.r11
      data := x₀.data
      vals := fun k hk hkn t ht => by
        rw [g₅ _ (q_ctr (k / 4) (by omega_arith) (k % 4) (by omega_arith)).2.2]; exact hp.vals k hk hkn t ht }
  obtain fin : ∀ s : State, Frame [⟨State.addr Dp, 16 * n⟩] s₅.mem s.mem →
      (∀ r, r ≠ kp → r ≠ .r10 → r ≠ .r11 → s.gpr r = s₅.gpr r) →
      s.rd = s₅.rd → s.wr = s₅.wr → s.sp = s₅.sp →
      Frame [⟨State.addr Dp, 16 * n⟩] s₃.mem s.mem ∧
        (∀ r, r ≠ kp → r ≠ .r10 → r ≠ .r11 → s.gpr r = s₃.gpr r) ∧
        s.rd = s₃.rd ∧ s.wr = s₃.wr ∧ s.sp = s₃.sp := fun s f o rd wr sp =>
    ⟨by rw [← u₄.mem, ← f₅.mem]; exact f, fun r h1 h2 h3 => by rw [o r h1 h2 h3, g₅ r h1],
      by rw [rd, f₅.rd, u₄.rd], by rw [wr, f₅.wr, u₄.wr], by rw [sp, f₅.sp, u₄.sp]⟩
  refine WP.ite (decide (2 ≤ n - 2 * g)) ev₅ (fun hb => ?_) (fun hb => ?_)
  · -- Two blocks.
    obtain h2 : 2 ≤ n - 2 * g := by simpa using hb
    rw [storeFull_eq]
    simp only [List.append_assoc]
    refine ss_step hp' (k := 0) (by omega_arith) (by omega_arith) x₀ fun s₆ x₆ => ?_
    refine ss_step hp' (k := 1) (by omega_arith) (by omega_arith) x₆ fun s₇ x₇ => ?_
    refine ss_step hp' (k := 2) (by omega_arith) (by omega_arith) x₇ fun s₈ x₈ => ?_
    refine ss_step hp' (k := 3) (by omega_arith) (by omega_arith) x₈ fun s₉ x₉ => ?_
    refine ss_step hp' (k := 4) (by omega_arith) (by omega_arith) x₉ fun s₁₀ x₁₀ => ?_
    refine ss_step hp' (k := 5) (by omega_arith) (by omega_arith) x₁₀ fun s₁₁ x₁₁ => ?_
    refine ss_step hp' (k := 6) (by omega_arith) (by omega_arith) x₁₁ fun s₁₂ x₁₂ => ?_
    refine ss_step hp' (k := 7) (by omega_arith) (by omega_arith) x₁₂ fun s₁₃ x₁₃ => ?_
    refine wp_add (op2_imm (by decide)) fun s₁₄ u₁₄ => wp_sub (op2_imm (by decide)) fun s₁₅ u₁₅ =>
      WP.block_nil ?_
    obtain ⟨c1, c2, c3, c4, c5⟩ := fin s₁₅ (by rw [u₁₅.mem, u₁₄.mem]; exact x₁₃.frame)
      (fun r _ h2 h3 => by rw [u₁₅.other _ h3, u₁₄.other _ h2, x₁₃.gpr])
      (by rw [u₁₅.rd, u₁₄.rd, x₁₃.rd]) (by rw [u₁₅.wr, u₁₄.wr, x₁₃.wr]) (by rw [u₁₅.sp, u₁₄.sp, x₁₃.sp])
    refine ⟨c1, c2, c3, c4, c5, ?_⟩
    obtain e₁₀ : s₁₅.gpr .r10 = Dp + BitVec.ofNat 32 (32 * (g + 1)) := by
      rw [u₁₅.other _ (by decide), u₁₄.gpr, x₁₃.gpr, hp'.r10]
      rw [BitVec.add_assoc, show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl, ← BitVec.ofNat_add]
      congr 2
    obtain e₁₁ : s₁₅.gpr .r11 = BitVec.ofNat 32 (n - 2 * (g + 1)) := by
      rw [u₁₅.gpr, u₁₄.other _ (by decide), x₁₃.gpr, hp'.r11]
      bv_omega
    obtain d : EcbInv m₀ s₁₅.mem (State.addr Dp) n (8 * (g + 1)) F := by
      rw [u₁₅.mem, u₁₄.mem]; exact x₁₃.data
    by_cases hl : n - 2 * g = 2
    · exact .inl ⟨by rw [e₁₁, show n - 2 * (g + 1) = 0 by omega_arith]; rfl,
        ecbInv_mono d (by omega_arith) (by omega_arith)⟩
    · exact .inr ⟨by omega_arith, d, e₁₀, e₁₁⟩
  · -- The last block.
    obtain h1 : n - 2 * g = 1 := by simp at hb; omega_arith
    rw [storeTail_eq]
    simp only [List.append_assoc]
    refine ss_step hp' (k := 0) (by omega_arith) (by omega_arith) x₀ fun s₆ x₆ => ?_
    refine ss_step hp' (k := 1) (by omega_arith) (by omega_arith) x₆ fun s₇ x₇ => ?_
    refine ss_step hp' (k := 2) (by omega_arith) (by omega_arith) x₇ fun s₈ x₈ => ?_
    refine ss_step hp' (k := 3) (by omega_arith) (by omega_arith) x₈ fun s₉ x₉ => ?_
    refine wp_mov (op2_imm (by decide)) fun s₁₀ u₁₀ => WP.block_nil ?_
    obtain ⟨c1, c2, c3, c4, c5⟩ := fin s₁₀ (by rw [u₁₀.mem]; exact x₉.frame)
      (fun r _ _ h3 => by rw [u₁₀.other _ h3, x₉.gpr]) (by rw [u₁₀.rd, x₉.rd]) (by rw [u₁₀.wr, x₉.wr])
      (by rw [u₁₀.sp, x₉.sp])
    refine ⟨c1, c2, c3, c4, c5, .inl ⟨u₁₀.gpr, ?_⟩⟩
    rw [u₁₀.mem]; exact ecbInv_mono x₉.data (by omega_arith) (by omega_arith)

end Store

/-! ## A group -/

/-- What the group loop runs with: `s₂` is the state after the round keys
are bitsliced, `b` the scratch buffer, `Dp` the data (`n` blocks). -/
structure ESetup (s₂ : State) (b Dp : BitVec 32) (n R : Nat) (w : List Byte) : Prop where
  scr : (⟨State.addr b, 2048⟩ : Region) ∈ s₂.wr
  fit : b.toNat + 2048 ≤ 2 ^ 32
  dat : (⟨State.addr Dp, 16 * n⟩ : Region) ∈ s₂.wr
  fitD : Dp.toNat + 16 * n ≤ 2 ^ 32
  sep : Region.Disjoint ⟨State.addr Dp, 16 * n⟩ ⟨State.addr b, 2048⟩
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  keys : KeysAt s₂.mem (b + BitVec.ofNat 32 (lastKey - 32 * R)) R w

/-- Before group `g`. -/
structure EInv (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (m₀ : Mem) (s₂ : State)
    (b Dp : BitVec 32) (n R : Nat) (w : List Byte) (g : Nat) (s : State) : Prop where
  hg : 2 * g < n
  r10 : s.gpr .r10 = Dp + BitVec.ofNat 32 (32 * g)
  r11 : s.gpr .r11 = BitVec.ofNat 32 (n - 2 * g)
  r12 : s.gpr .r12 = b + BitVec.ofNat 32 (lastKey - 32 * R)
  base : s.gpr sb = b
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  sp : s.sp = s₂.sp
  frame : Frame (gRegions (State.addr b) (State.addr Dp) n) s₂.mem s.mem
  data : EcbInv m₀ s.mem (State.addr Dp) n (8 * g) (ecbOut f m₀ (State.addr Dp) R w)

/-- After the last group. -/
structure EDone (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (m₀ : Mem) (s₂ : State)
    (b Dp : BitVec 32) (n R : Nat) (w : List Byte) (s : State) : Prop where
  base : s.gpr sb = b
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  sp : s.sp = s₂.sp
  frame : Frame (gRegions (State.addr b) (State.addr Dp) n) s₂.mem s.mem
  data : EcbInv m₀ s.mem (State.addr Dp) n (4 * n) (ecbOut f m₀ (State.addr Dp) R w)

/-- The memory after `groupSave`. -/
def saveMem (m : Mem) (B : Addr) (d l f : BitVec 32) : Mem :=
  ((m.writeW (slotA B dSlot) d).writeW (slotA B lSlot) l).writeW (slotA B fkSlot) f

theorem save_frame (m : Mem) (B : Addr) (d l f : BitVec 32) :
    Frame [⟨B + BitVec.ofNat 64 176, 16⟩] m (saveMem m B d l f) := by
  obtain c : ∀ k, 44 ≤ k → k < 48 →
      (⟨B + BitVec.ofNat 64 176, 16⟩ : Region).Contains (slotA B k) (32 / 8) := by
    intro k h1 h2
    simp only [Region.Contains, slotA]
    rw [show B + BitVec.ofNat 64 (4 * k) - (B + BitVec.ofNat 64 176) = BitVec.ofNat 64 (4 * k - 176) by
      bv_omega, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  exact (((Frame.refl _ m).writeW (List.mem_singleton_self _) _ (c 45 (by omega_arith) (by omega_arith))).writeW
    (List.mem_singleton_self _) _ (c 46 (by omega_arith) (by omega_arith))).writeW (List.mem_singleton_self _) _
    (c 47 (by omega_arith) (by omega_arith))

theorem save_read (m : Mem) (B : Addr) (d l f : BitVec 32) :
    (saveMem m B d l f).readW (slotA B dSlot) 32 = d ∧
      (saveMem m B d l f).readW (slotA B lSlot) 32 = l ∧
      (saveMem m B d l f).readW (slotA B fkSlot) 32 = f := by
  simp only [saveMem]
  refine ⟨?_, ?_, Mem.readW_writeW_self32 _ _ _⟩
  · rw [readW_writeW_slot _ _ (by decide) (by decide) (by decide),
      readW_writeW_slot _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [readW_writeW_slot _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]

/-- `groupSave`, and whether two blocks are left. -/
theorem front_wp {s : State} {b : BitVec 32} (hb : s.gpr sb = b)
    (hscr : (⟨State.addr b, 2048⟩ : Region) ∈ s.wr) (hfit : b.toNat + 2048 ≤ 2 ^ 32) {P : State → Prop}
    (h : ∀ s', s'.gpr kp = s.gpr .r12 → (∀ r, r ≠ kp → r ≠ .lr → s'.gpr r = s.gpr r) →
      s'.mem = saveMem s.mem (State.addr b) (s.gpr .r10) (s.gpr .r11) (s.gpr .r12) →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Arm.eval .ne s' = some (!(s.gpr .r11 >>> 1 - 0 == 0)) → P s') :
    WP isa (.block (groupSave ++ ([.mov .lr (lsrOp .r11 1), .cmp .lr (.imm 0)] : List Instr))) s P := by
  simp only [groupSave, List.cons_append, List.nil_append]
  refine wp_stS hb hscr hfit (by decide) fun s₁ u₁ => ?_
  refine wp_stS (u₁.gpr ▸ hb) (u₁.wr ▸ hscr) hfit (by decide) fun s₂ u₂ => ?_
  refine wp_stS (u₂.gpr ▸ u₁.gpr ▸ hb) (u₂.wr ▸ u₁.wr ▸ hscr) hfit (by decide) fun s₃ u₃ => ?_
  refine wp_mov (op2_reg _ _) fun s₄ u₄ => ?_
  refine wp_mov (op2_lsr (by decide)) fun s₅ u₅ => wp_cmp (op2_imm (by decide)) fun s₆ f₆ z₆ =>
    WP.block_nil (h s₆ ?_ (fun r h1 h2 => ?_) ?_ ?_ ?_ ?_ ?_)
  · rw [f₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr]
  · rw [f₆.gpr, u₅.other _ h2, u₄.other _ h1, u₃.gpr, u₂.gpr, u₁.gpr]
  · rw [f₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₂.gpr, u₁.gpr]; rfl
  · rw [f₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [f₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [f₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  · rw [Arm.eval, z₆, u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.gpr]

/-- The load phase: the blocks left (two, or the last one), in the words. -/
theorem load_wp {s : State} {Dp : BitVec 32} {n g : Nat} (hg : 2 * g < n)
    (hfit : Dp.toNat + 16 * n ≤ 2 ^ 32) (hdat : (⟨State.addr Dp, 16 * n⟩ : Region) ∈ s.wr)
    (h10 : s.gpr .r10 = Dp + BitVec.ofNat 32 (32 * g))
    (hz : Arm.eval .ne s = some (decide (2 ≤ n - 2 * g))) {P : State → Prop}
    (h : ∀ s', (∀ c < 2, 2 * g + c < n → ∀ k < 4, s'.gpr (q (2 * k + c)) =
        s.mem.readW (State.addr Dp + BitVec.ofNat 64 (16 * (2 * g + c)) + BitVec.ofNat 64 (4 * k)) 32) →
      (∀ r, (∀ c < 2, ∀ k < 4, r ≠ q (2 * k + c)) → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → P s') :
    WP isa (.ite .ne (.block (loadBlock 0 ++ loadBlock 1)) (.block (loadBlock 0))) s P := by
  refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
  · have h2 : 2 ≤ n - 2 * g := by simpa using hb
    rw [WP.block_append_iff (M := isa)]
    refine loadBlock_wp (g := g) (c := 0) (by omega_arith) (by omega_arith) hfit hdat h10
      fun s₁ v₁ o₁ m₁ rd₁ wr₁ sp₁ => ?_
    refine loadBlock_wp (g := g) (c := 1) (by omega_arith) (by omega_arith) hfit (wr₁ ▸ hdat)
      (by rw [o₁ _ fun k hk => (q_blk 0 (by omega_arith) k hk).1.symm]; exact h10)
      fun s₂ v₂ o₂ m₂ rd₂ wr₂ sp₂ => h s₂ (fun c hc _ k hk => ?_) (fun r hr => ?_)
        (by rw [m₂, m₁]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) (by rw [sp₂, sp₁])
    · rcases (show c = 0 ∨ c = 1 by omega_arith) with rfl | rfl
      · rw [o₂ _ fun j hj => q_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith), v₁ k hk]
      · rw [v₂ k hk, m₁]
    · rw [o₂ _ (hr 1 (by omega_arith)), o₁ _ (hr 0 (by omega_arith))]
  · have h1 : n - 2 * g = 1 := by simp at hb; omega_arith
    exact loadBlock_wp (g := g) (c := 0) (by omega_arith) (by omega_arith) hfit hdat h10
      fun s₁ v₁ o₁ m₁ rd₁ wr₁ sp₁ => h s₁ (fun c hc hcn k hk => by
        rcases (show c = 0 by omega_arith) with rfl
        exact v₁ k hk) (fun r hr => o₁ _ (hr 0 (by omega_arith))) m₁ rd₁ wr₁ sp₁

/-- One group: from before group `g`, to after the last group or before
group `g + 1`. -/
theorem group_ok {crypt2 : Prog isa} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    (hcr : CryptOk crypt2 f) {m₀ : Mem} {s₂ : State} {b Dp : BitVec 32} {n R : Nat} {w : List Byte}
    (hs : ESetup s₂ b Dp n R w) {g : Nat} {s : State} (hi : EInv f m₀ s₂ b Dp n R w g s) :
    WP isa (blockGroup crypt2) s fun s' => (Arm.eval .ne s' = some false ∧ EDone f m₀ s₂ b Dp n R w s') ∨
      (Arm.eval .ne s' = some true ∧ EInv f m₀ s₂ b Dp n R w (g + 1) s') := by
  obtain hR : R ≤ 14 := by rcases hs.rounds with h | h | h <;> omega_arith
  have hfit := hs.fit
  have hfitD := hs.fitD
  have hg := hi.hg
  obtain hscr : (⟨State.addr b, 2048⟩ : Region) ∈ s.wr := hi.wr ▸ hs.scr
  obtain hdat : (⟨State.addr Dp, 16 * n⟩ : Region) ∈ s.wr := hi.wr ▸ hs.dat
  let F := ecbOut f m₀ (State.addr Dp) R w
  unfold blockGroup
  refine WP.seq (front_wp hi.base hscr hfit fun s₁ hkp₁ o₁ m₁ rd₁ wr₁ sp₁ z₁ => ?_)
  obtain hb₁ : s₁.gpr sb = b := (o₁ sb (by decide) (by decide)).trans hi.base
  obtain f₁ : Frame [⟨State.addr b + BitVec.ofNat 64 176, 16⟩] s.mem s₁.mem := by
    rw [m₁]; exact save_frame _ _ _ _ _
  obtain hf₁ : Frame (gRegions (State.addr b) (State.addr Dp) n) s₂.mem s₁.mem :=
    hi.frame.trans (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨State.addr b + BitVec.ofNat 64 176, 20⟩, by simp, front_sub _⟩)
  obtain z₁' : Arm.eval .ne s₁ = some (decide (2 ≤ n - 2 * g)) := by
    rw [z₁, hi.r11, shr1_eq _ (by omega_arith)]
  obtain d₁ : EcbInv m₀ s₁.mem (State.addr Dp) n (8 * g) F :=
    ecbInv_frame f₁ (by simpa using hs.sep.sub_right (scr_sub _ (by omega_arith))) (by omega_arith) hi.data
  refine WP.seq (load_wp hg hfitD (wr₁ ▸ hdat) (by rw [o₁ _ (by decide) (by decide)]; exact hi.r10) z₁'
    fun s₂' v₂ o₂ m₂ rd₂ wr₂ sp₂ => ?_)
  obtain hkp₂ : s₂'.gpr kp = s.gpr .r12 := by
    rw [o₂ _ fun c hc k hk => (q_blk c hc k hk).2.2.2.2.1.symm, hkp₁]
  obtain hb₂ : s₂'.gpr sb = b := by
    rw [o₂ _ fun c hc k hk => (q_blk c hc k hk).2.2.2.1.symm, hb₁]
  obtain hp : EncPre s₂' R w :=
    ⟨by rw [hb₂, wr₂, wr₁, hi.wr]; exact hs.scr, by rw [hb₂]; exact hfit, hs.rounds,
      by rw [hkp₂, hi.r12, hb₂],
      by rw [hkp₂, hi.r12, m₂]; exact keysAt_frame hfit hR hf₁ (keys_disj_regions hs.sep) hs.keys⟩
  obtain hfk : FirstKey s₂' s₂'.mem := by
    rw [FirstKey, hb₂, hkp₂, m₂, m₁]; exact (save_read _ _ _ _ _).2.2
  -- The loaded blocks.
  obtain hld : ∀ c < 2, 2 * g + c < n → regBlock (Q s₂') c = Spec.Aes.stateAt m₀
      (State.addr Dp + BitVec.ofNat 64 (16 * (2 * g + c))) := fun c hc hcn => by
    rw [regBlock_load (m := s₁.mem) fun k hk => v₂ c hc hcn k hk]
    exact stateAt_ecbInv d₁ hcn (by omega_arith)
  refine WP.seq (WP.mono (hcr hp hfk (inRel_regBlock (Q s₂'))) fun s₃ ⟨hc₃, hin₃⟩ => ?_)
  have fr₃ := hc₃.frame
  rw [hb₂] at fr₃
  obtain hb₃ : s₃.gpr sb = b := hc₃.base.trans hb₂
  obtain hscr₃ : (⟨State.addr b, 2048⟩ : Region) ∈ s₃.wr := by rw [hc₃.wr, wr₂, wr₁]; exact hscr
  obtain mslot : ∀ k, 45 ≤ k → k < 48 → s₃.mem.readW (slotA (State.addr b) k) 32 =
      s₁.mem.readW (slotA (State.addr b) k) 32 := fun k h1 h2 => by
    rw [← m₂]
    exact fr₃.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (scr_disj _ (by omega_arith) (by omega_arith)).symm)
      (by decide)
  obtain ⟨rd10, rd11, rd12⟩ := save_read s.mem (State.addr b) (s.gpr .r10) (s.gpr .r11) (s.gpr .r12)
  refine WP.seq ?_
  simp only [groupLoad, List.cons_append, List.nil_append]
  refine wp_ldS hb₃ hscr₃ hfit (by decide) fun s₄ u₄ => ?_
  refine wp_ldS (by rw [u₄.other _ (by decide), hb₃]) (by rw [u₄.wr]; exact hscr₃) hfit (by decide)
    fun s₅ u₅ => ?_
  refine wp_ldS (by rw [u₅.other _ (by decide), u₄.other _ (by decide), hb₃])
    (by rw [u₅.wr, u₄.wr]; exact hscr₃) hfit (by decide) fun s₆ u₆ => ?_
  obtain e10 : s₆.gpr .r10 = Dp + BitVec.ofNat 32 (32 * g) := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, mslot dSlot (by decide) (by decide), m₁,
      rd10, hi.r10]
  obtain e11 : s₆.gpr .r11 = BitVec.ofNat 32 (n - 2 * g) := by
    rw [u₆.other _ (by decide), u₅.gpr, u₄.mem, mslot lSlot (by decide) (by decide), m₁, rd11, hi.r11]
  obtain e12 : s₆.gpr .r12 = b + BitVec.ofNat 32 (lastKey - 32 * R) := by
    rw [u₆.gpr, u₅.mem, u₄.mem, mslot fkSlot (by decide) (by decide), m₁, rd12, hi.r12]
  obtain mm₆ : s₆.mem = s₃.mem := by rw [u₆.mem, u₅.mem, u₄.mem]
  obtain gq₆ : ∀ i < 8, s₆.gpr (q i) = s₃.gpr (q i) := fun i hi' => by
    have : q i ≠ .r10 ∧ q i ≠ .r11 ∧ q i ≠ .r12 := by revert hi'; revert i; decide
    rw [u₆.other _ this.2.2, u₅.other _ this.2.1, u₄.other _ this.1]
  obtain d128 : Region.Disjoint ⟨State.addr Dp, 16 * n⟩ ⟨State.addr b, 128⟩ :=
    hs.sep.sub_right (Region.sub_prefix (by omega_arith))
  obtain hx : SPre m₀ Dp n g F s₆ :=
    { hg := hg, fit := hfitD, dat := by rw [u₆.wr, u₅.wr, u₄.wr, hc₃.wr, wr₂, wr₁]; exact hdat
      r10 := e10, r11 := e11
      data := by
        rw [mm₆]
        exact ecbInv_frame fr₃ (by simpa using d128) (by omega_arith) (by rw [m₂]; exact d₁)
      vals := fun k hk hkn t ht => by
        rw [gq₆ _ (by omega_arith)]
        obtain hcn : 2 * g + k / 4 < n := by omega_arith
        apply byte_ext
        intro j hj
        have := hin₃ (k / 4) (by omega_arith) (4 * (k % 4) + t) (by omega_arith) j hj
        dsimp only at this
        rw [show (4 * (k % 4) + t) / 4 = k % 4 by omega_arith, show (4 * (k % 4) + t) % 4 = t by omega_arith,
          hld _ (by omega_arith) hcn] at this
        rw [BitVec.getLsbD_extractLsb', this, show (4 * (8 * g + k) + t) / 16 = 2 * g + k / 4 by omega_arith,
          show (4 * (8 * g + k) + t) % 16 = 4 * (k % 4) + t by omega_arith]
        simp [hj, F, ecbOut] }
  refine WP.mono (storePhase_wp hx) fun s₇ h₇ => WP.seq (WP.mono h₇ fun s₈ hd₈ => ?_)
  obtain ⟨f₈, o₈, rd₈, wr₈, sp₈, hz⟩ := hd₈
  refine wp_cmp (op2_imm (by decide)) fun s₉ f₉ z₉ => WP.block_nil ?_
  obtain keep : ∀ r, r ∉ layerWrites → r ≠ kp → s₉.gpr r = s.gpr r := by
    intro r h1 h2
    have : r ≠ .lr ∧ r ≠ .r10 ∧ r ≠ .r11 ∧ r ≠ .r12 := by revert h1 h2; cases r <;> decide
    obtain qw : ∀ c < 2, ∀ k < 4, q (2 * k + c) ∈ layerWrites := by decide
    obtain hq : ∀ c < 2, ∀ k < 4, r ≠ q (2 * k + c) := fun c hc k hk h => h1 (h ▸ qw c hc k hk)
    rw [f₉.gpr, o₈ r h2 this.2.1 this.2.2.1, u₆.other _ this.2.2.2, u₅.other _ this.2.2.1,
      u₄.other _ this.2.1, hc₃.keep r h1 h2, o₂ r hq, o₁ r h2 this.1]
  obtain base' : s₉.gpr sb = b := (keep sb (by decide) (by decide)).trans hi.base
  obtain rd' : s₉.rd = s₂.rd := by rw [f₉.rd, rd₈, u₆.rd, u₅.rd, u₄.rd, hc₃.rd, rd₂, rd₁, hi.rd]
  obtain wr' : s₉.wr = s₂.wr := by rw [f₉.wr, wr₈, u₆.wr, u₅.wr, u₄.wr, hc₃.wr, wr₂, wr₁, hi.wr]
  obtain sp' : s₉.sp = s₂.sp := by rw [f₉.sp, sp₈, u₆.sp, u₅.sp, u₄.sp, hc₃.sp, sp₂, sp₁, hi.sp]
  obtain frame' : Frame (gRegions (State.addr b) (State.addr Dp) n) s₂.mem s₉.mem := by
    rw [f₉.mem]
    refine hf₁.trans (?_ : Frame _ s₁.mem s₈.mem)
    rw [← m₂]
    refine (fr₃.mono fun r hr => by simp at hr; simp [hr]).trans ?_
    rw [← mm₆]
    exact f₈.mono fun r hr => by simp at hr; simp [hr]
  obtain ev : Arm.eval .ne s₉ = some (!(s₈.gpr .r11 == 0)) := by
    obtain e0 : ∀ x : BitVec 32, x - (0 : BitVec 32) = x := fun x => by bv_omega
    simp only [Arm.eval, z₉, e0]
  rcases hz with ⟨z, d⟩ | ⟨h4, d, x10, x11⟩
  · exact .inl ⟨by rw [ev, z]; rfl, base', rd', wr', sp', frame', by rw [f₉.mem]; exact d⟩
  · refine .inr ⟨?_, ⟨by omega_arith, by rw [f₉.gpr]; exact x10, by rw [f₉.gpr]; exact x11,
      by rw [f₉.gpr, o₈ _ (by decide) (by decide) (by decide), e12], base', rd', wr', sp',
      frame', by rw [f₉.mem]; exact d⟩⟩
    obtain hne : BitVec.ofNat 32 (n - 2 * (g + 1)) ≠ 0 := by
      intro h; have := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this
      simp at this; omega_arith
    rw [ev, x11]; simpa using hne

/-- The loop over the groups. -/
theorem groups_ok {crypt2 : Prog isa} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    (hcr : CryptOk crypt2 f) {m₀ : Mem} {s₂ : State} {b Dp : BitVec 32} {n R : Nat} {w : List Byte}
    (hs : ESetup s₂ b Dp n R w) {s : State} (hi : EInv f m₀ s₂ b Dp n R w 0 s) :
    WP isa (.loop (blockGroup crypt2) .ne) s (EDone f m₀ s₂ b Dp n R w) := by
  refine WP.loop (M := isa) (fun k s => ∃ g, k = n - 2 * g ∧ EInv f m₀ s₂ b Dp n R w g s)
    (fun k s ⟨g, hk, hg⟩ => WP.mono (group_ok hcr hs hg) fun s' h => ?_) n s ⟨0, by omega_arith, hi⟩
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨z, d⟩
  · exact .inr ⟨z, n - 2 * (g + 1), by have := hg.hg; omega_arith, g + 1, rfl, d⟩

end VG.Proof.Aes.Arm.Ecb
