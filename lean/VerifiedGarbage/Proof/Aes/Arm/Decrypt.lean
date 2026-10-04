import VerifiedGarbage.Impl.Aes.Arm.Blocks
import VerifiedGarbage.Proof.Aes.Arm.Group
import VerifiedGarbage.Proof.Aes.InvSboxSpec
import VerifiedGarbage.Proof.Aes.Ct32.InvBitsliced

/-!
# Decrypting two blocks, bitsliced, on ARMv7

The inverse layers (`Impl/Aes/Arm/Inv.lean`) are checked by evaluation as
the cipher's are (`Sbox.lean`, `Linear.lean`): the inverse S-box on the
truth tables of the 256 inputs against the specification's (`invSboxT`),
the linear layers over the lane domain against the bits that
`Proof/Aes/Ct32/InvBitsliced.lean` gives (whose layout is the one
`Bitsliced.lean` defines here). `decrypt2_ok` composes them: from two
blocks in the registers (`InRel`), with the bitsliced round keys in the
scratch buffer (`EncPre`) and the first one's address in slot `fkSlot`,
`decrypt2` leaves the two plaintexts, having written only the first 128
bytes of the scratch buffer. The round loop's invariant is the
specification's `foldl` over the rounds done, with `kp` stepping down from
the last round key.
-/

namespace VG.Proof.Aes.Arm

open VG VG.Arm VG.Arm.Straight VG.Bitslice VG.Impl.Aes.Arm
open VG.Proof.Aes (invSboxT row_invSboxT getLsbD_row irnd invMid invMid_succ invCipher_eq)
open VG.Spec.Aes (invSbox roundKey invSubBytes invMixColumns addRoundKey invCipher)
open VG.Proof.MdStream.Arm (Upd Fupd op2_imm op2_reg wp_sub wp_cmp)

/-! ## The inverse S-box -/

def invSboxPost (e : Env Nat) : Bool :=
  (List.range 8).all fun j => e.reg (q j) == some ((invSboxT inTs).getD j 0)

theorem invSbox_check :
    check (table 32 256) sboxCfg (fun _ => none) invSboxCode sboxEnv invSboxPost = true := by
  decide +kernel

/-- The inverse S-box, at every bit position of the words in `q 0 … q 7`. -/
theorem invSbox_ok {s : State} (hok : Ok sboxCfg s) :
    ∃ s', runBlock isa invSboxCode s = some s' ∧
      (∀ j < 8, ∀ p < 32,
        (s'.gpr (q j)).getLsbD p = (invSbox (bsByte (fun k => s.gpr (q k)) p)).getLsbD j) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion sboxCfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ invSbox_check
  have hout : ∀ j < 8, e'.reg (q j) = some ((invSboxT inTs).getD j 0) := by
    intro j hj
    have := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
    simpa using this
  have key : ∀ p < 32, ∃ s', runBlock isa invSboxCode s = some s' ∧
      Post (TableRel p (bsByte (fun k => s.gpr (q k)) p).toNat) sboxCfg (fun _ => none) e' s s'
        (fun r => (invSboxCode.all fun i => dstOf i != some r) = false) := by
    intro p hp
    have hc := (bsByte (fun k => s.gpr (q k)) p).isLt
    refine run (table_sound hp hc) hok ⟨fun r a h => ?_, (fun _ _ _ h => by cases h),
      (fun _ _ _ h => by cases h), (fun _ _ h => by cases h)⟩ he
    simp only [sboxEnv, Option.map_eq_some_iff] at h
    obtain ⟨k, hk, rfl⟩ := h
    obtain ⟨hqk, hkr⟩ := List.find?_some hk, List.mem_of_find?_eq_some hk
    have hk8 := List.mem_range.mp hkr
    simp only [beq_iff_eq] at hqk
    subst hqk
    simp only [TableRel, inT, testBit_tableOf, hc, decide_true, Bool.true_and,
      BitVec.testBit_toNat, getLsbD_bsByte _ _ hk8]
  obtain ⟨s', hs', p₀⟩ := key 0 (by omega)
  refine ⟨s', hs', fun j hj p hp => ?_, p₀.rd, p₀.wr, p₀.sp, fun r hr => p₀.other r ?_, p₀.frame⟩
  · obtain ⟨s'', hs'', p₁⟩ := key p hp
    obtain rfl := run_unique hs'' hs'
    have hc := (bsByte (fun k => s.gpr (q k)) p).isLt
    have := p₁.rel.reg (q j) _ (hout j hj)
    simp only [TableRel] at this
    rw [← this, ← getLsbD_row _ _ hj, row_invSboxT _ hc, row_inTs hc]
    simp
  · simp [writes_rest (is := invSboxCode) (by decide +kernel) r hr]

/-! ## The linear layers -/

theorem invShiftRows_check :
    check (lanes 32 8) linCfg (linExt 0) Impl.Aes.Arm.invShiftRows (linEnv qIns)
      (linPost 8 (qOuts Ct32.invSrG)) = true := by
  decide +kernel

theorem invMixColumns_check :
    check (lanes 32 8) linCfg (linExt 0) Impl.Aes.Arm.invMixColumns (linEnv qIns)
      (linPost 8 (qOuts Ct32.invMcG)) = true := by
  decide +kernel

theorem invShiftRows_ok {s : State} (hok : Ok linCfg s) :
    ∃ s', runBlock isa Impl.Aes.Arm.invShiftRows s = some s' ∧
      (∀ j < 8, ∀ p < 32, (Q s' j).getLsbD p = (Q s j).getLsbD (Ct32.invSrSrc p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion linCfg s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, rest⟩ := q_linear invShiftRows_check (by decide) (by decide +kernel) hok
    (Q s) (fun _ _ => rfl) (fun j hj => by simp [sboxCfg] at hj)
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, Ct32.invSrG, Straight.xorBits_cons, Straight.xorBits_nil, Bool.xor_false,
    Straight.bitOf_word _ _ _ (by simp only [Ct32.invSrSrc]; omega)]

theorem invMixColumns_ok {s : State} (hok : Ok linCfg s) :
    ∃ s', runBlock isa Impl.Aes.Arm.invMixColumns s = some s' ∧
      (∀ j < 8, ∀ p < 32, (Q s' j).getLsbD p = termsXor (Q s) (Ct32.invMcTerms j p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion linCfg s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, rest⟩ := q_linear invMixColumns_check (by decide) (by decide +kernel) hok
    (Q s) (fun _ _ => rfl) (fun j hj => by simp [sboxCfg] at hj)
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, Ct32.invMcG, xorBits_map]
  intro wt hwt
  obtain ⟨wk, -, rfl⟩ := List.mem_map.mp hwt
  exact Nat.mod_lt _ (by decide)

/-! ## The layers on the states -/

/-- `BsRel` here is the 32-bit layout's (`Proof/Aes/Ct32/Bitsliced.lean`). -/
theorem bsRel_ct32 {Q : Nat → BitVec 32} {S : Nat → Spec.Aes.State} (h : BsRel Q S) :
    Ct32.BsRel Q S := h

theorem bs_invSubBytes {Q Q' : Nat → BitVec 32} {S : Nat → Spec.Aes.State}
    (h : ∀ j < 8, ∀ p < 32, (Q' j).getLsbD p = (invSbox (bsByte Q p)).getLsbD j) (hr : BsRel Q S) :
    BsRel Q' fun b => invSubBytes (S b) :=
  Ct32.bs_invSubBytes h (bsRel_ct32 hr)

theorem bs_invShiftRows {Q Q' : Nat → BitVec 32} {S : Nat → Spec.Aes.State}
    (h : ∀ j < 8, ∀ p < 32, (Q' j).getLsbD p = (Q j).getLsbD (Ct32.invSrSrc p)) (hr : BsRel Q S) :
    BsRel Q' fun b => Spec.Aes.invShiftRows (S b) :=
  Ct32.bs_invShiftRows h (bsRel_ct32 hr)

theorem bs_invMixColumns {Q Q' : Nat → BitVec 32} {S : Nat → Spec.Aes.State}
    (h : ∀ j < 8, ∀ p < 32, (Q' j).getLsbD p = termsXor Q (Ct32.invMcTerms j p)) (hr : BsRel Q S) :
    BsRel Q' fun b => invMixColumns (S b) :=
  Ct32.bs_invMixColumns h (bsRel_ct32 hr)

/-! ## The rounds -/

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

theorem kp_back (K : BitVec 32) {m : Nat} (hm : 0 < m) :
    K + BitVec.ofNat 32 (32 * m) - BitVec.ofNat 32 32 = K + BitVec.ofNat 32 (32 * (m - 1)) := by
  rw [show 32 * m = 32 * (m - 1) + 32 by omega, BitVec.ofNat_add, ← BitVec.add_assoc,
    BitVec.add_sub_cancel]

/-- `sub kp, kp, #32`. -/
theorem subKp_wp {s₀ s : State} {P : State → Prop} (hc : Ctx s₀ s)
    (h : ∀ s', Ctx s₀ s' → s'.gpr kp = s.gpr kp - BitVec.ofNat 32 32 → (∀ i, Q s' i = Q s i) → P s') :
    WP isa (.block [.dp .sub kp kp (.imm 32)]) s P :=
  wp_sub (op2_imm (by decide)) fun s' u => WP.block_nil (h s'
    (hc.step u.rd u.wr u.sp (fun r _ hr => u.other r hr) (by rw [u.mem]; exact Frame.refl _ _))
    u.gpr fun i => u.other _ (q_ne_kp i))

/-- `add kp, sb, #lastKey`. -/
theorem kpLast_wp {s₀ s : State} {P : State → Prop} (hc : Ctx s₀ s)
    (h : ∀ s', Ctx s₀ s' → s'.gpr kp = s.gpr sb + BitVec.ofNat 32 lastKey → (∀ i, Q s' i = Q s i) →
      P s') :
    WP isa (.block [.dp .add kp sb (.imm (BitVec.ofNat 32 lastKey))]) s P :=
  VG.Proof.MdStream.Arm.wp_add (op2_imm (by decide)) fun s' u => WP.block_nil (h s'
    (hc.step u.rd u.wr u.sp (fun r _ hr => u.other r hr) (by rw [u.mem]; exact Frame.refl _ _))
    u.gpr fun i => u.other _ (q_ne_kp i))

theorem z_first (K : BitVec 32) {m : Nat} (hm : m < 15) :
    (K + BitVec.ofNat 32 (32 * m) - K - BitVec.ofNat 32 32 == 0) = decide (m = 1) := by
  by_cases h : m = 1
  · subst h
    have : K + BitVec.ofNat 32 (32 * 1) - K - BitVec.ofNat 32 32 = 0 := by bv_omega
    simp [this]
  · have : K + BitVec.ofNat 32 (32 * m) - K - BitVec.ofNat 32 32 ≠ 0 := by
      intro h'; apply h; bv_omega
    simpa [h] using this

/-- `ldr t0, [sb, #fkSlot]; sub t0, kp, t0; cmp t0, #32`. -/
theorem cmpFirst_wp {s₀ s : State} {R : Nat} {w : List Byte} {P : State → Prop} (hp : EncPre s₀ R w)
    (hc : Ctx s₀ s) (hfk : FirstKey s₀ s.mem)
    (h : ∀ s', Ctx s₀ s' → s'.gpr kp = s.gpr kp → (∀ i, Q s' i = Q s i) →
      s'.z = (s.gpr kp - s₀.gpr kp - BitVec.ofNat 32 32 == 0) → P s') :
    WP isa (.block [ldS t0 fkSlot, .dp .sub t0 kp (.reg t0), .cmp t0 (.imm 32)]) s P := by
  refine wp_ldS hc.base (by rw [hc.wr]; exact hp.scr) hp.fit (by decide) fun s₁ u₁ => ?_
  refine wp_sub (op2_reg _ _) fun s₂ u₂ => wp_cmp (op2_imm (by decide)) fun s₃ f₃ z₃ =>
    WP.block_nil (h s₃ ?_ ?_ ?_ ?_)
  · refine hc.step (by rw [f₃.rd, u₂.rd, u₁.rd]) (by rw [f₃.wr, u₂.wr, u₁.wr])
      (by rw [f₃.sp, u₂.sp, u₁.sp]) (fun r hr _ => ?_) (by rw [f₃.mem, u₂.mem, u₁.mem]; exact Frame.refl _ _)
    have : r ≠ t0 := fun h => hr (h ▸ by decide)
    rw [f₃.gpr, u₂.other _ this, u₁.other _ this]
  · rw [f₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]
  · intro i; rw [Q, Q, f₃.gpr, u₂.other _ (q_ne_t0 i), u₁.other _ (q_ne_t0 i)]
  · rw [z₃, u₂.gpr, u₁.gpr, u₁.other _ (by decide), hfk]
    rfl

/-- A middle round of the inverse cipher. -/
theorem invRound_ok {s₀ s : State} {R m : Nat} {w : List Byte} {T : Nat → Spec.Aes.State}
    (hp : EncPre s₀ R w) (hfk : FirstKey s₀ s₀.mem) (hc : Ctx s₀ s)
    (hk : s.gpr kp = s₀.gpr kp + BitVec.ofNat 32 (32 * (R - m)))
    (hm : m + 1 < R) (hbs : BsRel (Q s) T) :
    WP isa (.block invRoundBody) s fun s' => Ctx s₀ s' ∧
      s'.gpr kp = s₀.gpr kp + BitVec.ofNat 32 (32 * (R - (m + 1))) ∧
      BsRel (Q s') (fun b => irnd R w m (T b)) ∧ Arm.eval .ne s' = some (!decide (m + 2 = R)) := by
  have hR : R ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  simp only [invRoundBody]
  repeat rw [WP.block_append_iff (M := isa)]
  refine subKp_wp hc fun s₁ hc₁ hk₁ hq₁ => ?_
  rw [hk, kp_back _ (by omega), show R - m - 1 = R - (m + 1) by omega] at hk₁
  have hbs₁ : BsRel (Q s₁) T := by
    have : Q s₁ = Q s := funext hq₁
    rw [this]; exact hbs
  refine layer_wp (invShiftRows_ok (hc₁.linOk hp)) hc₁ fun s₂ hc₂ h₂ hk₂ => ?_
  have hbs₂ := bs_invShiftRows h₂ hbs₁
  refine layer_wp (invSbox_ok (hc₂.linOk hp)) hc₂ fun s₃ hc₃ h₃ hk₃ => ?_
  have hbs₃ := bs_invSubBytes h₃ hbs₂
  refine ark_step hp hc₃ (j := R - (m + 1)) (by rw [hk₃, hk₂, hk₁]) (by omega) hbs₃
    fun s₄ hc₄ hk₄ hbs₄ => ?_
  refine layer_wp (invMixColumns_ok (hc₄.linOk hp)) hc₄ fun s₅ hc₅ h₅ hk₅ => ?_
  have hbs₅ := bs_invMixColumns h₅ hbs₄
  have hk₅' : s₅.gpr kp = s₀.gpr kp + BitVec.ofNat 32 (32 * (R - (m + 1))) := by
    rw [hk₅, hk₄, hk₃, hk₂, hk₁]
  refine cmpFirst_wp hp hc₅ (firstKey_ctx hc₅ hfk) fun s₆ hc₆ hk₆ hq₆ hz₆ => ⟨hc₆, ?_, ?_, ?_⟩
  · rw [hk₆, hk₅']
  · have : Q s₆ = Q s₅ := funext hq₆
    rw [this]
    intro b hb i hi
    rw [hbs₅ b hb i hi]
    simp only [irnd, show R - 1 - m = R - (m + 1) by omega]
  · simp only [Arm.eval, hz₆, hk₅', z_first _ (show R - (m + 1) < 15 by omega)]
    congr 2
    exact decide_eq_decide.mpr (by omega)

/-- Two blocks, from `InRel` to `InRel` of their decryptions. -/
theorem decrypt2_ok {s₀ : State} {R : Nat} {w : List Byte} {S : Nat → Spec.Aes.State}
    (hp : EncPre s₀ R w) (hfk : FirstKey s₀ s₀.mem) (hin : InRel (Q s₀) S) :
    WP isa decrypt2 s₀ fun s => Ctx s₀ s ∧ InRel (Q s) (fun b => invCipher R w (S b)) := by
  have hR : R ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  have hR1 : 2 ≤ R := by rcases hp.rounds with h | h | h <;> omega
  let A : Nat → Spec.Aes.State := fun b => addRoundKey (S b) (roundKey w R)
  let Inv : Nat → State → Prop := fun n s => ∃ m, n = R - 1 - m ∧ m + 1 < R ∧ Ctx s₀ s ∧
    s.gpr kp = s₀.gpr kp + BitVec.ofNat 32 (32 * (R - m)) ∧
    BsRel (Q s) (fun b => invMid R w m (A b))
  let Mid : State → Prop := fun s => Ctx s₀ s ∧
    s.gpr kp = s₀.gpr kp + BitVec.ofNat 32 (32 * 1) ∧
    BsRel (Q s) (fun b => invMid R w (R - 1) (A b))
  refine WP.seq (WP.mono (Q := Inv (R - 1)) ?_ fun s h => WP.seq (WP.mono (Q := Mid) ?_ fun s h => ?_))
  · -- ortho, the last round key.
    repeat rw [WP.block_append_iff (M := isa)]
    refine layer_wp (ortho_ok ((Ctx.refl s₀).linOk hp)) (Ctx.refl s₀) fun s₁ hc₁ h₁ _ => ?_
    have hbs₁ := bs_of_in h₁ hin
    refine kpLast_wp hc₁ fun s₂ hc₂ hk₂ hq₂ => ?_
    have hbs₂ : BsRel (Q s₂) S := by
      have : Q s₂ = Q s₁ := funext hq₂
      rw [this]; exact hbs₁
    have hk₂' : s₂.gpr kp = s₀.gpr kp + BitVec.ofNat 32 (32 * (R - 0)) := by
      rw [hk₂, hc₁.base, hp.k0, add_ofNat_ofNat]
      congr 2; simp only [lastKey]; omega
    exact ark_step hp hc₂ hk₂' (Nat.le_refl R) hbs₂ fun s₃ hc₃ hk₃ hbs₃ =>
      ⟨0, by omega, by omega, hc₃, by rw [hk₃, hk₂'], hbs₃⟩
  · -- The middle rounds.
    refine WP.loop (M := isa) Inv (fun n s hs => ?_) (R - 1) s h
    obtain ⟨m, rfl, hm, hc, hk, hbs⟩ := hs
    refine WP.mono (invRound_ok hp hfk hc hk hm hbs) fun s' ⟨hc', hk', hbs', hz⟩ => ?_
    by_cases hlast : m + 2 = R
    · refine .inl ⟨hz.trans (by simp [hlast]), hc', ?_, ?_⟩
      · rw [hk']; congr 3; omega
      · rw [show R - 1 = m + 1 by omega]
        intro b hb i hi
        rw [hbs' b hb i hi]; simp only [invMid_succ]
    · refine .inr ⟨hz.trans (by simp [hlast]), R - 1 - (m + 1), by omega, m + 1, rfl, by omega,
        hc', hk', fun b hb i hi => by rw [hbs' b hb i hi]; simp only [invMid_succ]⟩
  · -- The last round, and back to blocks.
    obtain ⟨hc, hk, hbs⟩ := h
    rw [WP.block_append_iff (M := isa)]
    simp only [invLastRound]
    repeat rw [WP.block_append_iff (M := isa)]
    refine subKp_wp hc fun s₁ hc₁ hk₁ hq₁ => ?_
    rw [hk, kp_back _ (by omega)] at hk₁
    have hbs₁ : BsRel (Q s₁) (fun b => invMid R w (R - 1) (A b)) := by
      have : Q s₁ = Q s := funext hq₁
      rw [this]; exact hbs
    refine layer_wp (invShiftRows_ok (hc₁.linOk hp)) hc₁ fun s₂ hc₂ h₂ hk₂ => ?_
    have hbs₂ := bs_invShiftRows h₂ hbs₁
    refine layer_wp (invSbox_ok (hc₂.linOk hp)) hc₂ fun s₃ hc₃ h₃ hk₃ => ?_
    have hbs₃ := bs_invSubBytes h₃ hbs₂
    refine ark_step hp hc₃ (j := 0) (by rw [hk₃, hk₂, hk₁]) (Nat.zero_le R) hbs₃ fun s₄ hc₄ _ hbs₄ => ?_
    refine layer_wp (ortho_ok (hc₄.linOk hp)) hc₄ fun s₅ hc₅ h₅ _ => ⟨hc₅, ?_⟩
    have := in_of_bs h₅ hbs₄
    intro b hb i hi j hj
    rw [this b hb i hi j hj]; simp only [invCipher_eq]; rfl

end VG.Proof.Aes.Arm
