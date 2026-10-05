import VerifiedGarbage.Impl.Aes.Arm.Blocks
import VerifiedGarbage.Proof.Aes.Arm.Ctr32
import VerifiedGarbage.Proof.Aes.InvSboxSpec
import VerifiedGarbage.Proof.Aes.Ct32.InvBitsliced
import VerifiedGarbage.Spec.Aes.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.Arm.Decrypt`. -/
section

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
  (List.range 8).all fun j => e.reg (VG.Impl.Aes.Arm.q j) == some ((invSboxT inTs).getD j 0)

theorem invSbox_check :
    VG.Arm.Straight.check (table 32 256) sboxCfg (fun _ => none) invSboxCode sboxEnv VG.Proof.Aes.Arm.invSboxPost = true := by
  decide +kernel

/-- The inverse S-box, at every bit position of the words in `q 0 … q 7`. -/
theorem invSbox_ok {s : State} (hok : Ok sboxCfg s) :
    ∃ s', runBlock isa invSboxCode s = some s' ∧
      (∀ j < 8, ∀ p < 32,
        (s'.gpr (VG.Impl.Aes.Arm.q j)).getLsbD p = (invSbox (bsByte (fun k => s.gpr (VG.Impl.Aes.Arm.q k)) p)).getLsbD j) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion sboxCfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ VG.Proof.Aes.Arm.invSbox_check
  have hout : ∀ j < 8, e'.reg (VG.Impl.Aes.Arm.q j) = some ((invSboxT inTs).getD j 0) := by
    intro j hj
    have := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
    simpa using this
  have key : ∀ p < 32, ∃ s', runBlock isa invSboxCode s = some s' ∧
      VG.Arm.Straight.Post (TableRel p (bsByte (fun k => s.gpr (VG.Impl.Aes.Arm.q k)) p).toNat) sboxCfg (fun _ => none) e' s s'
        (fun r => (invSboxCode.all fun i => dstOf i != some r) = false) := by
    intro p hp
    have hc := (bsByte (fun k => s.gpr (VG.Impl.Aes.Arm.q k)) p).isLt
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
    have hc := (bsByte (fun k => s.gpr (VG.Impl.Aes.Arm.q k)) p).isLt
    have := p₁.rel.reg (VG.Impl.Aes.Arm.q j) _ (hout j hj)
    simp only [TableRel] at this
    rw [← this, ← getLsbD_row _ _ hj, row_invSboxT _ hc, row_inTs hc]
    simp
  · simp [writes_rest (is := invSboxCode) (by decide +kernel) r hr]

/-! ## The linear layers -/

theorem invShiftRows_check :
    VG.Arm.Straight.check (lanes 32 8) linCfg (linExt 0) Impl.Aes.Arm.invShiftRows (linEnv qIns)
      (linPost 8 (qOuts Ct32.invSrG)) = true := by
  decide +kernel

theorem invMixColumns_check :
    VG.Arm.Straight.check (lanes 32 8) linCfg (linExt 0) Impl.Aes.Arm.invMixColumns (linEnv qIns)
      (linPost 8 (qOuts Ct32.invMcG)) = true := by
  decide +kernel

theorem invShiftRows_ok {s : State} (hok : Ok linCfg s) :
    ∃ s', runBlock isa Impl.Aes.Arm.invShiftRows s = some s' ∧
      (∀ j < 8, ∀ p < 32, (Q s' j).getLsbD p = (Q s j).getLsbD (Ct32.invSrSrc p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion linCfg s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, rest⟩ := q_linear VG.Proof.Aes.Arm.invShiftRows_check (by decide) (by decide +kernel) hok
    (Q s) (fun _ _ => rfl) (fun j hj => by simp [sboxCfg] at hj)
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, Ct32.invSrG, Straight.xorBits_cons, Straight.xorBits_nil, Bool.xor_false,
    Straight.bitOf_word _ _ _ (by simp only [Ct32.invSrSrc]; omega)]

theorem invMixColumns_ok {s : State} (hok : Ok linCfg s) :
    ∃ s', runBlock isa Impl.Aes.Arm.invMixColumns s = some s' ∧
      (∀ j < 8, ∀ p < 32, (Q s' j).getLsbD p = termsXor (Q s) (Ct32.invMcTerms j p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion linCfg s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, rest⟩ := q_linear VG.Proof.Aes.Arm.invMixColumns_check (by decide) (by decide +kernel) hok
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
  Ct32.bs_invSubBytes h (VG.Proof.Aes.Arm.bsRel_ct32 hr)

theorem bs_invShiftRows {Q Q' : Nat → BitVec 32} {S : Nat → Spec.Aes.State}
    (h : ∀ j < 8, ∀ p < 32, (Q' j).getLsbD p = (Q j).getLsbD (Ct32.invSrSrc p)) (hr : BsRel Q S) :
    BsRel Q' fun b => Spec.Aes.invShiftRows (S b) :=
  Ct32.bs_invShiftRows h (VG.Proof.Aes.Arm.bsRel_ct32 hr)

theorem bs_invMixColumns {Q Q' : Nat → BitVec 32} {S : Nat → Spec.Aes.State}
    (h : ∀ j < 8, ∀ p < 32, (Q' j).getLsbD p = termsXor Q (Ct32.invMcTerms j p)) (hr : BsRel Q S) :
    BsRel Q' fun b => invMixColumns (S b) :=
  Ct32.bs_invMixColumns h (VG.Proof.Aes.Arm.bsRel_ct32 hr)

/-! ## The rounds -/

/-- The first round key's address, in slot `fkSlot`. -/
abbrev FirstKey (s₀ : State) (m : Mem) : Prop :=
  m.readW (slotA (State.addr (s₀.gpr sb)) fkSlot) 32 = s₀.gpr kp

theorem firstKey_ctx {s₀ s : State} (hc : VG.Proof.Aes.Arm.Ctx s₀ s)
    (h : VG.Proof.Aes.Arm.FirstKey s₀ s₀.mem) : VG.Proof.Aes.Arm.FirstKey s₀ s.mem := by
  rw [VG.Proof.Aes.Arm.FirstKey, hc.frame.readW (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (scr_disj _ (lx := 128) (y := 4 * fkSlot) (ly := 32 / 8) (by decide) (by decide)).symm)
    (by decide)]
  exact h

theorem kp_back (K : BitVec 32) {m : Nat} (hm : 0 < m) :
    K + BitVec.ofNat 32 (32 * m) - BitVec.ofNat 32 32 = K + BitVec.ofNat 32 (32 * (m - 1)) := by
  rw [show 32 * m = 32 * (m - 1) + 32 by omega, BitVec.ofNat_add, ← BitVec.add_assoc,
    BitVec.add_sub_cancel]

/-- `sub kp, kp, #32`. -/
theorem subKp_wp {s₀ s : State} {P : State → Prop} (hc : VG.Proof.Aes.Arm.Ctx s₀ s)
    (h : ∀ s', VG.Proof.Aes.Arm.Ctx s₀ s' → s'.gpr kp = s.gpr kp - BitVec.ofNat 32 32 → (∀ i, Q s' i = Q s i) → P s') :
    WP isa (.block [.dp .sub kp kp (.imm 32)]) s P :=
  wp_sub (op2_imm (by decide)) fun s' u => WP.block_nil (h s'
    (hc.step u.rd u.wr u.sp (fun r _ hr => u.other r hr) (by rw [u.mem]; exact Frame.refl _ _))
    u.gpr fun i => u.other _ (q_ne_kp i))

/-- `add kp, sb, #lastKey`. -/
theorem kpLast_wp {s₀ s : State} {P : State → Prop} (hc : VG.Proof.Aes.Arm.Ctx s₀ s)
    (h : ∀ s', VG.Proof.Aes.Arm.Ctx s₀ s' → s'.gpr kp = s.gpr sb + BitVec.ofNat 32 lastKey → (∀ i, Q s' i = Q s i) →
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
    (hc : VG.Proof.Aes.Arm.Ctx s₀ s) (hfk : VG.Proof.Aes.Arm.FirstKey s₀ s.mem)
    (h : ∀ s', VG.Proof.Aes.Arm.Ctx s₀ s' → s'.gpr kp = s.gpr kp → (∀ i, Q s' i = Q s i) →
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
    (hp : EncPre s₀ R w) (hfk : VG.Proof.Aes.Arm.FirstKey s₀ s₀.mem) (hc : VG.Proof.Aes.Arm.Ctx s₀ s)
    (hk : s.gpr kp = s₀.gpr kp + BitVec.ofNat 32 (32 * (R - m)))
    (hm : m + 1 < R) (hbs : BsRel (Q s) T) :
    WP isa (.block invRoundBody) s fun s' => VG.Proof.Aes.Arm.Ctx s₀ s' ∧
      s'.gpr kp = s₀.gpr kp + BitVec.ofNat 32 (32 * (R - (m + 1))) ∧
      BsRel (Q s') (fun b => irnd R w m (T b)) ∧ Arm.eval .ne s' = some (!decide (m + 2 = R)) := by
  have hR : R ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  simp only [invRoundBody]
  repeat rw [WP.block_append_iff (M := isa)]
  refine VG.Proof.Aes.Arm.subKp_wp hc fun s₁ hc₁ hk₁ hq₁ => ?_
  rw [hk, VG.Proof.Aes.Arm.kp_back _ (by omega), show R - m - 1 = R - (m + 1) by omega] at hk₁
  have hbs₁ : BsRel (Q s₁) T := by
    have : Q s₁ = Q s := funext hq₁
    rw [this]; exact hbs
  refine layer_wp (VG.Proof.Aes.Arm.invShiftRows_ok (hc₁.linOk hp)) hc₁ fun s₂ hc₂ h₂ hk₂ => ?_
  have hbs₂ := VG.Proof.Aes.Arm.bs_invShiftRows h₂ hbs₁
  refine layer_wp (VG.Proof.Aes.Arm.invSbox_ok (hc₂.linOk hp)) hc₂ fun s₃ hc₃ h₃ hk₃ => ?_
  have hbs₃ := VG.Proof.Aes.Arm.bs_invSubBytes h₃ hbs₂
  refine ark_step hp hc₃ (j := R - (m + 1)) (by rw [hk₃, hk₂, hk₁]) (by omega) hbs₃
    fun s₄ hc₄ hk₄ hbs₄ => ?_
  refine layer_wp (VG.Proof.Aes.Arm.invMixColumns_ok (hc₄.linOk hp)) hc₄ fun s₅ hc₅ h₅ hk₅ => ?_
  have hbs₅ := VG.Proof.Aes.Arm.bs_invMixColumns h₅ hbs₄
  have hk₅' : s₅.gpr kp = s₀.gpr kp + BitVec.ofNat 32 (32 * (R - (m + 1))) := by
    rw [hk₅, hk₄, hk₃, hk₂, hk₁]
  refine VG.Proof.Aes.Arm.cmpFirst_wp hp hc₅ (VG.Proof.Aes.Arm.firstKey_ctx hc₅ hfk) fun s₆ hc₆ hk₆ hq₆ hz₆ => ⟨hc₆, ?_, ?_, ?_⟩
  · rw [hk₆, hk₅']
  · have : Q s₆ = Q s₅ := funext hq₆
    rw [this]
    intro b hb i hi
    rw [hbs₅ b hb i hi]
    simp only [irnd, show R - 1 - m = R - (m + 1) by omega]
  · simp only [Arm.eval, hz₆, hk₅', VG.Proof.Aes.Arm.z_first _ (show R - (m + 1) < 15 by omega)]
    congr 2
    exact decide_eq_decide.mpr (by omega)

/-- Two blocks, from `InRel` to `InRel` of their decryptions. -/
theorem decrypt2_ok {s₀ : State} {R : Nat} {w : List Byte} {S : Nat → Spec.Aes.State}
    (hp : EncPre s₀ R w) (hfk : VG.Proof.Aes.Arm.FirstKey s₀ s₀.mem) (hin : InRel (Q s₀) S) :
    WP isa decrypt2 s₀ fun s => VG.Proof.Aes.Arm.Ctx s₀ s ∧ InRel (Q s) (fun b => invCipher R w (S b)) := by
  have hR : R ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  have hR1 : 2 ≤ R := by rcases hp.rounds with h | h | h <;> omega
  let A : Nat → Spec.Aes.State := fun b => addRoundKey (S b) (roundKey w R)
  let Inv : Nat → State → Prop := fun n s => ∃ m, n = R - 1 - m ∧ m + 1 < R ∧ VG.Proof.Aes.Arm.Ctx s₀ s ∧
    s.gpr kp = s₀.gpr kp + BitVec.ofNat 32 (32 * (R - m)) ∧
    BsRel (Q s) (fun b => invMid R w m (A b))
  let Mid : State → Prop := fun s => VG.Proof.Aes.Arm.Ctx s₀ s ∧
    s.gpr kp = s₀.gpr kp + BitVec.ofNat 32 (32 * 1) ∧
    BsRel (Q s) (fun b => invMid R w (R - 1) (A b))
  refine WP.seq (WP.mono (Q := Inv (R - 1)) ?_ fun s h => WP.seq (WP.mono (Q := Mid) ?_ fun s h => ?_))
  · -- ortho, the last round key.
    repeat rw [WP.block_append_iff (M := isa)]
    refine layer_wp (ortho_ok ((Ctx.refl s₀).linOk hp)) (Ctx.refl s₀) fun s₁ hc₁ h₁ _ => ?_
    have hbs₁ := bs_of_in h₁ hin
    refine VG.Proof.Aes.Arm.kpLast_wp hc₁ fun s₂ hc₂ hk₂ hq₂ => ?_
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
    refine WP.mono (VG.Proof.Aes.Arm.invRound_ok hp hfk hc hk hm hbs) fun s' ⟨hc', hk', hbs', hz⟩ => ?_
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
    refine VG.Proof.Aes.Arm.subKp_wp hc fun s₁ hc₁ hk₁ hq₁ => ?_
    rw [hk, VG.Proof.Aes.Arm.kp_back _ (by omega)] at hk₁
    have hbs₁ : BsRel (Q s₁) (fun b => invMid R w (R - 1) (A b)) := by
      have : Q s₁ = Q s := funext hq₁
      rw [this]; exact hbs
    refine layer_wp (VG.Proof.Aes.Arm.invShiftRows_ok (hc₁.linOk hp)) hc₁ fun s₂ hc₂ h₂ hk₂ => ?_
    have hbs₂ := VG.Proof.Aes.Arm.bs_invShiftRows h₂ hbs₁
    refine layer_wp (VG.Proof.Aes.Arm.invSbox_ok (hc₂.linOk hp)) hc₂ fun s₃ hc₃ h₃ hk₃ => ?_
    have hbs₃ := VG.Proof.Aes.Arm.bs_invSubBytes h₃ hbs₂
    refine ark_step hp hc₃ (j := 0) (by rw [hk₃, hk₂, hk₁]) (Nat.zero_le R) hbs₃ fun s₄ hc₄ _ hbs₄ => ?_
    refine layer_wp (ortho_ok (hc₄.linOk hp)) hc₄ fun s₅ hc₅ h₅ _ => ⟨hc₅, ?_⟩
    have := in_of_bs h₅ hbs₄
    intro b hb i hi j hj
    rw [this b hb i hi j hj]; simp only [invCipher_eq]; rfl

end VG.Proof.Aes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.Arm.Ecb`. -/
section

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

namespace VG.Proof.Aes.Arm.Ecb

open VG VG.Arm VG.Arm.Straight VG.Bitslice VG.Impl.Aes.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg op2_lsr wp_mov wp_add wp_sub wp_cmp
  wp_ldr wp_str)
open VG.Proof.Aes (getD_eq byte_ext)

/-- The state made of the bytes of the words: byte `i` of block `c` is byte
`i mod 4` of word `2 ⌊i / 4⌋ + c`, as `InRel` places them. -/
def regBlock (Q : Nat → BitVec 32) (c : Nat) : Spec.Aes.State :=
  Vector.ofFn fun i => (Q (2 * (i.1 / 4) + c)).extractLsb' (8 * (i.1 % 4)) 8

theorem inRel_regBlock (Q : Nat → BitVec 32) : InRel Q (VG.Proof.Aes.Arm.Ecb.regBlock Q) := by
  intro b _ i hi j hj
  rw [getD_eq _ hi]
  simp [VG.Proof.Aes.Arm.Ecb.regBlock, hj]

/-- What a transformation of two blocks does: `f R w` to each, with the
round keys as `EncPre` has them and the first one's address in slot
`fkSlot`. -/
def CryptOk (crypt2 : Prog isa) (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) : Prop :=
  ∀ {s₀ : State} {R : Nat} {w : List Byte} {S : Nat → Spec.Aes.State}, EncPre s₀ R w →
    VG.Proof.Aes.Arm.FirstKey s₀ s₀.mem → InRel (Q s₀) S →
    WP isa crypt2 s₀ fun s => VG.Proof.Aes.Arm.Ctx s₀ s ∧ InRel (Q s) (fun b => f R w (S b))

theorem encrypt2_cryptOk : VG.Proof.Aes.Arm.Ecb.CryptOk encrypt2 Spec.Aes.cipher := fun hp _ hin => encrypt2_ok hp hin
theorem decrypt2_cryptOk : VG.Proof.Aes.Arm.Ecb.CryptOk decrypt2 Spec.Aes.invCipher := fun hp hfk hin => VG.Proof.Aes.Arm.decrypt2_ok hp hfk hin

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
    (hn : 16 * n ≤ 2 ^ 32) (hk : k < 4 * n) (h : VG.Proof.Aes.Arm.Ecb.EcbInv m₀ m D n k F)
    (hv : ∀ t < 4, v.extractLsb' (8 * t) 8 = (F ((4 * k + t) / 16)).getD ((4 * k + t) % 16) 0) :
    VG.Proof.Aes.Arm.Ecb.EcbInv m₀ (m.writeW (D + BitVec.ofNat 64 (4 * k)) v) D n (k + 1) F ∧
      Frame [⟨D, 16 * n⟩] m (m.writeW (D + BitVec.ofNat 64 (4 * k)) v) := by
  refine ⟨fun i hi => ?_, fun x hx => ?_⟩
  · rw [VG.Proof.Aes.Arm.Ecb.writeW32_apply, off_toNat D (by omega) (by omega)]
    by_cases h1 : 4 * k ≤ i
    · rw [ite_eq_left h1]
      by_cases h2 : i - 4 * k < 4
      · rw [ite_eq_left h2, hv _ h2, ite_eq_left (show i < 4 * (k + 1) by omega),
          show 4 * k + (i - 4 * k) = i by omega]
      · rw [ite_eq_right h2, h i hi, ite_eq_right (show ¬ i < 4 * k by omega),
          ite_eq_right (show ¬ i < 4 * (k + 1) by omega)]
    · rw [ite_eq_right h1, ite_eq_right (show ¬ 2 ^ 64 + i - 4 * k < 4 by omega), h i hi,
        ite_eq_left (show i < 4 * k by omega), ite_eq_left (show i < 4 * (k + 1) by omega)]
  · have hx' : ¬ (x - D).toNat + 1 ≤ 16 * n := hx _ (List.mem_singleton_self _)
    rw [VG.Proof.Aes.Arm.Ecb.writeW32_apply, ite_eq_right]
    have : 4 * k < 2 ^ 64 := by omega
    have : (BitVec.ofNat 64 (4 * k)).toNat = 4 * k := by simp; omega
    bv_omega

theorem ecbInv_mono {m₀ m : Mem} {D : Addr} {n k k' : Nat} {F : Nat → Spec.Aes.State}
    (h : VG.Proof.Aes.Arm.Ecb.EcbInv m₀ m D n k F) (hk : 4 * n ≤ k) (hk' : 4 * n ≤ k') : VG.Proof.Aes.Arm.Ecb.EcbInv m₀ m D n k' F := by
  intro i hi
  rw [h i hi, ite_eq_left (show i < 4 * k by omega), ite_eq_left (show i < 4 * k' by omega)]

theorem ecbInv_frame {m₀ m m' : Mem} {D : Addr} {n k : Nat} {F : Nat → Spec.Aes.State}
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨D, 16 * n⟩ r)
    (hn : 16 * n < 2 ^ 64) (h : VG.Proof.Aes.Arm.Ecb.EcbInv m₀ m D n k F) : VG.Proof.Aes.Arm.Ecb.EcbInv m₀ m' D n k F := fun i hi => by
  rw [← h i hi]
  exact hf.bytes (R := ⟨D, 16 * n⟩) hd (by simp only; omega) hi

/-- The output blocks: `f R w` of the original ones. -/
def ecbOut (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (m₀ : Mem) (D : Addr) (R : Nat)
    (w : List Byte) (j : Nat) : Spec.Aes.State :=
  f R w (Spec.Aes.stateAt m₀ (D + BitVec.ofNat 64 (16 * j)))

/-! ## Loading -/

theorem regBlock_load {Q : Nat → BitVec 32} {m : Mem} {A : Addr} {c : Nat}
    (h : ∀ k < 4, Q (2 * k + c) = m.readW (A + BitVec.ofNat 64 (4 * k)) 32) :
    VG.Proof.Aes.Arm.Ecb.regBlock Q c = Spec.Aes.stateAt m A := by
  apply Vector.ext
  intro i hi
  refine byte_ext fun j hj => ?_
  simp only [VG.Proof.Aes.Arm.Ecb.regBlock, Spec.Aes.stateAt, Vector.getElem_ofFn, BitVec.getLsbD_extractLsb', hj,
    decide_true, Bool.true_and]
  rw [h _ (by omega), readW_bit _ _ (by omega) hj, Offset.add_add,
    show 4 * (i / 4) + i % 4 = i by omega]

/-- Block `j` of the data, while the first `k ≤ 4 j` words are written, is the original one. -/
theorem stateAt_ecbInv {m₀ m : Mem} {D : Addr} {n k j : Nat} {F : Nat → Spec.Aes.State}
    (h : VG.Proof.Aes.Arm.Ecb.EcbInv m₀ m D n k F) (hj : j < n) (hk : k ≤ 4 * j) :
    Spec.Aes.stateAt m (D + BitVec.ofNat 64 (16 * j)) = Spec.Aes.stateAt m₀ (D + BitVec.ofNat 64 (16 * j)) := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Aes.stateAt, Vector.getElem_ofFn]
  rw [Offset.add_add, h _ (by omega), ite_eq_right (by omega)]

theorem q_blk : ∀ c < 2, ∀ k < 4, VG.Impl.Aes.Arm.q (2 * k + c) ≠ .r10 ∧ VG.Impl.Aes.Arm.q (2 * k + c) ≠ .r11 ∧ VG.Impl.Aes.Arm.q (2 * k + c) ≠ .r12 ∧
    VG.Impl.Aes.Arm.q (2 * k + c) ≠ sb ∧ VG.Impl.Aes.Arm.q (2 * k + c) ≠ kp ∧ VG.Impl.Aes.Arm.q (2 * k + c) ≠ .lr := by
  decide

theorem loadBlock_wp {s : State} {Dp : BitVec 32} {n g c : Nat} (hc : c < 2) (hgc : 2 * g + c < n)
    (hfit : Dp.toNat + 16 * n ≤ 2 ^ 32) (hdat : (⟨State.addr Dp, 16 * n⟩ : Region) ∈ s.wr)
    (h10 : s.gpr .r10 = Dp + BitVec.ofNat 32 (32 * g)) {P : State → Prop}
    (h : ∀ s', (∀ k < 4, s'.gpr (VG.Impl.Aes.Arm.q (2 * k + c)) =
        s.mem.readW (State.addr Dp + BitVec.ofNat 64 (16 * (2 * g + c)) + BitVec.ofNat 64 (4 * k)) 32) →
      (∀ r, (∀ k < 4, r ≠ VG.Impl.Aes.Arm.q (2 * k + c)) → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → P s') :
    WP isa (.block (loadBlock c)) s P := by
  have ha : ∀ (s' : State), s'.gpr .r10 = s.gpr .r10 → s'.wr = s.wr → ∀ k < 4,
      State.addr (s'.gpr .r10 + BitVec.ofNat 32 (16 * c + 4 * k)) =
        State.addr Dp + BitVec.ofNat 64 (16 * (2 * g + c)) + BitVec.ofNat 64 (4 * k) ∧
      InRegions (s'.rd ++ s'.wr)
        (State.addr Dp + BitVec.ofNat 64 (16 * (2 * g + c)) + BitVec.ofNat 64 (4 * k)) 4 := by
    intro s' h1 h2 k hk
    have e : State.addr (s'.gpr .r10 + BitVec.ofNat 32 (16 * c + 4 * k)) =
        State.addr Dp + BitVec.ofNat 64 (16 * (2 * g + c)) + BitVec.ofNat 64 (4 * k) := by
      rw [h1, h10, add_ofNat_ofNat, addr_add (by omega), Offset.add_add]
      congr 2; omega
    refine ⟨e, ?_⟩
    have := in_off (List.mem_append_right s'.rd (h2 ▸ hdat)) hfit
      (off := 16 * (2 * g + c) + 4 * k) (n := 4) (by omega) (by omega)
    rwa [addr_add (by omega), ← Offset.add_add] at this
  have qb := VG.Proof.Aes.Arm.Ecb.q_blk c hc
  simp only [loadBlock, List.range, List.range.loop, List.map_cons, List.map_nil]
  obtain ⟨a0, i0⟩ := ha s rfl rfl 0 (by omega)
  refine wp_ldr (by omega) a0 i0 fun s₁ u₁ => ?_
  obtain ⟨a1, i1⟩ := ha s₁ (u₁.other _ (qb 0 (by omega)).1.symm) u₁.wr 1 (by omega)
  refine wp_ldr (by omega) a1 i1 fun s₂ u₂ => ?_
  obtain ⟨a2, i2⟩ := ha s₂ (by rw [u₂.other _ (qb 1 (by omega)).1.symm,
    u₁.other _ (qb 0 (by omega)).1.symm]) (by rw [u₂.wr, u₁.wr]) 2 (by omega)
  refine wp_ldr (by omega) a2 i2 fun s₃ u₃ => ?_
  obtain ⟨a3, i3⟩ := ha s₃ (by rw [u₃.other _ (qb 2 (by omega)).1.symm,
    u₂.other _ (qb 1 (by omega)).1.symm, u₁.other _ (qb 0 (by omega)).1.symm])
    (by rw [u₃.wr, u₂.wr, u₁.wr]) 3 (by omega)
  refine wp_ldr (by omega) a3 i3 fun s₄ u₄ => WP.block_nil (h s₄ (fun k hk => ?_) (fun r hr => ?_)
    (by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]) (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]) (by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]))
  · have hne : ∀ j < 4, j ≠ k → VG.Impl.Aes.Arm.q (2 * k + c) ≠ VG.Impl.Aes.Arm.q (2 * j + c) := fun j hj hjk =>
      q_inj c hc k (by omega) j hj (Ne.symm hjk)
    have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
    · rw [u₄.other _ (hne 3 (by omega) (by omega)), u₃.other _ (hne 2 (by omega) (by omega)),
        u₂.other _ (hne 1 (by omega) (by omega)), u₁.gpr]
    · rw [u₄.other _ (hne 3 (by omega) (by omega)), u₃.other _ (hne 2 (by omega) (by omega)),
        u₂.gpr, u₁.mem]
    · rw [u₄.other _ (hne 3 (by omega) (by omega)), u₃.gpr, u₂.mem, u₁.mem]
    · rw [u₄.gpr, m₃]
  · rw [u₄.other _ (hr 3 (by omega)), u₃.other _ (hr 2 (by omega)), u₂.other _ (hr 1 (by omega)),
      u₁.other _ (hr 0 (by omega))]

/-! ## Storing -/

/-- Word `k` of a group of two blocks: data word `k` from `q (2 (k mod 4) + ⌊k / 4⌋)`. -/
def stw (k : Nat) : List Instr := [.str (VG.Impl.Aes.Arm.q (2 * (k % 4) + k / 4)) .r10 (4 * k)]

theorem storeFull_eq : storeFull = VG.Proof.Aes.Arm.Ecb.stw 0 ++ VG.Proof.Aes.Arm.Ecb.stw 1 ++ VG.Proof.Aes.Arm.Ecb.stw 2 ++ VG.Proof.Aes.Arm.Ecb.stw 3 ++ VG.Proof.Aes.Arm.Ecb.stw 4 ++ VG.Proof.Aes.Arm.Ecb.stw 5 ++ VG.Proof.Aes.Arm.Ecb.stw 6 ++
    VG.Proof.Aes.Arm.Ecb.stw 7 ++ ([.dp .add .r10 .r10 (.imm 32), .dp .sub .r11 .r11 (.imm 2)] : List Instr) := rfl

theorem storeTail_eq : storeTail = VG.Proof.Aes.Arm.Ecb.stw 0 ++ VG.Proof.Aes.Arm.Ecb.stw 1 ++ VG.Proof.Aes.Arm.Ecb.stw 2 ++ VG.Proof.Aes.Arm.Ecb.stw 3 ++
    ([.mov .r11 (.imm 0)] : List Instr) := rfl

/-- After `k` words of the group have been stored, from `s₃`. -/
structure SS (m₀ : Mem) (D : Addr) (n g : Nat) (F : Nat → Spec.Aes.State) (s₃ : State) (k : Nat)
    (s : State) : Prop where
  data : VG.Proof.Aes.Arm.Ecb.EcbInv m₀ s.mem D n (8 * g + k) F
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
  data : VG.Proof.Aes.Arm.Ecb.EcbInv m₀ s₃.mem (State.addr Dp) n (8 * g) F
  vals : ∀ k < 8, 8 * g + k < 4 * n → ∀ t < 4,
    (s₃.gpr (VG.Impl.Aes.Arm.q (2 * (k % 4) + k / 4))).extractLsb' (8 * t) 8 =
      (F ((4 * (8 * g + k) + t) / 16)).getD ((4 * (8 * g + k) + t) % 16) 0

section Store

variable {m₀ : Mem} {Dp : BitVec 32} {n g : Nat} {F : Nat → Spec.Aes.State} {s₃ : State}

theorem ss_step (hp : VG.Proof.Aes.Arm.Ecb.SPre m₀ Dp n g F s₃) {k : Nat} (hk : k < 8) (hkn : 8 * g + k < 4 * n) {s : State}
    (hs : VG.Proof.Aes.Arm.Ecb.SS m₀ (State.addr Dp) n g F s₃ k s) {is : List Instr} {P : State → Prop}
    (h : ∀ s', VG.Proof.Aes.Arm.Ecb.SS m₀ (State.addr Dp) n g F s₃ (k + 1) s' → WP isa (.block is) s' P) :
    WP isa (.block (VG.Proof.Aes.Arm.Ecb.stw k ++ is)) s P := by
  have hn := hp.fit
  have ha : State.addr (s.gpr .r10 + BitVec.ofNat 32 (4 * k)) =
      State.addr Dp + BitVec.ofNat 64 (4 * (8 * g + k)) := by
    rw [hs.gpr, hp.r10, add_ofNat_ofNat, addr_add (by omega)]
    congr 2; omega
  have hin : InRegions s.wr (State.addr Dp + BitVec.ofNat 64 (4 * (8 * g + k))) 4 := by
    have := in_off (hs.wr ▸ hp.dat) hp.fit (off := 4 * (8 * g + k)) (n := 4) (by omega) (by omega)
    rwa [addr_add (by omega)] at this
  simp only [VG.Proof.Aes.Arm.Ecb.stw, List.cons_append, List.nil_append]
  refine wp_str (by omega) ha hin fun s' u => ?_
  have hst := VG.Proof.Aes.Arm.Ecb.ecbInv_step (v := s.gpr (VG.Impl.Aes.Arm.q (2 * (k % 4) + k / 4))) (by omega) hkn hs.data
    (fun t ht => by rw [hs.gpr]; exact hp.vals k hk hkn t ht)
  rw [← u.mem] at hst
  exact h s' ⟨by rw [show 8 * g + (k + 1) = 8 * g + k + 1 by omega]; exact hst.1,
    hs.frame.trans hst.2, by rw [u.gpr, hs.gpr], by rw [u.rd, hs.rd], by rw [u.wr, hs.wr],
    by rw [u.sp, hs.sp]⟩

/-- After the stores: `r11` is zero if no data is left. -/
def SDone (m₀ : Mem) (Dp : BitVec 32) (n g : Nat) (F : Nat → Spec.Aes.State) (s₃ s : State) : Prop :=
  Frame [⟨State.addr Dp, 16 * n⟩] s₃.mem s.mem ∧
    (∀ r, r ≠ kp → r ≠ .r10 → r ≠ .r11 → s.gpr r = s₃.gpr r) ∧
    s.rd = s₃.rd ∧ s.wr = s₃.wr ∧ s.sp = s₃.sp ∧
    ((s.gpr .r11 = 0 ∧ VG.Proof.Aes.Arm.Ecb.EcbInv m₀ s.mem (State.addr Dp) n (4 * n) F) ∨
     (2 * g + 2 < n ∧ VG.Proof.Aes.Arm.Ecb.EcbInv m₀ s.mem (State.addr Dp) n (8 * (g + 1)) F ∧
      s.gpr .r10 = Dp + BitVec.ofNat 32 (32 * (g + 1)) ∧
      s.gpr .r11 = BitVec.ofNat 32 (n - 2 * (g + 1))))

theorem storePhase_wp (hp : VG.Proof.Aes.Arm.Ecb.SPre m₀ Dp n g F s₃) :
    WP isa (.block [.mov kp (lsrOp .r11 1), .cmp kp (.imm 0)]) s₃ fun s =>
      WP isa (.ite .ne (.block storeFull) (.block storeTail)) s (VG.Proof.Aes.Arm.Ecb.SDone m₀ Dp n g F s₃) := by
  have hg := hp.hg
  have hn := hp.fit
  refine wp_mov (op2_lsr (by decide)) fun s₄ u₄ => wp_cmp (op2_imm (by decide)) fun s₅ f₅ z₅ =>
    WP.block_nil ?_
  have ev₅ : Arm.eval .ne s₅ = some (decide (2 ≤ n - 2 * g)) := by
    rw [Arm.eval, z₅, u₄.gpr, hp.r11, shr1_eq _ (by omega)]
  -- The stores start from `s₅`, which differs from `s₃` only in `kp` and the flags.
  let s₃' := s₅
  have x₀ : VG.Proof.Aes.Arm.Ecb.SS m₀ (State.addr Dp) n g F s₃' 0 s₅ :=
    ⟨by rw [f₅.mem, u₄.mem]; exact hp.data, Frame.refl _ _, rfl, rfl, rfl, rfl⟩
  have g₅ : ∀ r, r ≠ kp → s₅.gpr r = s₃.gpr r := fun r hr => by rw [f₅.gpr, u₄.other r hr]
  have hp' : VG.Proof.Aes.Arm.Ecb.SPre m₀ Dp n g F s₃' :=
    { hg := hg, fit := hn, dat := by rw [f₅.wr, u₄.wr]; exact hp.dat
      r10 := by rw [g₅ _ (by decide)]; exact hp.r10
      r11 := by rw [g₅ _ (by decide)]; exact hp.r11
      data := x₀.data
      vals := fun k hk hkn t ht => by
        rw [g₅ _ (q_ctr (k / 4) (by omega) (k % 4) (by omega)).2.2]; exact hp.vals k hk hkn t ht }
  have fin : ∀ s : State, Frame [⟨State.addr Dp, 16 * n⟩] s₅.mem s.mem →
      (∀ r, r ≠ kp → r ≠ .r10 → r ≠ .r11 → s.gpr r = s₅.gpr r) →
      s.rd = s₅.rd → s.wr = s₅.wr → s.sp = s₅.sp →
      Frame [⟨State.addr Dp, 16 * n⟩] s₃.mem s.mem ∧
        (∀ r, r ≠ kp → r ≠ .r10 → r ≠ .r11 → s.gpr r = s₃.gpr r) ∧
        s.rd = s₃.rd ∧ s.wr = s₃.wr ∧ s.sp = s₃.sp := fun s f o rd wr sp =>
    ⟨by rw [← u₄.mem, ← f₅.mem]; exact f, fun r h1 h2 h3 => by rw [o r h1 h2 h3, g₅ r h1],
      by rw [rd, f₅.rd, u₄.rd], by rw [wr, f₅.wr, u₄.wr], by rw [sp, f₅.sp, u₄.sp]⟩
  refine WP.ite (decide (2 ≤ n - 2 * g)) ev₅ (fun hb => ?_) (fun hb => ?_)
  · -- Two blocks.
    have h2 : 2 ≤ n - 2 * g := by simpa using hb
    rw [VG.Proof.Aes.Arm.Ecb.storeFull_eq]
    simp only [List.append_assoc]
    refine VG.Proof.Aes.Arm.Ecb.ss_step hp' (k := 0) (by omega) (by omega) x₀ fun s₆ x₆ => ?_
    refine VG.Proof.Aes.Arm.Ecb.ss_step hp' (k := 1) (by omega) (by omega) x₆ fun s₇ x₇ => ?_
    refine VG.Proof.Aes.Arm.Ecb.ss_step hp' (k := 2) (by omega) (by omega) x₇ fun s₈ x₈ => ?_
    refine VG.Proof.Aes.Arm.Ecb.ss_step hp' (k := 3) (by omega) (by omega) x₈ fun s₉ x₉ => ?_
    refine VG.Proof.Aes.Arm.Ecb.ss_step hp' (k := 4) (by omega) (by omega) x₉ fun s₁₀ x₁₀ => ?_
    refine VG.Proof.Aes.Arm.Ecb.ss_step hp' (k := 5) (by omega) (by omega) x₁₀ fun s₁₁ x₁₁ => ?_
    refine VG.Proof.Aes.Arm.Ecb.ss_step hp' (k := 6) (by omega) (by omega) x₁₁ fun s₁₂ x₁₂ => ?_
    refine VG.Proof.Aes.Arm.Ecb.ss_step hp' (k := 7) (by omega) (by omega) x₁₂ fun s₁₃ x₁₃ => ?_
    refine wp_add (op2_imm (by decide)) fun s₁₄ u₁₄ => wp_sub (op2_imm (by decide)) fun s₁₅ u₁₅ =>
      WP.block_nil ?_
    obtain ⟨c1, c2, c3, c4, c5⟩ := fin s₁₅ (by rw [u₁₅.mem, u₁₄.mem]; exact x₁₃.frame)
      (fun r _ h2 h3 => by rw [u₁₅.other _ h3, u₁₄.other _ h2, x₁₃.gpr])
      (by rw [u₁₅.rd, u₁₄.rd, x₁₃.rd]) (by rw [u₁₅.wr, u₁₄.wr, x₁₃.wr]) (by rw [u₁₅.sp, u₁₄.sp, x₁₃.sp])
    refine ⟨c1, c2, c3, c4, c5, ?_⟩
    have e₁₀ : s₁₅.gpr .r10 = Dp + BitVec.ofNat 32 (32 * (g + 1)) := by
      rw [u₁₅.other _ (by decide), u₁₄.gpr, x₁₃.gpr, hp'.r10]
      rw [BitVec.add_assoc, show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl, ← BitVec.ofNat_add]
      congr 2
    have e₁₁ : s₁₅.gpr .r11 = BitVec.ofNat 32 (n - 2 * (g + 1)) := by
      rw [u₁₅.gpr, u₁₄.other _ (by decide), x₁₃.gpr, hp'.r11]
      bv_omega
    have d : VG.Proof.Aes.Arm.Ecb.EcbInv m₀ s₁₅.mem (State.addr Dp) n (8 * (g + 1)) F := by
      rw [u₁₅.mem, u₁₄.mem]; exact x₁₃.data
    by_cases hl : n - 2 * g = 2
    · exact .inl ⟨by rw [e₁₁, show n - 2 * (g + 1) = 0 by omega]; rfl,
        VG.Proof.Aes.Arm.Ecb.ecbInv_mono d (by omega) (by omega)⟩
    · exact .inr ⟨by omega, d, e₁₀, e₁₁⟩
  · -- The last block.
    have h1 : n - 2 * g = 1 := by simp at hb; omega
    rw [VG.Proof.Aes.Arm.Ecb.storeTail_eq]
    simp only [List.append_assoc]
    refine VG.Proof.Aes.Arm.Ecb.ss_step hp' (k := 0) (by omega) (by omega) x₀ fun s₆ x₆ => ?_
    refine VG.Proof.Aes.Arm.Ecb.ss_step hp' (k := 1) (by omega) (by omega) x₆ fun s₇ x₇ => ?_
    refine VG.Proof.Aes.Arm.Ecb.ss_step hp' (k := 2) (by omega) (by omega) x₇ fun s₈ x₈ => ?_
    refine VG.Proof.Aes.Arm.Ecb.ss_step hp' (k := 3) (by omega) (by omega) x₈ fun s₉ x₉ => ?_
    refine wp_mov (op2_imm (by decide)) fun s₁₀ u₁₀ => WP.block_nil ?_
    obtain ⟨c1, c2, c3, c4, c5⟩ := fin s₁₀ (by rw [u₁₀.mem]; exact x₉.frame)
      (fun r _ _ h3 => by rw [u₁₀.other _ h3, x₉.gpr]) (by rw [u₁₀.rd, x₉.rd]) (by rw [u₁₀.wr, x₉.wr])
      (by rw [u₁₀.sp, x₉.sp])
    refine ⟨c1, c2, c3, c4, c5, .inl ⟨u₁₀.gpr, ?_⟩⟩
    rw [u₁₀.mem]; exact VG.Proof.Aes.Arm.Ecb.ecbInv_mono x₉.data (by omega) (by omega)

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
  data : VG.Proof.Aes.Arm.Ecb.EcbInv m₀ s.mem (State.addr Dp) n (8 * g) (VG.Proof.Aes.Arm.Ecb.ecbOut f m₀ (State.addr Dp) R w)

/-- After the last group. -/
structure EDone (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (m₀ : Mem) (s₂ : State)
    (b Dp : BitVec 32) (n R : Nat) (w : List Byte) (s : State) : Prop where
  base : s.gpr sb = b
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  sp : s.sp = s₂.sp
  frame : Frame (gRegions (State.addr b) (State.addr Dp) n) s₂.mem s.mem
  data : VG.Proof.Aes.Arm.Ecb.EcbInv m₀ s.mem (State.addr Dp) n (4 * n) (VG.Proof.Aes.Arm.Ecb.ecbOut f m₀ (State.addr Dp) R w)

/-- The memory after `groupSave`. -/
def saveMem (m : Mem) (B : Addr) (d l f : BitVec 32) : Mem :=
  ((m.writeW (slotA B dSlot) d).writeW (slotA B lSlot) l).writeW (slotA B fkSlot) f

theorem save_frame (m : Mem) (B : Addr) (d l f : BitVec 32) :
    Frame [⟨B + BitVec.ofNat 64 176, 16⟩] m (VG.Proof.Aes.Arm.Ecb.saveMem m B d l f) := by
  have c : ∀ k, 44 ≤ k → k < 48 →
      (⟨B + BitVec.ofNat 64 176, 16⟩ : Region).Contains (slotA B k) (32 / 8) := by
    intro k h1 h2
    simp only [Region.Contains, slotA]
    rw [show B + BitVec.ofNat 64 (4 * k) - (B + BitVec.ofNat 64 176) = BitVec.ofNat 64 (4 * k - 176) by
      bv_omega, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  exact (((Frame.refl _ m).writeW (List.mem_singleton_self _) _ (c 45 (by omega) (by omega))).writeW
    (List.mem_singleton_self _) _ (c 46 (by omega) (by omega))).writeW (List.mem_singleton_self _) _
    (c 47 (by omega) (by omega))

theorem save_read (m : Mem) (B : Addr) (d l f : BitVec 32) :
    (VG.Proof.Aes.Arm.Ecb.saveMem m B d l f).readW (slotA B dSlot) 32 = d ∧
      (VG.Proof.Aes.Arm.Ecb.saveMem m B d l f).readW (slotA B lSlot) 32 = l ∧
      (VG.Proof.Aes.Arm.Ecb.saveMem m B d l f).readW (slotA B fkSlot) 32 = f := by
  simp only [VG.Proof.Aes.Arm.Ecb.saveMem]
  refine ⟨?_, ?_, Mem.readW_writeW_self32 _ _ _⟩
  · rw [readW_writeW_slot _ _ (by decide) (by decide) (by decide),
      readW_writeW_slot _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [readW_writeW_slot _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]

/-- `groupSave`, and whether two blocks are left. -/
theorem front_wp {s : State} {b : BitVec 32} (hb : s.gpr sb = b)
    (hscr : (⟨State.addr b, 2048⟩ : Region) ∈ s.wr) (hfit : b.toNat + 2048 ≤ 2 ^ 32) {P : State → Prop}
    (h : ∀ s', s'.gpr kp = s.gpr .r12 → (∀ r, r ≠ kp → r ≠ .lr → s'.gpr r = s.gpr r) →
      s'.mem = VG.Proof.Aes.Arm.Ecb.saveMem s.mem (State.addr b) (s.gpr .r10) (s.gpr .r11) (s.gpr .r12) →
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
    (h : ∀ s', (∀ c < 2, 2 * g + c < n → ∀ k < 4, s'.gpr (VG.Impl.Aes.Arm.q (2 * k + c)) =
        s.mem.readW (State.addr Dp + BitVec.ofNat 64 (16 * (2 * g + c)) + BitVec.ofNat 64 (4 * k)) 32) →
      (∀ r, (∀ c < 2, ∀ k < 4, r ≠ VG.Impl.Aes.Arm.q (2 * k + c)) → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → P s') :
    WP isa (.ite .ne (.block (loadBlock 0 ++ loadBlock 1)) (.block (loadBlock 0))) s P := by
  refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
  · have h2 : 2 ≤ n - 2 * g := by simpa using hb
    rw [WP.block_append_iff (M := isa)]
    refine VG.Proof.Aes.Arm.Ecb.loadBlock_wp (g := g) (c := 0) (by omega) (by omega) hfit hdat h10
      fun s₁ v₁ o₁ m₁ rd₁ wr₁ sp₁ => ?_
    refine VG.Proof.Aes.Arm.Ecb.loadBlock_wp (g := g) (c := 1) (by omega) (by omega) hfit (wr₁ ▸ hdat)
      (by rw [o₁ _ fun k hk => (VG.Proof.Aes.Arm.Ecb.q_blk 0 (by omega) k hk).1.symm]; exact h10)
      fun s₂ v₂ o₂ m₂ rd₂ wr₂ sp₂ => h s₂ (fun c hc _ k hk => ?_) (fun r hr => ?_)
        (by rw [m₂, m₁]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) (by rw [sp₂, sp₁])
    · rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl
      · rw [o₂ _ fun j hj => q_ne _ (by omega) _ (by omega) (by omega), v₁ k hk]
      · rw [v₂ k hk, m₁]
    · rw [o₂ _ (hr 1 (by omega)), o₁ _ (hr 0 (by omega))]
  · have h1 : n - 2 * g = 1 := by simp at hb; omega
    exact VG.Proof.Aes.Arm.Ecb.loadBlock_wp (g := g) (c := 0) (by omega) (by omega) hfit hdat h10
      fun s₁ v₁ o₁ m₁ rd₁ wr₁ sp₁ => h s₁ (fun c hc hcn k hk => by
        rcases (show c = 0 by omega) with rfl
        exact v₁ k hk) (fun r hr => o₁ _ (hr 0 (by omega))) m₁ rd₁ wr₁ sp₁

theorem q_keep (r : Reg) (hr : ∀ c < 2, ∀ k < 4, r ≠ VG.Impl.Aes.Arm.q (2 * k + c)) : r ∉ layerWrites ∨ r = .r10 ∨
    r = .r11 ∨ r = .r12 ∨ r = .lr := by
  revert hr; cases r <;> decide

/-- One group: from before group `g`, to after the last group or before
group `g + 1`. -/
theorem group_ok {crypt2 : Prog isa} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    (hcr : VG.Proof.Aes.Arm.Ecb.CryptOk crypt2 f) {m₀ : Mem} {s₂ : State} {b Dp : BitVec 32} {n R : Nat} {w : List Byte}
    (hs : VG.Proof.Aes.Arm.Ecb.ESetup s₂ b Dp n R w) {g : Nat} {s : State} (hi : VG.Proof.Aes.Arm.Ecb.EInv f m₀ s₂ b Dp n R w g s) :
    WP isa (blockGroup crypt2) s fun s' => (Arm.eval .ne s' = some false ∧ VG.Proof.Aes.Arm.Ecb.EDone f m₀ s₂ b Dp n R w s') ∨
      (Arm.eval .ne s' = some true ∧ VG.Proof.Aes.Arm.Ecb.EInv f m₀ s₂ b Dp n R w (g + 1) s') := by
  have hR : R ≤ 14 := by rcases hs.rounds with h | h | h <;> omega
  have hfit := hs.fit
  have hfitD := hs.fitD
  have hg := hi.hg
  have hscr : (⟨State.addr b, 2048⟩ : Region) ∈ s.wr := hi.wr ▸ hs.scr
  have hdat : (⟨State.addr Dp, 16 * n⟩ : Region) ∈ s.wr := hi.wr ▸ hs.dat
  let F := VG.Proof.Aes.Arm.Ecb.ecbOut f m₀ (State.addr Dp) R w
  unfold blockGroup
  refine WP.seq (VG.Proof.Aes.Arm.Ecb.front_wp hi.base hscr hfit fun s₁ hkp₁ o₁ m₁ rd₁ wr₁ sp₁ z₁ => ?_)
  have hb₁ : s₁.gpr sb = b := (o₁ sb (by decide) (by decide)).trans hi.base
  have f₁ : Frame [⟨State.addr b + BitVec.ofNat 64 176, 16⟩] s.mem s₁.mem := by
    rw [m₁]; exact VG.Proof.Aes.Arm.Ecb.save_frame _ _ _ _ _
  have hf₁ : Frame (gRegions (State.addr b) (State.addr Dp) n) s₂.mem s₁.mem :=
    hi.frame.trans (f₁.mono fun r hr => by simp at hr; simp [hr])
  have z₁' : Arm.eval .ne s₁ = some (decide (2 ≤ n - 2 * g)) := by
    rw [z₁, hi.r11, shr1_eq _ (by omega)]
  have d₁ : VG.Proof.Aes.Arm.Ecb.EcbInv m₀ s₁.mem (State.addr Dp) n (8 * g) F :=
    VG.Proof.Aes.Arm.Ecb.ecbInv_frame f₁ (by simpa using hs.sep.sub_right (scr_sub _ (by omega))) (by omega) hi.data
  refine WP.seq (VG.Proof.Aes.Arm.Ecb.load_wp hg hfitD (wr₁ ▸ hdat) (by rw [o₁ _ (by decide) (by decide)]; exact hi.r10) z₁'
    fun s₂' v₂ o₂ m₂ rd₂ wr₂ sp₂ => ?_)
  have hkp₂ : s₂'.gpr kp = s.gpr .r12 := by
    rw [o₂ _ fun c hc k hk => (VG.Proof.Aes.Arm.Ecb.q_blk c hc k hk).2.2.2.2.1.symm, hkp₁]
  have hb₂ : s₂'.gpr sb = b := by
    rw [o₂ _ fun c hc k hk => (VG.Proof.Aes.Arm.Ecb.q_blk c hc k hk).2.2.2.1.symm, hb₁]
  have hp : EncPre s₂' R w :=
    ⟨by rw [hb₂, wr₂, wr₁, hi.wr]; exact hs.scr, by rw [hb₂]; exact hfit, hs.rounds,
      by rw [hkp₂, hi.r12, hb₂],
      by rw [hkp₂, hi.r12, m₂]; exact keysAt_frame hfit hR hf₁ (keys_disj_regions hs.sep) hs.keys⟩
  have hfk : VG.Proof.Aes.Arm.FirstKey s₂' s₂'.mem := by
    rw [VG.Proof.Aes.Arm.FirstKey, hb₂, hkp₂, m₂, m₁]; exact (VG.Proof.Aes.Arm.Ecb.save_read _ _ _ _ _).2.2
  -- The loaded blocks.
  have hld : ∀ c < 2, 2 * g + c < n → VG.Proof.Aes.Arm.Ecb.regBlock (Q s₂') c = Spec.Aes.stateAt m₀
      (State.addr Dp + BitVec.ofNat 64 (16 * (2 * g + c))) := fun c hc hcn => by
    rw [VG.Proof.Aes.Arm.Ecb.regBlock_load (m := s₁.mem) fun k hk => v₂ c hc hcn k hk]
    exact VG.Proof.Aes.Arm.Ecb.stateAt_ecbInv d₁ hcn (by omega)
  refine WP.seq (WP.mono (hcr hp hfk (VG.Proof.Aes.Arm.Ecb.inRel_regBlock (Q s₂'))) fun s₃ ⟨hc₃, hin₃⟩ => ?_)
  have fr₃ := hc₃.frame
  rw [hb₂] at fr₃
  have hb₃ : s₃.gpr sb = b := hc₃.base.trans hb₂
  have hscr₃ : (⟨State.addr b, 2048⟩ : Region) ∈ s₃.wr := by rw [hc₃.wr, wr₂, wr₁]; exact hscr
  have mslot : ∀ k, 45 ≤ k → k < 48 → s₃.mem.readW (slotA (State.addr b) k) 32 =
      s₁.mem.readW (slotA (State.addr b) k) 32 := fun k h1 h2 => by
    rw [← m₂]
    exact fr₃.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (scr_disj _ (by omega) (by omega)).symm)
      (by decide)
  obtain ⟨rd10, rd11, rd12⟩ := VG.Proof.Aes.Arm.Ecb.save_read s.mem (State.addr b) (s.gpr .r10) (s.gpr .r11) (s.gpr .r12)
  refine WP.seq ?_
  simp only [groupLoad, List.cons_append, List.nil_append]
  refine wp_ldS hb₃ hscr₃ hfit (by decide) fun s₄ u₄ => ?_
  refine wp_ldS (by rw [u₄.other _ (by decide), hb₃]) (by rw [u₄.wr]; exact hscr₃) hfit (by decide)
    fun s₅ u₅ => ?_
  refine wp_ldS (by rw [u₅.other _ (by decide), u₄.other _ (by decide), hb₃])
    (by rw [u₅.wr, u₄.wr]; exact hscr₃) hfit (by decide) fun s₆ u₆ => ?_
  have e10 : s₆.gpr .r10 = Dp + BitVec.ofNat 32 (32 * g) := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, mslot dSlot (by decide) (by decide), m₁,
      rd10, hi.r10]
  have e11 : s₆.gpr .r11 = BitVec.ofNat 32 (n - 2 * g) := by
    rw [u₆.other _ (by decide), u₅.gpr, u₄.mem, mslot lSlot (by decide) (by decide), m₁, rd11, hi.r11]
  have e12 : s₆.gpr .r12 = b + BitVec.ofNat 32 (lastKey - 32 * R) := by
    rw [u₆.gpr, u₅.mem, u₄.mem, mslot fkSlot (by decide) (by decide), m₁, rd12, hi.r12]
  have mm₆ : s₆.mem = s₃.mem := by rw [u₆.mem, u₅.mem, u₄.mem]
  have gq₆ : ∀ i < 8, s₆.gpr (VG.Impl.Aes.Arm.q i) = s₃.gpr (VG.Impl.Aes.Arm.q i) := fun i hi' => by
    have : VG.Impl.Aes.Arm.q i ≠ .r10 ∧ VG.Impl.Aes.Arm.q i ≠ .r11 ∧ VG.Impl.Aes.Arm.q i ≠ .r12 := by revert hi'; revert i; decide
    rw [u₆.other _ this.2.2, u₅.other _ this.2.1, u₄.other _ this.1]
  have d128 : Region.Disjoint ⟨State.addr Dp, 16 * n⟩ ⟨State.addr b, 128⟩ :=
    hs.sep.sub_right (Region.sub_prefix (by omega))
  have hx : VG.Proof.Aes.Arm.Ecb.SPre m₀ Dp n g F s₆ :=
    { hg := hg, fit := hfitD, dat := by rw [u₆.wr, u₅.wr, u₄.wr, hc₃.wr, wr₂, wr₁]; exact hdat
      r10 := e10, r11 := e11
      data := by
        rw [mm₆]
        exact VG.Proof.Aes.Arm.Ecb.ecbInv_frame fr₃ (by simpa using d128) (by omega) (by rw [m₂]; exact d₁)
      vals := fun k hk hkn t ht => by
        rw [gq₆ _ (by omega)]
        have hcn : 2 * g + k / 4 < n := by omega
        apply byte_ext
        intro j hj
        have := hin₃ (k / 4) (by omega) (4 * (k % 4) + t) (by omega) j hj
        dsimp only at this
        rw [show (4 * (k % 4) + t) / 4 = k % 4 by omega, show (4 * (k % 4) + t) % 4 = t by omega,
          hld _ (by omega) hcn] at this
        rw [BitVec.getLsbD_extractLsb', this, show (4 * (8 * g + k) + t) / 16 = 2 * g + k / 4 by omega,
          show (4 * (8 * g + k) + t) % 16 = 4 * (k % 4) + t by omega]
        simp [hj, F, VG.Proof.Aes.Arm.Ecb.ecbOut] }
  refine WP.mono (VG.Proof.Aes.Arm.Ecb.storePhase_wp hx) fun s₇ h₇ => WP.seq (WP.mono h₇ fun s₈ hd₈ => ?_)
  obtain ⟨f₈, o₈, rd₈, wr₈, sp₈, hz⟩ := hd₈
  refine wp_cmp (op2_imm (by decide)) fun s₉ f₉ z₉ => WP.block_nil ?_
  have keep : ∀ r, r ∉ layerWrites → r ≠ kp → s₉.gpr r = s.gpr r := by
    intro r h1 h2
    have : r ≠ .lr ∧ r ≠ .r10 ∧ r ≠ .r11 ∧ r ≠ .r12 := by revert h1 h2; cases r <;> decide
    have qw : ∀ c < 2, ∀ k < 4, VG.Impl.Aes.Arm.q (2 * k + c) ∈ layerWrites := by decide
    have hq : ∀ c < 2, ∀ k < 4, r ≠ VG.Impl.Aes.Arm.q (2 * k + c) := fun c hc k hk h => h1 (h ▸ qw c hc k hk)
    rw [f₉.gpr, o₈ r h2 this.2.1 this.2.2.1, u₆.other _ this.2.2.2, u₅.other _ this.2.2.1,
      u₄.other _ this.2.1, hc₃.keep r h1 h2, o₂ r hq, o₁ r h2 this.1]
  have base' : s₉.gpr sb = b := (keep sb (by decide) (by decide)).trans hi.base
  have rd' : s₉.rd = s₂.rd := by rw [f₉.rd, rd₈, u₆.rd, u₅.rd, u₄.rd, hc₃.rd, rd₂, rd₁, hi.rd]
  have wr' : s₉.wr = s₂.wr := by rw [f₉.wr, wr₈, u₆.wr, u₅.wr, u₄.wr, hc₃.wr, wr₂, wr₁, hi.wr]
  have sp' : s₉.sp = s₂.sp := by rw [f₉.sp, sp₈, u₆.sp, u₅.sp, u₄.sp, hc₃.sp, sp₂, sp₁, hi.sp]
  have frame' : Frame (gRegions (State.addr b) (State.addr Dp) n) s₂.mem s₉.mem := by
    rw [f₉.mem]
    refine hf₁.trans (?_ : Frame _ s₁.mem s₈.mem)
    rw [← m₂]
    refine (fr₃.mono fun r hr => by simp at hr; simp [hr]).trans ?_
    rw [← mm₆]
    exact f₈.mono fun r hr => by simp at hr; simp [hr]
  have ev : Arm.eval .ne s₉ = some (!(s₈.gpr .r11 == 0)) := by
    have e0 : ∀ x : BitVec 32, x - (0 : BitVec 32) = x := fun x => by bv_omega
    simp only [Arm.eval, z₉, e0]
  rcases hz with ⟨z, d⟩ | ⟨h4, d, x10, x11⟩
  · exact .inl ⟨by rw [ev, z]; rfl, base', rd', wr', sp', frame', by rw [f₉.mem]; exact d⟩
  · refine .inr ⟨?_, ⟨by omega, by rw [f₉.gpr]; exact x10, by rw [f₉.gpr]; exact x11,
      by rw [f₉.gpr, o₈ _ (by decide) (by decide) (by decide), e12], base', rd', wr', sp',
      frame', by rw [f₉.mem]; exact d⟩⟩
    have hne : BitVec.ofNat 32 (n - 2 * (g + 1)) ≠ 0 := by
      intro h; have := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      simp at this; omega
    rw [ev, x11]; simpa using hne

/-- The loop over the groups. -/
theorem groups_ok {crypt2 : Prog isa} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    (hcr : VG.Proof.Aes.Arm.Ecb.CryptOk crypt2 f) {m₀ : Mem} {s₂ : State} {b Dp : BitVec 32} {n R : Nat} {w : List Byte}
    (hs : VG.Proof.Aes.Arm.Ecb.ESetup s₂ b Dp n R w) {s : State} (hi : VG.Proof.Aes.Arm.Ecb.EInv f m₀ s₂ b Dp n R w 0 s) :
    WP isa (.loop (blockGroup crypt2) .ne) s (VG.Proof.Aes.Arm.Ecb.EDone f m₀ s₂ b Dp n R w) := by
  refine WP.loop (M := isa) (fun k s => ∃ g, k = n - 2 * g ∧ VG.Proof.Aes.Arm.Ecb.EInv f m₀ s₂ b Dp n R w g s)
    (fun k s ⟨g, hk, hg⟩ => WP.mono (VG.Proof.Aes.Arm.Ecb.group_ok hcr hs hg) fun s' h => ?_) n s ⟨0, by omega, hi⟩
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨z, d⟩
  · exact .inr ⟨z, n - 2 * (g + 1), by have := hg.hg; omega, g + 1, rfl, d⟩

end VG.Proof.Aes.Arm.Ecb

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.Arm.Blocks`. -/
section

/-!
# AES on whole blocks on ARMv7: the whole functions

`vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` are `blocks` around
`encrypt2` and `decrypt2`, and are proven at once, for any transformation of
two blocks with `CryptOk`: the prologue saves the callee-saved registers
(as `vg_aes_ctr32`'s does, `Ctr32.lean`), stores `n` in its slot and
bitslices the round keys (`Keys.lean`); the groups (`Ecb.lean`) do the
rest; the epilogue restores the registers.
-/

namespace VG.Proof.Aes

open VG.Arm in
/-- 32-bit ARM contract for `vg_aes_encrypt_blocks(schedule = r0, rounds = r1,
data = r2, n = r3, scratch = [sp])` (and `vg_aes_decrypt_blocks`, with `f` the
inverse cipher): replaces each of the `n` blocks at `data` with `f rounds w`
of it, for the key schedule `w`.

The code may read `schedule` (240 bytes) and the argument on the stack (4
bytes at `sp`), and read and write `data` (`16 n` bytes) and `scratch` (2048
bytes, whose contents on exit are unspecified). These may not overlap each
other, and none may wrap around the end of the (32-bit) address space.
`rounds` is 10, 12 or 14. The pointers, `rounds` and `n` are public; the key
schedule and the data are secret. -/
def blocksArm (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) : Contract Arm.isa where
  pre s :=
    let sched : Region := ⟨State.addr (s.gpr .r0), 240⟩
    let data : Region := ⟨State.addr (s.gpr .r2), 16 * (s.gpr .r3).toNat⟩
    let scratch : Region := ⟨State.addr (stackArg s 0), 2048⟩
    let args : Region := ⟨stackArgAddr s 0, 4⟩
    s.rd = [sched, args] ∧ s.wr = [data, scratch] ∧
    sched.Disjoint data ∧ sched.Disjoint scratch ∧ data.Disjoint scratch ∧
    data.Disjoint args ∧ scratch.Disjoint args ∧
    (s.gpr .r0).toNat + 240 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 16 * (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
    (stackArg s 0).toNat + 2048 ≤ 2 ^ 32 ∧ s.sp.toNat + 4 ≤ 2 ^ 32 ∧
    ((s.gpr .r1).toNat = 10 ∨ (s.gpr .r1).toNat = 12 ∨ (s.gpr .r1).toNat = 14)
  post s s' :=
    Spec.Aes.statesAt s'.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat =
      (Spec.Aes.statesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat).map
        (f (s.gpr .r1).toNat
          (Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r0)) (16 * ((s.gpr .r1).toNat + 1))))
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

end VG.Proof.Aes

namespace VG.Proof.Aes.Arm.Ecb

open VG VG.Arm VG.Arm.Straight VG.Bitslice VG.Impl.Aes.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg op2_lsr wp_mov wp_add wp_sub wp_cmp
  wp_ldr wp_str wp_ldrSp)

section
variable (s₀ : State)

abbrev scP : BitVec 32 := s₀.gpr .r0
abbrev dP : BitVec 32 := s₀.gpr .r2
abbrev nB : Nat := (s₀.gpr .r3).toNat
abbrev bP : BitVec 32 := stackArg s₀ 0
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 4⟩

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [⟨State.addr (VG.Proof.Aes.Arm.Ecb.scP s₀), 240⟩, VG.Proof.Aes.Arm.Ecb.argR s₀]
  wr : s₀.wr = [⟨State.addr (VG.Proof.Aes.Arm.Ecb.dP s₀), 16 * VG.Proof.Aes.Arm.Ecb.nB s₀⟩, ⟨State.addr (VG.Proof.Aes.Arm.Ecb.bP s₀), 2048⟩]
  dSD : Region.Disjoint ⟨State.addr (VG.Proof.Aes.Arm.Ecb.scP s₀), 240⟩ ⟨State.addr (VG.Proof.Aes.Arm.Ecb.dP s₀), 16 * VG.Proof.Aes.Arm.Ecb.nB s₀⟩
  dSS : Region.Disjoint ⟨State.addr (VG.Proof.Aes.Arm.Ecb.scP s₀), 240⟩ ⟨State.addr (VG.Proof.Aes.Arm.Ecb.bP s₀), 2048⟩
  dDS : Region.Disjoint ⟨State.addr (VG.Proof.Aes.Arm.Ecb.dP s₀), 16 * VG.Proof.Aes.Arm.Ecb.nB s₀⟩ ⟨State.addr (VG.Proof.Aes.Arm.Ecb.bP s₀), 2048⟩
  dDA : Region.Disjoint ⟨State.addr (VG.Proof.Aes.Arm.Ecb.dP s₀), 16 * VG.Proof.Aes.Arm.Ecb.nB s₀⟩ (VG.Proof.Aes.Arm.Ecb.argR s₀)
  dSA : Region.Disjoint ⟨State.addr (VG.Proof.Aes.Arm.Ecb.bP s₀), 2048⟩ (VG.Proof.Aes.Arm.Ecb.argR s₀)
  fitS : (VG.Proof.Aes.Arm.Ecb.scP s₀).toNat + 240 ≤ 2 ^ 32
  fitD : (VG.Proof.Aes.Arm.Ecb.dP s₀).toNat + 16 * VG.Proof.Aes.Arm.Ecb.nB s₀ ≤ 2 ^ 32
  fitB : (VG.Proof.Aes.Arm.Ecb.bP s₀).toNat + 2048 ≤ 2 ^ 32
  fitSp : s₀.sp.toNat + 4 ≤ 2 ^ 32
  rounds : (s₀.gpr .r1).toNat = 10 ∨ (s₀.gpr .r1).toNat = 12 ∨ (s₀.gpr .r1).toNat = 14

theorem pre_of {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s₀ : State}
    (h : (Proof.Aes.blocksArm f).pre s₀) : VG.Proof.Aes.Arm.Ecb.Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

theorem arg_in {s : State} (hr : VG.Proof.Aes.Arm.Ecb.argR s ∈ s.rd) : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 4 :=
  ⟨VG.Proof.Aes.Arm.Ecb.argR s, List.mem_append_left _ hr, by simp [Region.Contains]⟩

/-- The stack argument is as on entry. -/
theorem stackArg_frame {s s' : State} {rs : List Region} (hf : Frame rs s.mem s'.mem) (hsp : s'.sp = s.sp)
    (hd : ∀ r ∈ rs, Region.Disjoint (VG.Proof.Aes.Arm.Ecb.argR s) r) : stackArg s' 0 = stackArg s 0 := by
  simp only [stackArg, stackArgAddr, hsp]
  exact hf.readW (by simp [Region.Contains, stackArgAddr]) hd (by decide)

/-- The data after the last group, as states. -/
theorem statesAt_of_ecbInv {m₀ m : Mem} {D : Addr} {n : Nat} {F : Nat → Spec.Aes.State}
    (h : VG.Proof.Aes.Arm.Ecb.EcbInv m₀ m D n (4 * n) F) : Spec.Aes.statesAt m D n = (List.range n).map F := by
  simp only [Spec.Aes.statesAt]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  apply Vector.ext
  intro t ht
  simp only [Spec.Aes.stateAt, Vector.getElem_ofFn]
  rw [Offset.add_add, h _ (by omega), ite_eq_left (show 16 * j + t < 4 * (4 * n) by omega),
    show (16 * j + t) / 16 = j by omega, show (16 * j + t) % 16 = t by omega, getD_eq _ ht]

/-! ## The key loop, counting in the low 4 bits of `lr` -/

theorem and15 {N j : Nat} (hj : j < 16) (hN : 16 * N + 16 ≤ 2 ^ 32) :
    BitVec.ofNat 32 (16 * N + j) &&& 15 = BitVec.ofNat 32 j := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), show (15 : BitVec 32).toNat = 2 ^ 4 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem shr4 {N : Nat} (hN : 16 * N + 16 ≤ 2 ^ 32) : BitVec.ofNat 32 (16 * N) >>> 4 = BitVec.ofNat 32 N := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]
  omega

theorem blocksKeyBody_ok {s₀ : State} {b sc : BitVec 32} {R N : Nat} {w : List Byte}
    (hk : KSetup s₀ b sc R w) (hN : 16 * N + 16 ≤ 2 ^ 32) {j : Nat} {s : State}
    (hi : KInv s₀ b sc R w j s) (hlr : s.gpr .lr = BitVec.ofNat 32 (16 * N + j + 1)) :
    WP isa (.block blocksKeyBody) s fun s' =>
      (j = 0 ∧ Arm.eval .ne s' = some false ∧ KDone s₀ b R w s' ∧ s'.gpr .lr = BitVec.ofNat 32 (16 * N)) ∨
      (0 < j ∧ Arm.eval .ne s' = some true ∧ KInv s₀ b sc R w (j - 1) s' ∧
        s'.gpr .lr = BitVec.ofNat 32 (16 * N + (j - 1) + 1)) := by
  have hR := hk.rounds
  have hjR := hi.hj
  simp only [blocksKeyBody]
  refine keyFront_ok hk hi fun s₃ hr12 hkp hlr₃ hkeep₃ hrd hwr hsp hfr hkeys => ?_
  simp only [blocksKeyStep]
  refine wp_sub (op2_imm (by decide)) fun s₄ u₄ => wp_sub (op2_imm (by decide)) fun s₅ u₅ =>
    wp_sub (op2_imm (by decide)) fun s₆ u₆ => VG.Proof.MdStream.Arm.wp_and (op2_imm (by decide))
    fun s₇ u₇ => wp_cmp (op2_imm (by decide)) fun s₈ f₈ z₈ => WP.block_nil ?_
  have hlr₈ : s₈.gpr .lr = BitVec.ofNat 32 (16 * N + j) := by
    rw [f₈.gpr, u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), hlr₃,
      hlr]
    bv_omega
  have hev : Arm.eval .ne s₈ = some (!(BitVec.ofNat 32 j == 0)) := by
    have e0 : ∀ x : BitVec 32, x - (0 : BitVec 32) = x := fun x => by bv_omega
    simp only [Arm.eval, z₈, e0, u₇.gpr]
    rw [show s₆.gpr .lr = BitVec.ofNat 32 (16 * N + j) by
      rw [← hlr₈, f₈.gpr, u₇.other _ (by decide)], VG.Proof.Aes.Arm.Ecb.and15 (by omega) hN]
  have hkeep : ∀ r, r ∉ keyWrites → s₈.gpr r = s₀.gpr r := by
    intro r hr
    obtain ⟨h1, h2, h3, h4⟩ := keyWrites_not r hr
    have h5 : r ≠ t0 := fun h => h1 (h ▸ by decide)
    rw [f₈.gpr, u₇.other _ h5, u₆.other _ h4, u₅.other _ h3, u₄.other _ h2, hkeep₃ r hr]
  have m₈ : s₈.mem = s₃.mem := by rw [f₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  have rd₈ : s₈.rd = s₀.rd := by rw [f₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, hrd]
  have wr₈ : s₈.wr = s₀.wr := by rw [f₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, hwr]
  have sp₈ : s₈.sp = s₀.sp := by rw [f₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, hsp]
  have kp₈ : s₈.gpr kp = keyAddr b R j - 32 := by
    rw [f₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), hkp]
  have r12₈ : s₈.gpr .r12 = sc + BitVec.ofNat 32 (16 * j) - 16 := by
    rw [f₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, hr12]
  rw [← m₈] at hfr hkeys
  by_cases h0 : j = 0
  · subst h0
    exact .inl ⟨rfl, hev.trans (by decide), ⟨kp₈, rd₈, wr₈, sp₈, hkeep, hfr,
      fun i hiR => hkeys i (by omega) hiR⟩, by rw [hlr₈]; rfl⟩
  · have hne : BitVec.ofNat 32 j ≠ 0 := by
      intro h; have := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      simp at this; omega
    refine .inr ⟨by omega, hev.trans (by simpa using hne),
      ⟨by omega, ?_, ?_, rd₈, wr₈, sp₈, hkeep, hfr, fun i hi' hiR => hkeys i (by omega) hiR⟩,
      by rw [hlr₈, show 16 * N + (j - 1) + 1 = 16 * N + j by omega]⟩
    · rw [r12₈]; bv_omega
    · rw [kp₈]; exact keyAddr_pred b hk.rounds (by omega) hi.hj

theorem blocksKeyLoop_ok {s₀ : State} {b sc : BitVec 32} {R N : Nat} {w : List Byte}
    (hk : KSetup s₀ b sc R w) (hN : 16 * N + 16 ≤ 2 ^ 32) {s : State} (hi : KInv s₀ b sc R w R s)
    (hlr : s.gpr .lr = BitVec.ofNat 32 (16 * N + R + 1)) :
    WP isa (.loop (.block blocksKeyBody) .ne) s fun s' =>
      KDone s₀ b R w s' ∧ s'.gpr .lr = BitVec.ofNat 32 (16 * N) := by
  refine WP.loop (M := isa)
    (fun n s => KInv s₀ b sc R w n s ∧ s.gpr .lr = BitVec.ofNat 32 (16 * N + n + 1))
    (fun n s hs => ?_) R s ⟨hi, hlr⟩
  refine WP.mono (VG.Proof.Aes.Arm.Ecb.blocksKeyBody_ok hk hN hs.1 hs.2) fun s' h => ?_
  rcases h with ⟨_, hev, hd, hl⟩ | ⟨hn, hev, hi', hlr'⟩
  · exact .inl ⟨hev, hd, hl⟩
  · exact .inr ⟨hev, n - 1, by omega, hi', hlr'⟩

theorem correct {crypt2 : Prog isa} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    (hcr : VG.Proof.Aes.Arm.Ecb.CryptOk crypt2 f) {s₀ : State} (hp : VG.Proof.Aes.Arm.Ecb.Pre s₀) :
    WP isa (blocks crypt2) s₀ fun s' =>
      (∀ i < 9, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧ (Proof.Aes.blocksArm f).post s₀ s' := by
  have hR14 : (s₀.gpr .r1).toNat ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  have hfit := hp.fitB
  have hwS : (⟨State.addr (VG.Proof.Aes.Arm.Ecb.bP s₀), 2048⟩ : Region) ∈ s₀.wr := by rw [hp.wr]; simp
  have hwD : (⟨State.addr (VG.Proof.Aes.Arm.Ecb.dP s₀), 16 * VG.Proof.Aes.Arm.Ecb.nB s₀⟩ : Region) ∈ s₀.wr := by rw [hp.wr]; simp
  have hrS : (⟨State.addr (VG.Proof.Aes.Arm.Ecb.scP s₀), 240⟩ : Region) ∈ s₀.rd := by rw [hp.rd]; simp
  have hrA : VG.Proof.Aes.Arm.Ecb.argR s₀ ∈ s₀.rd := by rw [hp.rd]; simp
  let b := VG.Proof.Aes.Arm.Ecb.bP s₀
  let B := State.addr b
  let n := VG.Proof.Aes.Arm.Ecb.nB s₀
  let D := State.addr (VG.Proof.Aes.Arm.Ecb.dP s₀)
  have n16 : 16 * n < 2 ^ 64 := by have := hp.fitD; omega
  have argB : ∀ {lx : Nat}, lx ≤ 2048 → Region.Disjoint (VG.Proof.Aes.Arm.Ecb.argR s₀) ⟨B, lx⟩ := fun h =>
    (hp.dSA.sub_left (Region.sub_prefix h)).symm
  have argD : ∀ {x lx : Nat}, x + lx ≤ 2048 → Region.Disjoint (VG.Proof.Aes.Arm.Ecb.argR s₀) ⟨B + BitVec.ofNat 64 x, lx⟩ :=
    fun h => (hp.dSA.sub_left (sub_scr _ h)).symm
  -- The prologue.
  unfold blocks
  refine WP.seq ?_
  simp only [blocksPrologue, blocksKeySetup, List.cons_append, List.nil_append]
  refine wp_ldrSp (by omega) (a := stackArgAddr s₀ 0) rfl (VG.Proof.Aes.Arm.Ecb.arg_in hrA) fun s₁ u₁ => ?_
  have hb₁ : s₁.gpr .r12 = b := u₁.gpr
  rw [WP.block_append_iff (M := isa)]
  obtain ⟨s₂, h₂, sv₂, g₂, rd₂, wr₂, sp₂, f₂⟩ :=
    save_ok (by decide) (by rw [u₁.wr]; exact hwS) hfit hb₁ save_check12
  refine WP.of_runBlock ⟨s₂, h₂, ?_⟩
  have sv₂' : VG.Proof.Aes.Arm.Saved s₀ B s₂.mem := fun i hi => by
    rw [sv₂ i hi]
    have : sreg i ≠ .r12 := by revert hi; revert i; decide
    exact u₁.other _ this
  have f₀₂ : Frame [⟨B, 4 * 41⟩] s₀.mem s₂.mem := by rw [← u₁.mem]; exact f₂
  have sp₂' : s₂.sp = s₀.sp := by rw [sp₂, u₁.sp]
  have hb₂ : s₂.gpr .r12 = b := by rw [g₂, hb₁]
  have hscr₂ : (⟨B, 2048⟩ : Region) ∈ s₂.wr := by rw [wr₂, u₁.wr]; exact hwS
  -- The key loop's setup.
  have r0₂ : s₂.gpr .r0 = VG.Proof.Aes.Arm.Ecb.scP s₀ := by rw [g₂, u₁.other _ (by decide)]
  have r1₂ : s₂.gpr .r1 = s₀.gpr .r1 := by rw [g₂, u₁.other _ (by decide)]
  have r2₂ : s₂.gpr .r2 = VG.Proof.Aes.Arm.Ecb.dP s₀ := by rw [g₂, u₁.other _ (by decide)]
  have r3₂ : s₂.gpr .r3 = s₀.gpr .r3 := by rw [g₂, u₁.other _ (by decide)]
  refine wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_add (VG.Proof.MdStream.Arm.op2_lsl (by decide))
    fun s₄ u₄ => wp_mov (VG.Proof.MdStream.Arm.op2_lsl (by decide)) fun s₅ u₅ =>
    wp_add (op2_reg _ _) fun s₆ u₆ => wp_add (op2_imm (by decide)) fun s₆' u₆' =>
    wp_mov (op2_reg _ _) fun s₇ u₇ => WP.block_nil ?_
  have m₇ : s₇.mem = s₂.mem := by rw [u₇.mem, u₆'.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆'.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd]
  have wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆'.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr]
  have sp₇ : s₇.sp = s₀.sp := by rw [u₇.sp, u₆'.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂']
  let R := (s₀.gpr .r1).toNat
  let w := Spec.Aes.bytesAt s₀.mem (State.addr (VG.Proof.Aes.Arm.Ecb.scP s₀)) (16 * (R + 1))
  have f₀₇ : Frame [⟨B, 2048⟩] s₀.mem s₇.mem := by
    rw [m₇]
    exact f₀₂.sub fun r hr => ⟨⟨B, 2048⟩, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)⟩
  have hk : KSetup s₇ b (VG.Proof.Aes.Arm.Ecb.scP s₀) R w :=
    { scr := by rw [wr₇]; exact hwS
      fit := hfit
      sch := List.mem_append_left _ (by rw [rd₇]; exact hrS)
      fitS := hp.fitS
      sep := hp.dSS
      rounds := hR14
      w := fun i hi => by
        simp only [w, Spec.Aes.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range hi, Option.map_some, Option.getD_some]
        refine (f₀₇.bytes (R := ⟨State.addr (VG.Proof.Aes.Arm.Ecb.scP s₀), 240⟩) (fun r hr => ?_) (by simp)
          (by simp only; omega)).symm
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.dSS }
  have hi₇ : KInv s₇ b (VG.Proof.Aes.Arm.Ecb.scP s₀) R w R s₇ :=
    { hj := Nat.le_refl _
      r12 := by
        rw [u₇.other _ (by decide), u₆'.other _ (by decide), u₆.other _ (by decide),
          u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), r0₂, u₃.other _ (by decide), r1₂, shl4]
      kp := by
        rw [u₇.other _ (by decide), u₆'.other _ (by decide), u₆.other _ (by decide),
          u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, hb₂]
        simp [keyAddr, lastKey]
      rd := rfl
      wr := rfl
      sp := rfl
      keep := fun _ _ => rfl
      frame := Frame.refl _ _
      done := fun i h1 h2 => absurd h2 (by omega) }
  have hN : 16 * n + 16 ≤ 2 ^ 32 := by
    refine Nat.le_of_not_lt fun hc => ?_
    have hD := hp.fitD
    simp only [n, VG.Proof.Aes.Arm.Ecb.nB] at hc hD
    have hz : State.addr (VG.Proof.Aes.Arm.Ecb.dP s₀) = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [VG.Proof.MdStream.Arm.addr_toNat]; show _ = 0; omega
    refine hp.dDS (State.addr (VG.Proof.Aes.Arm.Ecb.bP s₀)) ?_ (by
      show (State.addr (VG.Proof.Aes.Arm.Ecb.bP s₀) - State.addr (VG.Proof.Aes.Arm.Ecb.bP s₀)).toNat + 1 ≤ 2048; simp)
    show (State.addr (VG.Proof.Aes.Arm.Ecb.bP s₀) - State.addr (VG.Proof.Aes.Arm.Ecb.dP s₀)).toNat + 1 ≤ 16 * VG.Proof.Aes.Arm.Ecb.nB s₀
    have e : State.addr (VG.Proof.Aes.Arm.Ecb.bP s₀) - 0 = State.addr (VG.Proof.Aes.Arm.Ecb.bP s₀) := by bv_omega
    rw [hz, e, VG.Proof.MdStream.Arm.addr_toNat]
    have := (VG.Proof.Aes.Arm.Ecb.bP s₀).isLt
    simp only [VG.Proof.Aes.Arm.Ecb.nB]
    omega
  have lr₇ : s₇.gpr .lr = BitVec.ofNat 32 (16 * n + R + 1) := by
    rw [u₇.other _ (by decide), u₆'.gpr, u₆.gpr, u₅.gpr, u₅.other .r1 (by decide),
      u₄.other .r3 (by decide), u₄.other .r1 (by decide), u₃.other .r3 (by decide),
      u₃.other .r1 (by decide), r3₂, r1₂, shl4]
    simp only [n, VG.Proof.Aes.Arm.Ecb.nB, R]
    bv_omega
  have r8₇ : s₇.gpr .r8 = VG.Proof.Aes.Arm.Ecb.dP s₀ := by
    rw [u₇.gpr, u₆'.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), r2₂]
  -- The key loop.
  refine WP.seq (WP.mono (VG.Proof.Aes.Arm.Ecb.blocksKeyLoop_ok hk hN hi₇ lr₇) fun s₈ ⟨d₈, lr₈⟩ => ?_)
  have f₀₈ : Frame [⟨B, 2048⟩] s₀.mem s₈.mem :=
    f₀₇.trans (d₈.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨⟨B, 2048⟩, by simp, keyArea_sub _⟩)
  have sp₈ : s₈.sp = s₀.sp := by rw [d₈.sp, sp₇]
  have arg₈ : stackArg s₈ 0 = b := VG.Proof.Aes.Arm.Ecb.stackArg_frame f₀₈ sp₈ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact argB (by omega)
  -- After the key loop.
  refine WP.seq ?_
  simp only [blocksKeyDone, List.cons_append, List.nil_append]
  refine wp_add (op2_imm (by decide)) fun s₉ u₉ => wp_mov (op2_reg _ _) fun s₁₀ u₁₀ => ?_
  have sp₁₀ : s₁₀.sp = s₀.sp := by rw [u₁₀.sp, u₉.sp, sp₈]
  have rd₁₀ : s₁₀.rd = s₀.rd := by rw [u₁₀.rd, u₉.rd, d₈.rd, rd₇]
  have wr₁₀ : s₁₀.wr = s₀.wr := by rw [u₁₀.wr, u₉.wr, d₈.wr, wr₇]
  have m₁₀ : s₁₀.mem = s₈.mem := by rw [u₁₀.mem, u₉.mem]
  refine wp_ldrSp (by omega) (a := stackArgAddr s₀ 0) (by simp [stackArgAddr, sp₁₀])
    (by rw [rd₁₀, wr₁₀]; exact VG.Proof.Aes.Arm.Ecb.arg_in hrA) fun s₁₁ u₁₁ => ?_
  have b₁₁ : s₁₁.gpr sb = b := by
    rw [u₁₁.gpr, m₁₀]
    have := arg₈
    simp only [stackArg, stackArgAddr, sp₈] at this
    exact this
  refine wp_mov (op2_lsr (by decide)) fun s₁₂ u₁₂ => ?_
  refine wp_cmp (op2_imm (by decide)) fun s₁₃ f₁₃ z₁₃ => WP.block_nil ?_
  have n₁₂ : s₁₂.gpr .r11 = s₀.gpr .r3 := by
    rw [u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), lr₈,
      VG.Proof.Aes.Arm.Ecb.shr4 hN]
    simp [n]
  have n₁₃ : s₁₃.gpr .r11 = BitVec.ofNat 32 (n - 2 * 0) := by
    rw [f₁₃.gpr, n₁₂]; simp only [n, VG.Proof.Aes.Arm.Ecb.nB, Nat.mul_zero, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have b₁₃ : s₁₃.gpr sb = b := by rw [f₁₃.gpr, u₁₂.other _ (by decide), b₁₁]
  have d₁₃ : s₁₃.gpr .r10 = VG.Proof.Aes.Arm.Ecb.dP s₀ + BitVec.ofNat 32 (32 * 0) := by
    rw [f₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide),
      d₈.keep _ (by decide), r8₇]
    simp
  have k₁₃ : s₁₃.gpr .r12 = b + BitVec.ofNat 32 (lastKey - 32 * R) := by
    rw [f₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr,
      d₈.kp]
    simp only [keyAddr, Nat.sub_zero, BitVec.sub_add_cancel]
  have m₁₃ : s₁₃.mem = s₈.mem := by rw [f₁₃.mem, u₁₂.mem, u₁₁.mem, m₁₀]
  have rd₁₃ : s₁₃.rd = s₀.rd := by rw [f₁₃.rd, u₁₂.rd, u₁₁.rd, rd₁₀]
  have wr₁₃ : s₁₃.wr = s₀.wr := by rw [f₁₃.wr, u₁₂.wr, u₁₁.wr, wr₁₀]
  have sp₁₃ : s₁₃.sp = s₀.sp := by rw [f₁₃.sp, u₁₂.sp, u₁₁.sp, sp₁₀]
  have hs : VG.Proof.Aes.Arm.Ecb.ESetup s₁₃ b (VG.Proof.Aes.Arm.Ecb.dP s₀) n R w :=
    { scr := by rw [wr₁₃]; exact hwS
      fit := hfit
      dat := by rw [wr₁₃]; exact hwD
      fitD := hp.fitD
      sep := hp.dDS
      rounds := hp.rounds
      keys := fun j hj => keyRel_congr (d₈.keys j hj) fun k hk => by
        rw [m₁₃, keyAddr, add_ofNat_ofNat, show lastKey - 32 * R + 32 * j = lastKey - 32 * (R - j) by
          simp only [lastKey]; omega] }
  -- The data is as on entry.
  have data₁₃ : VG.Proof.Aes.Arm.Ecb.EcbInv s₀.mem s₁₃.mem D n (8 * 0) (VG.Proof.Aes.Arm.Ecb.ecbOut f s₀.mem D R w) := by
    intro i hi
    rw [ite_eq_right (by omega), m₁₃]
    refine f₀₈.bytes (R := ⟨D, 16 * n⟩) (fun r hr => ?_) (by simp only; omega) hi
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.dDS
  refine WP.seq (WP.mono (Q := VG.Proof.Aes.Arm.Ecb.EDone f s₀.mem s₁₃ b (VG.Proof.Aes.Arm.Ecb.dP s₀) n R w) ?_ fun s₁₄ gd => ?_)
  · have e0 : ∀ x : BitVec 32, x - (0 : BitVec 32) = x := fun x => by bv_omega
    refine WP.ite (s₀.gpr .r3 == 0) (by simp only [Arm.eval, z₁₃, n₁₂, e0]) (fun h0 => ?_)
      (fun h0 => ?_)
    · have hn0 : n = 0 := by
        simp only [beq_iff_eq] at h0; show (s₀.gpr .r3).toNat = 0; rw [h0]; rfl
      exact WP.block_nil ⟨b₁₃, rfl, rfl, rfl, Frame.refl _ _, fun i hi => by omega⟩
    · have hn0 : n ≠ 0 := by
        simp only [beq_eq_false_iff_ne, ne_eq] at h0
        intro h; apply h0; exact BitVec.eq_of_toNat_eq (by simpa [n] using h)
      exact VG.Proof.Aes.Arm.Ecb.groups_ok hcr hs ⟨by omega, d₁₃, n₁₃, k₁₃, b₁₃, rfl, rfl, rfl, Frame.refl _ _, data₁₃⟩
  -- The epilogue.
  have sv : VG.Proof.Aes.Arm.Saved s₀ B s₁₄.mem := by
    intro i hi
    have c : ∀ {m m' : Mem} {rs : List Region}, Frame rs m m' →
        (∀ r ∈ rs, Region.Disjoint ⟨slotA B (32 + i), 32 / 8⟩ r) →
        m'.readW (slotA B (32 + i)) 32 = m.readW (slotA B (32 + i)) 32 :=
      fun hf hd => hf.readW (Region.contains_self _ _) hd (by decide)
    rw [c gd.frame (slot_disj_regions hp.dDS (by omega) (by omega) (by omega)), m₁₃,
      c d₈.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact off_disjoint _ (by omega) (by omega) (by omega)), m₇, sv₂' i hi]
  have f₀₁₄ : Frame [⟨B, 2048⟩, ⟨D, 16 * n⟩] s₀.mem s₁₄.mem := by
    refine (f₀₈.mono fun r hr => List.mem_cons.mpr (.inl (List.mem_singleton.mp hr))).trans ?_
    rw [← m₁₃]
    refine gd.frame.sub fun r hr => ?_
    simp only [gRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨B, 2048⟩, by simp, Region.sub_prefix (by omega)⟩
    · exact ⟨⟨B, 2048⟩, by simp, sub_scr _ (by omega)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩
  refine wp_ldrSp (by omega) (a := stackArgAddr s₀ 0) (by simp [stackArgAddr, gd.sp, sp₁₃])
    (by rw [gd.rd, gd.wr, rd₁₃, wr₁₃]; exact VG.Proof.Aes.Arm.Ecb.arg_in hrA) fun s₁₅ u₁₅ => ?_
  have b₁₅ : s₁₅.gpr .r12 = b := by
    rw [u₁₅.gpr]
    have := VG.Proof.Aes.Arm.Ecb.stackArg_frame f₀₁₄ (by rw [gd.sp, sp₁₃]) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact argB (by omega)
      · exact hp.dDA.symm)
    simp only [stackArg, stackArgAddr, gd.sp, sp₁₃] at this
    exact this
  obtain ⟨s₁₆, h₁₆, rg₁₆, fR⟩ := restore_ok (s₀ := s₀) (by decide)
    (by rw [u₁₅.wr, gd.wr, wr₁₃]; exact hwS) hfit b₁₅ (by rw [u₁₅.mem]; exact sv)
  refine WP.of_runBlock ⟨s₁₆, h₁₆, rg₁₆, ?_⟩
  rw [u₁₅.mem] at fR
  show Spec.Aes.statesAt s₁₆.mem D n = _
  rw [VG.Proof.Aes.Arm.Ecb.statesAt_of_ecbInv (VG.Proof.Aes.Arm.Ecb.ecbInv_frame fR (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.dDS.sub_right (Region.sub_prefix (by omega))) n16 gd.data)]
  simp only [Spec.Aes.statesAt, List.map_map]
  rfl

theorem blocks_correct {crypt2 : Prog isa} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    (hcr : VG.Proof.Aes.Arm.Ecb.CryptOk crypt2 f) (s : State) (hs : (Proof.Aes.blocksArm f).pre s) :
    ∃ t s', Exec isa (blocks crypt2) s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksArm f).post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := VG.Proof.Aes.Arm.Ecb.correct hcr (VG.Proof.Aes.Arm.Ecb.pre_of hs)
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he⟩, h₂⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h₁ 0 (by omega)
  · exact h₁ 1 (by omega)
  · exact h₁ 2 (by omega)
  · exact h₁ 3 (by omega)
  · exact h₁ 4 (by omega)
  · exact h₁ 5 (by omega)
  · exact h₁ 6 (by omega)
  · exact h₁ 7 (by omega)
  · exact h₁ 8 (by omega)

/-! ## Constant time -/

/-- The initial taint: the pointers, `rounds`, `n` and the stack argument are
public; `r2` points at the data, and the stack argument at the scratch
buffer. -/
def τ₀ : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [0, 2048],
    bases := [(.r2, 0)], argLen := 4, argBases := [(0, 1)] }

theorem wf₀ {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s : State}
    (h : (Proof.Aes.blocksArm f).pre s) : VG.Arm.Taint.Wf VG.Proof.Aes.Arm.Ecb.τ₀ s := by
  have hp := VG.Proof.Aes.Arm.Ecb.pre_of h
  have e : (⟨State.addr s.sp, 4⟩ : Region) = VG.Proof.Aes.Arm.Ecb.argR s := by simp [VG.Proof.Aes.Arm.Ecb.argR, stackArgAddr]
  refine ⟨fun _ => ⟨by simp [hp.wr, VG.Proof.Aes.Arm.Ecb.τ₀], ?_, ?_⟩, ?_, fun _ => ⟨hp.fitSp, ?_⟩, ?_⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil]
    exact ⟨hp.dDS, fun _ h => h.elim, trivial⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    have := hp.fitD; have := hp.fitB
    rintro r (rfl | rfl) <;> simp only [VG.Proof.MdStream.Arm.addr_toNat] <;> omega
  · intro p hp'
    simp only [VG.Proof.Aes.Arm.Ecb.τ₀, List.mem_singleton] at hp'; subst hp'
    simp [VG.Arm.Taint.region, hp.wr]
  · simp only [VG.Proof.Aes.Arm.Ecb.τ₀, e, hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.dDA.symm
    · exact hp.dSA.symm
  · intro p hp'
    simp only [VG.Proof.Aes.Arm.Ecb.τ₀, List.mem_singleton] at hp'; subst hp'
    refine ⟨by decide, ?_⟩
    simp only [VG.Arm.Taint.region, hp.wr]
    rfl

theorem agree₀ {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s₁ s₂ : State}
    (h₁ : (Proof.Aes.blocksArm f).pre s₁) (h₂ : (Proof.Aes.blocksArm f).pre s₂)
    (hpub : (Proof.Aes.blocksArm f).pub s₁ s₂) : VG.Arm.Taint.Agree VG.Proof.Aes.Arm.Ecb.τ₀ s₁ s₂ := by
  obtain ⟨psp, p0, p1, p2, p3, a0⟩ := hpub
  have hp₁ := VG.Proof.Aes.Arm.Ecb.pre_of h₁; have hp₂ := VG.Proof.Aes.Arm.Ecb.pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, VG.Proof.Aes.Arm.Ecb.wf₀ h₁, VG.Proof.Aes.Arm.Ecb.wf₀ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => psp,
    fun k hk => ?_⟩
  · simp only [VG.Proof.Aes.Arm.Ecb.τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  · rw [hp₁.wr, hp₂.wr]; simp only [VG.Proof.Aes.Arm.Ecb.dP, VG.Proof.Aes.Arm.Ecb.nB, VG.Proof.Aes.Arm.Ecb.bP, p2, p3, a0]
  · simp only [VG.Proof.Aes.Arm.Ecb.τ₀] at hk
    rw [VG.Proof.MdStream.Arm.argByte_eq hp₁.fitSp hk, VG.Proof.MdStream.Arm.argByte_eq hp₂.fitSp hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    rw [show k / 4 = 0 by omega]
    exact congrArg _ a0

theorem encryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksArm Spec.Aes.cipher).pre
    (Proof.Aes.blocksArm Spec.Aes.cipher).pub encryptBlocks :=
  VG.Taint.constantTime (A := VG.Arm.taint) VG.Proof.Aes.Arm.Ecb.τ₀ (fun _ _ h₁ h₂ hp => VG.Proof.Aes.Arm.Ecb.agree₀ h₁ h₂ hp) (by taint_decide)

theorem decryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksArm Spec.Aes.invCipher).pre
    (Proof.Aes.blocksArm Spec.Aes.invCipher).pub decryptBlocks :=
  VG.Taint.constantTime (A := VG.Arm.taint) VG.Proof.Aes.Arm.Ecb.τ₀ (fun _ _ h₁ h₂ hp => VG.Proof.Aes.Arm.Ecb.agree₀ h₁ h₂ hp) (by taint_decide)

/-- A state satisfying the precondition (with no data, and the scratch buffer at 0). -/
def sat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 240⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x3000, 0⟩, ⟨0, 2048⟩]

theorem encryptBlocks_verified :
    Verified Arm.target encryptBlocks (Spec.Aes.encryptBlocksContract Arm.abi) :=
  Verified.of_correct (VG.Proof.Aes.Arm.Ecb.blocks_correct VG.Proof.Aes.Arm.Ecb.encrypt2_cryptOk) VG.Proof.Aes.Arm.Ecb.encryptBlocks_ct (by
    sig_implies [Spec.Aes.encryptBlocksContract, Spec.Aes.blocksSig, Proof.Aes.blocksArm, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Aes.Arm.Ecb.sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
      using Proof.Aes.Arm.Ecb.sat)

theorem decryptBlocks_verified :
    Verified Arm.target decryptBlocks (Spec.Aes.decryptBlocksContract Arm.abi) :=
  Verified.of_correct (VG.Proof.Aes.Arm.Ecb.blocks_correct VG.Proof.Aes.Arm.Ecb.decrypt2_cryptOk) VG.Proof.Aes.Arm.Ecb.decryptBlocks_ct (by
    sig_implies [Spec.Aes.decryptBlocksContract, Spec.Aes.blocksSig, Proof.Aes.blocksArm, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Aes.Arm.Ecb.sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
      using Proof.Aes.Arm.Ecb.sat)

end VG.Proof.Aes.Arm.Ecb

end
