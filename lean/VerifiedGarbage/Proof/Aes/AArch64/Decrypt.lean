import VerifiedGarbage.Impl.Aes.AArch64.Blocks
import VerifiedGarbage.Proof.Aes.AArch64.Encrypt
import VerifiedGarbage.Proof.Aes.InvSboxSpec
import VerifiedGarbage.Proof.Aes.InvBitsliced

/-!
# Decrypting four blocks, bitsliced, on AArch64

The inverse layers (`Impl/Aes/AArch64/Inv.lean`) are checked by evaluation
as the cipher's are (`Encrypt.lean`): the inverse S-box on the truth
tables of the 256 inputs against the specification's (`invSboxT`), the
linear layers over the lane domain. `decrypt4_ok` composes them: from
four blocks in the registers (`InRel`), with the bitsliced round keys in
the scratch buffer (`EncPre`), `decrypt4` leaves the four plaintexts,
having written only the first 384 bytes of the scratch buffer. The round
loop's invariant is the specification's `foldl` over the rounds done, with
`kp` stepping down from the last round key.
-/

namespace VG.Proof.Aes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Bitslice VG.Impl.Aes.AArch64 VG.Proof.Aes
open VG.Spec.Aes (invSbox roundKey invSubBytes invShiftRows invMixColumns addRoundKey invCipher)

/-! ## The inverse S-box -/

def invSboxPost (e : Env Nat) : Bool :=
  (List.range 8).all fun j => e.reg (q j) == some ((invSboxT inTs).getD j 0)

theorem invSbox_check :
    check (table 64 256) sboxCfg (fun _ => none) invSboxCode sboxEnv invSboxPost = true := by
  decide +kernel

/-- The inverse S-box, at every bit position of the words in `q 0 … q 7`. -/
theorem invSbox_ok {s : State} (hok : Ok sboxCfg s) :
    ∃ s', runBlock isa invSboxCode s = some s' ∧
      (∀ j < 8, ∀ p < 64,
        (s'.gpr (q j)).getLsbD p = (invSbox (bsByte (fun k => s.gpr (q k)) p)).getLsbD j) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion sboxCfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ invSbox_check
  have hout : ∀ j < 8, e'.reg (q j) = some ((invSboxT inTs).getD j 0) := by
    intro j hj
    have := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
    simpa using this
  have key : ∀ p < 64, ∃ s', runBlock isa invSboxCode s = some s' ∧
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
    check (lanes 64 9) linCfg (linExt 0) Impl.Aes.AArch64.invShiftRows (linEnv qIns)
      (linPost 9 (qOuts invSrG)) = true := by
  decide +kernel

theorem invMixColumns_check :
    check (lanes 64 9) linCfg (linExt 0) Impl.Aes.AArch64.invMixColumns (linEnv qIns)
      (linPost 9 (qOuts invMcG)) = true := by
  decide +kernel

theorem invShiftRows_ok {s : State} (hok : Ok linCfg s) :
    ∃ s', runBlock isa Impl.Aes.AArch64.invShiftRows s = some s' ∧
      (∀ j < 8, ∀ p < 64, (Q s' j).getLsbD p = (Q s j).getLsbD (invSrSrc p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion linCfg s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, rest⟩ := q_linear invShiftRows_check (by decide) (by decide +kernel) hok
    (Q s) (fun _ _ => rfl) (fun j hj => by simp [linCfg] at hj)
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, invSrG, xorBits_cons, xorBits_nil, Bool.xor_false,
    bitOf_word _ _ _ (by simp only [invSrSrc]; omega)]

theorem invMixColumns_ok {s : State} (hok : Ok linCfg s) :
    ∃ s', runBlock isa Impl.Aes.AArch64.invMixColumns s = some s' ∧
      (∀ j < 8, ∀ p < 64, (Q s' j).getLsbD p = termsXor (Q s) (invMcTerms j p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion linCfg s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, rest⟩ := q_linear invMixColumns_check (by decide) (by decide +kernel) hok
    (Q s) (fun _ _ => rfl) (fun j hj => by simp [linCfg] at hj)
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, invMcG, xorBits_map]
  intro wt hwt
  obtain ⟨wk, -, rfl⟩ := List.mem_map.mp hwt
  exact Nat.mod_lt _ (by decide)

/-! ## The rounds -/

theorem kp_back (K : Addr) {m : Nat} (hm : 0 < m) :
    K + BitVec.ofNat 64 (64 * m) - BitVec.ofNat 64 64 = K + BitVec.ofNat 64 (64 * (m - 1)) := by
  rw [Offset.add_ofNat_sub K (by omega), show 64 * m - 64 = 64 * (m - 1) by omega]

/-- `sub kp, kp, #64`. -/
theorem subKp_wp {s₀ s : State} {P : State → Prop} (hc : Ctx s₀ s)
    (h : ∀ s', Ctx s₀ s' → s'.gpr kp = s.gpr kp - BitVec.ofNat 64 64 →
      (∀ i, Q s' i = Q s i) → P s') :
    WP isa (.block [.subImm .x kp kp 64]) s P := by
  refine WP.of_runBlock ⟨_, by rw [runBlock_cons, exec_subImm_x (by decide), runStep_some,
    runBlock_nil], h _ ?_ ?_ ?_⟩
  · exact hc.step rfl rfl rfl (fun r _ hr => by simp [State.write, hr]) (Frame.refl _ _)
  · simp [State.write, State.read]
  · intro i; simp [Q, State.write, q_ne_kp i]

/-- `sub t0, kp, x0; sub t0, t0, #64`. -/
theorem cmpFirst_wp {s₀ s : State} {P : State → Prop} (hc : Ctx s₀ s)
    (h : ∀ s', Ctx s₀ s' → s'.gpr kp = s.gpr kp → (∀ i, Q s' i = Q s i) →
      s'.gpr t0 = s.gpr kp - s.gpr .x0 - BitVec.ofNat 64 64 → P s') :
    WP isa (.block [.sub .x t0 kp .x0, .subImm .x t0 t0 64]) s P := by
  refine WP.of_runBlock ⟨_, by rw [runBlock_cons, show exec (.sub .x t0 kp .x0) s =
    some (s.write .x t0 (s.read .x kp - s.read .x .x0)) from rfl, runStep_some, runBlock_cons,
    exec_subImm_x (by decide), runStep_some, runBlock_nil], h _ ?_ ?_ ?_ ?_⟩
  · exact hc.step rfl rfl rfl (fun r hr _ => by
      have : r ≠ t0 := fun h => hr (h ▸ by decide)
      simp [State.write, this]) (Frame.refl _ _)
  · simp [State.write, t0, kp]
  · intro i; simp [Q, State.write, q_ne_t0 i]
  · simp [State.write, State.read]

/-- `add kp, x5, #lastKey`. -/
theorem kpLast_wp {s₀ s : State} {P : State → Prop} (hc : Ctx s₀ s)
    (h : ∀ s', Ctx s₀ s' → s'.gpr kp = s.gpr sb + BitVec.ofNat 64 lastKey →
      (∀ i, Q s' i = Q s i) → P s') :
    WP isa (.block [.addImm .x kp sb lastKey]) s P := by
  refine WP.of_runBlock ⟨_, by rw [runBlock_cons, exec_addImm_x (by decide), runStep_some,
    runBlock_nil], h _ ?_ ?_ ?_⟩
  · exact hc.step rfl rfl rfl (fun r _ hr => by simp [State.write, hr]) (Frame.refl _ _)
  · simp [State.write, State.read]
  · intro i; simp [Q, State.write, q_ne_kp i]

theorem t0_first (K : Addr) {m : Nat} (hm : m < 15) :
    (K + BitVec.ofNat 64 (64 * m) - K - BitVec.ofNat 64 64 != 0) = !decide (m = 1) := by
  rw [Offset.add_sub_cancel_left, bne, Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
  congr 1
  exact decide_eq_decide.mpr (by omega)

/-- A middle round of the inverse cipher. -/
theorem invRound_ok {s₀ s : State} {R m : Nat} {w : List Byte} {T : Nat → Spec.Aes.State}
    (hp : EncPre s₀ R w) (hc : Ctx s₀ s) (hk : s.gpr kp = s₀.gpr .x0 + BitVec.ofNat 64 (64 * (R - m)))
    (hm : m + 1 < R) (hbs : BsRel (Q s) T) :
    WP isa (.block invRoundBody) s fun s' => Ctx s₀ s' ∧
      s'.gpr kp = s₀.gpr .x0 + BitVec.ofNat 64 (64 * (R - (m + 1))) ∧
      BsRel (Q s') (fun b => irnd R w m (T b)) ∧
      AArch64.eval (.nonzero .x t0) s' = some (!decide (m + 2 = R)) := by
  have hR : R ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  simp only [invRoundBody]
  repeat rw [WP.block_append_iff (M := isa)]
  refine subKp_wp hc fun s₁ hc₁ hk₁ hq₁ => ?_
  rw [hk, kp_back _ (by omega), show R - m - 1 = R - (m + 1) by omega] at hk₁
  have hbs₁ : BsRel (Q s₁) T := by
    have : Q s₁ = Q s := funext hq₁
    rw [this]; exact hbs
  refine layer_wp (invShiftRows_ok (hc₁.linOk hp.scr)) hc₁ fun s₂ hc₂ h₂ hk₂ => ?_
  have hbs₂ := bs_invShiftRows h₂ hbs₁
  refine layer_wp (invSbox_ok (hc₂.linOk hp.scr)) hc₂ fun s₃ hc₃ h₃ hk₃ => ?_
  have hbs₃ := bs_invSubBytes h₃ hbs₂
  refine ark_step hp hc₃ (j := R - (m + 1)) (by rw [hk₃, hk₂, hk₁]) (by omega) hbs₃
    fun s₄ hc₄ hk₄ hbs₄ => ?_
  refine layer_wp (invMixColumns_ok (hc₄.linOk hp.scr)) hc₄ fun s₅ hc₅ h₅ hk₅ => ?_
  have hbs₅ := bs_invMixColumns h₅ hbs₄
  have hk₅' : s₅.gpr kp = s₀.gpr .x0 + BitVec.ofNat 64 (64 * (R - (m + 1))) := by
    rw [hk₅, hk₄, hk₃, hk₂, hk₁]
  refine cmpFirst_wp hc₅ fun s₆ hc₆ hk₆ hq₆ ht₆ => ⟨hc₆, ?_, ?_, ?_⟩
  · rw [hk₆, hk₅']
  · have : Q s₆ = Q s₅ := funext hq₆
    rw [this]
    intro b hb i hi
    rw [hbs₅ b hb i hi]
    simp only [irnd, show R - 1 - m = R - (m + 1) by omega]
  · simp only [AArch64.eval, State.read, Size.bits, BitVec.setWidth_eq, ht₆]
    rw [hk₅', hc₅.keep _ x0_not.1 x0_not.2, t0_first _ (by omega)]
    exact congrArg (some ∘ not) (decide_eq_decide.mpr (by omega))

/-- Four blocks, from `InRel` to `InRel` of their decryptions. -/
theorem decrypt4_ok {s₀ : State} {R : Nat} {w : List Byte} {S : Nat → Spec.Aes.State}
    (hp : EncPre s₀ R w) (hin : InRel (Q s₀) S) :
    WP isa decrypt4 s₀ fun s => Ctx s₀ s ∧ InRel (Q s) (fun b => invCipher R w (S b)) := by
  have hR : R ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  have hR1 : 2 ≤ R := by rcases hp.rounds with h | h | h <;> omega
  let A : Nat → Spec.Aes.State := fun b => addRoundKey (S b) (roundKey w R)
  let Inv : Nat → State → Prop := fun n s => ∃ m, n = R - 1 - m ∧ m + 1 < R ∧ Ctx s₀ s ∧
    s.gpr kp = s₀.gpr .x0 + BitVec.ofNat 64 (64 * (R - m)) ∧
    BsRel (Q s) (fun b => invMid R w m (A b))
  let Mid : State → Prop := fun s => Ctx s₀ s ∧
    s.gpr kp = s₀.gpr .x0 + BitVec.ofNat 64 (64 * 1) ∧
    BsRel (Q s) (fun b => invMid R w (R - 1) (A b))
  refine WP.seq (WP.mono (Q := Inv (R - 1)) ?_ fun s h => WP.seq (WP.mono (Q := Mid) ?_ fun s h => ?_))
  · -- toBs, the last round key.
    repeat rw [WP.block_append_iff (M := isa)]
    refine layer_wp (toBs_ok ((Ctx.refl s₀).linOk hp.scr)) (Ctx.refl s₀) fun s₁ hc₁ h₁ _ => ?_
    have hbs₁ := bs_of_in h₁ hin
    refine kpLast_wp hc₁ fun s₂ hc₂ hk₂ hq₂ => ?_
    have hbs₂ : BsRel (Q s₂) S := by
      have : Q s₂ = Q s₁ := funext hq₂
      rw [this]; exact hbs₁
    have hk₂' : s₂.gpr kp = s₀.gpr .x0 + BitVec.ofNat 64 (64 * R) := by
      rw [hk₂, hc₁.base, hp.k0, BitVec.add_assoc, ← BitVec.ofNat_add, lastKey]
      congr 2; omega
    exact ark_step hp hc₂ hk₂' (Nat.le_refl R) hbs₂ fun s₃ hc₃ hk₃ hbs₃ =>
      ⟨0, by omega, by omega, hc₃, by rw [hk₃, hk₂']; simp, hbs₃⟩
  · -- The middle rounds.
    refine WP.loop (M := isa) Inv (fun n s hs => ?_) (R - 1) s h
    obtain ⟨m, rfl, hm, hc, hk, hbs⟩ := hs
    refine WP.mono (invRound_ok hp hc hk hm hbs) fun s' ⟨hc', hk', hbs', hz⟩ => ?_
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
    refine layer_wp (invShiftRows_ok (hc₁.linOk hp.scr)) hc₁ fun s₂ hc₂ h₂ hk₂ => ?_
    have hbs₂ := bs_invShiftRows h₂ hbs₁
    refine layer_wp (invSbox_ok (hc₂.linOk hp.scr)) hc₂ fun s₃ hc₃ h₃ hk₃ => ?_
    have hbs₃ := bs_invSubBytes h₃ hbs₂
    refine ark_step hp hc₃ (j := 0) (by rw [hk₃, hk₂, hk₁]) (Nat.zero_le R) hbs₃ fun s₄ hc₄ _ hbs₄ => ?_
    refine layer_wp (fromBs_ok (hc₄.linOk hp.scr)) hc₄ fun s₅ hc₅ h₅ _ => ⟨hc₅, ?_⟩
    have := in_of_bs h₅ hbs₄
    intro b hb i hi j hj
    rw [this b hb i hi j hj]; simp only [invCipher_eq]; rfl

end VG.Proof.Aes.AArch64
