module

public import VerifiedGarbage.Impl.Aes.Arm.Blocks
public import VerifiedGarbage.Proof.Aes.Arm.Group
public import VerifiedGarbage.Proof.Aes.InvSboxSpec
public import VerifiedGarbage.Proof.Aes.Ct32.InvBitsliced
public import VerifiedGarbage.Spec.Aes.Contract
import VerifiedGarbage.Proof.Framework.Arm.Bytes
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `Aes.Arm.Decrypt`, which only this module used -/

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

@[expose] public section

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
        (fun r => (invSboxCode.all fun i => !clobbers i r) = false) := by
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
  obtain ⟨s', hs', p₀⟩ := key 0 (by omega_arith)
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
    Straight.bitOf_word _ _ _ (by simp only [Ct32.invSrSrc]; omega_arith)]

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
  rw [show 32 * m = 32 * (m - 1) + 32 by omega_arith, BitVec.ofNat_add, ← BitVec.add_assoc,
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
  have hR : R ≤ 14 := by rcases hp.rounds with h | h | h <;> omega_arith
  simp only [invRoundBody]
  repeat rw [WP.block_append_iff (M := isa)]
  refine subKp_wp hc fun s₁ hc₁ hk₁ hq₁ => ?_
  rw [hk, kp_back _ (by omega_arith), show R - m - 1 = R - (m + 1) by omega_arith] at hk₁
  have hbs₁ : BsRel (Q s₁) T := by
    have : Q s₁ = Q s := funext hq₁
    rw [this]; exact hbs
  refine layer_wp (invShiftRows_ok (hc₁.linOk hp)) hc₁ fun s₂ hc₂ h₂ hk₂ => ?_
  have hbs₂ := bs_invShiftRows h₂ hbs₁
  refine layer_wp (invSbox_ok (hc₂.linOk hp)) hc₂ fun s₃ hc₃ h₃ hk₃ => ?_
  have hbs₃ := bs_invSubBytes h₃ hbs₂
  refine ark_step hp hc₃ (j := R - (m + 1)) (by rw [hk₃, hk₂, hk₁]) (by omega_arith) hbs₃
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
    simp only [irnd, show R - 1 - m = R - (m + 1) by omega_arith]
  · simp only [Arm.eval, hz₆, hk₅', z_first _ (show R - (m + 1) < 15 by omega_arith)]
    congr 2
    exact decide_eq_decide.mpr (by omega_arith)

/-- Two blocks, from `InRel` to `InRel` of their decryptions. -/
theorem decrypt2_ok {s₀ : State} {R : Nat} {w : List Byte} {S : Nat → Spec.Aes.State}
    (hp : EncPre s₀ R w) (hfk : FirstKey s₀ s₀.mem) (hin : InRel (Q s₀) S) :
    WP isa decrypt2 s₀ fun s => Ctx s₀ s ∧ InRel (Q s) (fun b => invCipher R w (S b)) := by
  have hR : R ≤ 14 := by rcases hp.rounds with h | h | h <;> omega_arith
  have hR1 : 2 ≤ R := by rcases hp.rounds with h | h | h <;> omega_arith
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
      congr 2; simp only [lastKey]; omega_arith
    exact ark_step hp hc₂ hk₂' (Nat.le_refl R) hbs₂ fun s₃ hc₃ hk₃ hbs₃ =>
      ⟨0, by omega_arith, by omega_arith, hc₃, by rw [hk₃, hk₂'], hbs₃⟩
  · -- The middle rounds.
    refine WP.loop (M := isa) Inv (fun n s hs => ?_) (R - 1) s h
    obtain ⟨m, rfl, hm, hc, hk, hbs⟩ := hs
    refine WP.mono (invRound_ok hp hfk hc hk hm hbs) fun s' ⟨hc', hk', hbs', hz⟩ => ?_
    by_cases hlast : m + 2 = R
    · refine .inl ⟨hz.trans (by simp [hlast]), hc', ?_, ?_⟩
      · rw [hk']; congr 3; omega_arith
      · rw [show R - 1 = m + 1 by omega_arith]
        intro b hb i hi
        rw [hbs' b hb i hi]; simp only [invMid_succ]
    · refine .inr ⟨hz.trans (by simp [hlast]), R - 1 - (m + 1), by omega_arith, m + 1, rfl, by omega_arith,
        hc', hk', fun b hb i hi => by rw [hbs' b hb i hi]; simp only [invMid_succ]⟩
  · -- The last round, and back to blocks.
    obtain ⟨hc, hk, hbs⟩ := h
    rw [WP.block_append_iff (M := isa)]
    simp only [invLastRound]
    repeat rw [WP.block_append_iff (M := isa)]
    refine subKp_wp hc fun s₁ hc₁ hk₁ hq₁ => ?_
    rw [hk, kp_back _ (by omega_arith)] at hk₁
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
open VG.Proof.Aes (getD_eq byte_ext)

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
  have ha : ∀ (s' : State), s'.gpr .r10 = s.gpr .r10 → s'.wr = s.wr → ∀ k < 4,
      State.addr (s'.gpr .r10 + BitVec.ofNat 32 (16 * c + 4 * k)) =
        State.addr Dp + BitVec.ofNat 64 (16 * (2 * g + c)) + BitVec.ofNat 64 (4 * k) ∧
      InRegions (s'.rd ++ s'.wr)
        (State.addr Dp + BitVec.ofNat 64 (16 * (2 * g + c)) + BitVec.ofNat 64 (4 * k)) 4 := by
    intro s' h1 h2 k hk
    have e : State.addr (s'.gpr .r10 + BitVec.ofNat 32 (16 * c + 4 * k)) =
        State.addr Dp + BitVec.ofNat 64 (16 * (2 * g + c)) + BitVec.ofNat 64 (4 * k) := by
      rw [h1, h10, add_ofNat_ofNat, addr_add (by omega_arith), Offset.add_add]
      congr 2; omega_arith
    refine ⟨e, ?_⟩
    have := in_off (List.mem_append_right s'.rd (h2 ▸ hdat)) hfit
      (off := 16 * (2 * g + c) + 4 * k) (n := 4) (by omega_arith) (by omega_arith)
    rwa [addr_add (by omega_arith), ← Offset.add_add] at this
  have qb := q_blk c hc
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
    have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
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
  have ha : State.addr (s.gpr .r10 + BitVec.ofNat 32 (4 * k)) =
      State.addr Dp + BitVec.ofNat 64 (4 * (8 * g + k)) := by
    rw [hs.gpr, hp.r10, add_ofNat_ofNat, addr_add (by omega_arith)]
    congr 2; omega_arith
  have hin : InRegions s.wr (State.addr Dp + BitVec.ofNat 64 (4 * (8 * g + k))) 4 := by
    have := in_off (hs.wr ▸ hp.dat) hp.fit (off := 4 * (8 * g + k)) (n := 4) (by omega_arith) (by omega_arith)
    rwa [addr_add (by omega_arith)] at this
  simp only [stw, List.cons_append, List.nil_append]
  refine wp_str (by omega_arith) ha hin fun s' u => ?_
  have hst := ecbInv_step (v := s.gpr (q (2 * (k % 4) + k / 4))) (by omega_arith) hkn hs.data
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
  have ev₅ : Arm.eval .ne s₅ = some (decide (2 ≤ n - 2 * g)) := by
    rw [Arm.eval, z₅, u₄.gpr, hp.r11, shr1_eq _ (by omega_arith)]
  -- The stores start from `s₅`, which differs from `s₃` only in `kp` and the flags.
  let s₃' := s₅
  have x₀ : SS m₀ (State.addr Dp) n g F s₃' 0 s₅ :=
    ⟨by rw [f₅.mem, u₄.mem]; exact hp.data, Frame.refl _ _, rfl, rfl, rfl, rfl⟩
  have g₅ : ∀ r, r ≠ kp → s₅.gpr r = s₃.gpr r := fun r hr => by rw [f₅.gpr, u₄.other r hr]
  have hp' : SPre m₀ Dp n g F s₃' :=
    { hg := hg, fit := hn, dat := by rw [f₅.wr, u₄.wr]; exact hp.dat
      r10 := by rw [g₅ _ (by decide)]; exact hp.r10
      r11 := by rw [g₅ _ (by decide)]; exact hp.r11
      data := x₀.data
      vals := fun k hk hkn t ht => by
        rw [g₅ _ (q_ctr (k / 4) (by omega_arith) (k % 4) (by omega_arith)).2.2]; exact hp.vals k hk hkn t ht }
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
    have e₁₀ : s₁₅.gpr .r10 = Dp + BitVec.ofNat 32 (32 * (g + 1)) := by
      rw [u₁₅.other _ (by decide), u₁₄.gpr, x₁₃.gpr, hp'.r10]
      rw [BitVec.add_assoc, show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl, ← BitVec.ofNat_add]
      congr 2
    have e₁₁ : s₁₅.gpr .r11 = BitVec.ofNat 32 (n - 2 * (g + 1)) := by
      rw [u₁₅.gpr, u₁₄.other _ (by decide), x₁₃.gpr, hp'.r11]
      bv_omega
    have d : EcbInv m₀ s₁₅.mem (State.addr Dp) n (8 * (g + 1)) F := by
      rw [u₁₅.mem, u₁₄.mem]; exact x₁₃.data
    by_cases hl : n - 2 * g = 2
    · exact .inl ⟨by rw [e₁₁, show n - 2 * (g + 1) = 0 by omega_arith]; rfl,
        ecbInv_mono d (by omega_arith) (by omega_arith)⟩
    · exact .inr ⟨by omega_arith, d, e₁₀, e₁₁⟩
  · -- The last block.
    have h1 : n - 2 * g = 1 := by simp at hb; omega_arith
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
  have c : ∀ k, 44 ≤ k → k < 48 →
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
  have hR : R ≤ 14 := by rcases hs.rounds with h | h | h <;> omega_arith
  have hfit := hs.fit
  have hfitD := hs.fitD
  have hg := hi.hg
  have hscr : (⟨State.addr b, 2048⟩ : Region) ∈ s.wr := hi.wr ▸ hs.scr
  have hdat : (⟨State.addr Dp, 16 * n⟩ : Region) ∈ s.wr := hi.wr ▸ hs.dat
  let F := ecbOut f m₀ (State.addr Dp) R w
  unfold blockGroup
  refine WP.seq (front_wp hi.base hscr hfit fun s₁ hkp₁ o₁ m₁ rd₁ wr₁ sp₁ z₁ => ?_)
  have hb₁ : s₁.gpr sb = b := (o₁ sb (by decide) (by decide)).trans hi.base
  have f₁ : Frame [⟨State.addr b + BitVec.ofNat 64 176, 16⟩] s.mem s₁.mem := by
    rw [m₁]; exact save_frame _ _ _ _ _
  have hf₁ : Frame (gRegions (State.addr b) (State.addr Dp) n) s₂.mem s₁.mem :=
    hi.frame.trans (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨State.addr b + BitVec.ofNat 64 176, 20⟩, by simp, front_sub _⟩)
  have z₁' : Arm.eval .ne s₁ = some (decide (2 ≤ n - 2 * g)) := by
    rw [z₁, hi.r11, shr1_eq _ (by omega_arith)]
  have d₁ : EcbInv m₀ s₁.mem (State.addr Dp) n (8 * g) F :=
    ecbInv_frame f₁ (by simpa using hs.sep.sub_right (scr_sub _ (by omega_arith))) (by omega_arith) hi.data
  refine WP.seq (load_wp hg hfitD (wr₁ ▸ hdat) (by rw [o₁ _ (by decide) (by decide)]; exact hi.r10) z₁'
    fun s₂' v₂ o₂ m₂ rd₂ wr₂ sp₂ => ?_)
  have hkp₂ : s₂'.gpr kp = s.gpr .r12 := by
    rw [o₂ _ fun c hc k hk => (q_blk c hc k hk).2.2.2.2.1.symm, hkp₁]
  have hb₂ : s₂'.gpr sb = b := by
    rw [o₂ _ fun c hc k hk => (q_blk c hc k hk).2.2.2.1.symm, hb₁]
  have hp : EncPre s₂' R w :=
    ⟨by rw [hb₂, wr₂, wr₁, hi.wr]; exact hs.scr, by rw [hb₂]; exact hfit, hs.rounds,
      by rw [hkp₂, hi.r12, hb₂],
      by rw [hkp₂, hi.r12, m₂]; exact keysAt_frame hfit hR hf₁ (keys_disj_regions hs.sep) hs.keys⟩
  have hfk : FirstKey s₂' s₂'.mem := by
    rw [FirstKey, hb₂, hkp₂, m₂, m₁]; exact (save_read _ _ _ _ _).2.2
  -- The loaded blocks.
  have hld : ∀ c < 2, 2 * g + c < n → regBlock (Q s₂') c = Spec.Aes.stateAt m₀
      (State.addr Dp + BitVec.ofNat 64 (16 * (2 * g + c))) := fun c hc hcn => by
    rw [regBlock_load (m := s₁.mem) fun k hk => v₂ c hc hcn k hk]
    exact stateAt_ecbInv d₁ hcn (by omega_arith)
  refine WP.seq (WP.mono (hcr hp hfk (inRel_regBlock (Q s₂'))) fun s₃ ⟨hc₃, hin₃⟩ => ?_)
  have fr₃ := hc₃.frame
  rw [hb₂] at fr₃
  have hb₃ : s₃.gpr sb = b := hc₃.base.trans hb₂
  have hscr₃ : (⟨State.addr b, 2048⟩ : Region) ∈ s₃.wr := by rw [hc₃.wr, wr₂, wr₁]; exact hscr
  have mslot : ∀ k, 45 ≤ k → k < 48 → s₃.mem.readW (slotA (State.addr b) k) 32 =
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
  have e10 : s₆.gpr .r10 = Dp + BitVec.ofNat 32 (32 * g) := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, mslot dSlot (by decide) (by decide), m₁,
      rd10, hi.r10]
  have e11 : s₆.gpr .r11 = BitVec.ofNat 32 (n - 2 * g) := by
    rw [u₆.other _ (by decide), u₅.gpr, u₄.mem, mslot lSlot (by decide) (by decide), m₁, rd11, hi.r11]
  have e12 : s₆.gpr .r12 = b + BitVec.ofNat 32 (lastKey - 32 * R) := by
    rw [u₆.gpr, u₅.mem, u₄.mem, mslot fkSlot (by decide) (by decide), m₁, rd12, hi.r12]
  have mm₆ : s₆.mem = s₃.mem := by rw [u₆.mem, u₅.mem, u₄.mem]
  have gq₆ : ∀ i < 8, s₆.gpr (q i) = s₃.gpr (q i) := fun i hi' => by
    have : q i ≠ .r10 ∧ q i ≠ .r11 ∧ q i ≠ .r12 := by revert hi'; revert i; decide
    rw [u₆.other _ this.2.2, u₅.other _ this.2.1, u₄.other _ this.1]
  have d128 : Region.Disjoint ⟨State.addr Dp, 16 * n⟩ ⟨State.addr b, 128⟩ :=
    hs.sep.sub_right (Region.sub_prefix (by omega_arith))
  have hx : SPre m₀ Dp n g F s₆ :=
    { hg := hg, fit := hfitD, dat := by rw [u₆.wr, u₅.wr, u₄.wr, hc₃.wr, wr₂, wr₁]; exact hdat
      r10 := e10, r11 := e11
      data := by
        rw [mm₆]
        exact ecbInv_frame fr₃ (by simpa using d128) (by omega_arith) (by rw [m₂]; exact d₁)
      vals := fun k hk hkn t ht => by
        rw [gq₆ _ (by omega_arith)]
        have hcn : 2 * g + k / 4 < n := by omega_arith
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
  have keep : ∀ r, r ∉ layerWrites → r ≠ kp → s₉.gpr r = s.gpr r := by
    intro r h1 h2
    have : r ≠ .lr ∧ r ≠ .r10 ∧ r ≠ .r11 ∧ r ≠ .r12 := by revert h1 h2; cases r <;> decide
    have qw : ∀ c < 2, ∀ k < 4, q (2 * k + c) ∈ layerWrites := by decide
    have hq : ∀ c < 2, ∀ k < 4, r ≠ q (2 * k + c) := fun c hc k hk h => h1 (h ▸ qw c hc k hk)
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
  · refine .inr ⟨?_, ⟨by omega_arith, by rw [f₉.gpr]; exact x10, by rw [f₉.gpr]; exact x11,
      by rw [f₉.gpr, o₈ _ (by decide) (by decide) (by decide), e12], base', rd', wr', sp',
      frame', by rw [f₉.mem]; exact d⟩⟩
    have hne : BitVec.ofNat 32 (n - 2 * (g + 1)) ≠ 0 := by
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
