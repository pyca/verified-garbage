import VerifiedGarbage.Impl.Aes.X86.Blocks
import VerifiedGarbage.Proof.Aes.X86.Encrypt
import VerifiedGarbage.Proof.Aes.InvSboxSpec
import VerifiedGarbage.Proof.Aes.Ct32.InvBitsliced

/-!
# Decrypting two blocks, bitsliced, on x86 (32-bit)

The inverse layers (`Impl/Aes/X86/Inv.lean`) are checked by evaluation as
the cipher's are (`Sbox.lean`, `Linear.lean`): the inverse S-box on the
truth tables of the 256 inputs against the specification's (`invSboxT`),
the linear layers over the lane domain. `decrypt2_ok` composes them: from
two blocks in slots `0 … 7` (`InRel`), with the bitsliced round keys in the
scratch buffer (`EncPre`), `decrypt2` leaves the two plaintexts, having
written only the first 256 bytes of the scratch buffer. The round loop's
invariant is the specification's `foldl` over the rounds done, with `kp`
stepping down from the last round key.
-/

namespace VG.Proof.Aes.X86

open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.Aes.X86 VG.Proof.Aes VG.Proof.Aes.Ct32
open VG.Spec.Aes (invSbox roundKey invSubBytes invShiftRows invMixColumns addRoundKey invCipher)
open VG.X86.Wp (Upd wp_mov wp_ldm wp_addi wp_add wp_sub wp_subi wp_cmp sub_beq)

/-! ## The inverse S-box -/

def invSboxPost (e : Env Nat) : Bool :=
  (List.range 8).all fun j => e.slot j == some ((invSboxT inTs).getD j 0)

theorem invSbox_check :
    check (table 32 256) linCfg (fun _ => none) invSboxCode sboxEnv invSboxPost = true := by
  decide +kernel

/-- The inverse S-box, at every bit position of the words in slots `0 … 7`. -/
theorem invSbox_ok {s : State} (hok : Ok linCfg s) :
    ∃ s', runBlock isa invSboxCode s = some s' ∧
      (∀ j < 8, ∀ p < 32, (Q s' j).getLsbD p = (invSbox (bsByte (Q s) p)).getLsbD j) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ tmpRegs → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion linCfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ invSbox_check
  have hout : ∀ j < 8, e'.slot j = some ((invSboxT inTs).getD j 0) := by
    intro j hj
    have := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
    simpa using this
  have key : ∀ p < 32, ∃ s', runBlock isa invSboxCode s = some s' ∧
      Post (TableRel p (bsByte (Q s) p).toNat) linCfg (fun _ => none) e' s s'
        (fun r => (invSboxCode.all fun i => i.dst != some r) = false) := by
    intro p hp
    have hc := (bsByte (Q s) p).isLt
    refine run (table_sound hp hc) hok ⟨(fun r a h => by cases h), fun k a _ h => ?_,
      (fun _ _ _ h => by cases h)⟩ he
    simp only [sboxEnv] at h
    split at h
    · rename_i hk8
      cases h
      simp only [TableRel, inT, testBit_tableOf, hc, decide_true, Bool.true_and,
        BitVec.testBit_toNat, getLsbD_bsByte _ _ hk8, Q, linCfg]
    · cases h
  obtain ⟨s', hs', p₀⟩ := key 0 (by omega)
  refine ⟨s', hs', fun j hj p hp => ?_, p₀.rd, p₀.wr, fun r hr => p₀.other r ?_, p₀.frame⟩
  · obtain ⟨s'', hs'', p₁⟩ := key p hp
    obtain rfl := run_unique hs'' hs'
    have hc := (bsByte (Q s) p).isLt
    have := p₁.rel.slot j _ (by simp [linCfg]; omega) (hout j hj)
    have hb : s''.gpr sb = s.gpr sb := p₁.base
    simp only [TableRel, linCfg, hb] at this
    rw [Q, hb, ← this, ← getLsbD_row _ _ hj, row_invSboxT _ hc, row_inTs hc]
    simp
  · have : (invSboxCode.all fun i => i.dst != some r) = true :=
      keeps_rest (by decide +kernel) r hr
    simp [this]

/-! ## The linear layers -/

theorem invShiftRows_check :
    check (lanes 32 8) linCfg (linExt 0) Impl.Aes.X86.invShiftRows (linEnv qIns)
      (linPost 64 8 (qOuts invSrG)) = true := by
  decide +kernel

theorem invMixColumns_check :
    check (lanes 32 8) linCfg (linExt 0) Impl.Aes.X86.invMixColumns (linEnv qIns)
      (linPost 64 8 (qOuts invMcG)) = true := by
  decide +kernel

theorem invShiftRows_ok {s : State} (hok : Ok linCfg s) :
    ∃ s', runBlock isa Impl.Aes.X86.invShiftRows s = some s' ∧
      (∀ j < 8, ∀ p < 32, (Q s' j).getLsbD p = (Q s j).getLsbD (invSrSrc p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ tmpRegs → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion linCfg s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, rest⟩ := q_linear invShiftRows_check (by decide) rfl
    (by decide +kernel) hok (Q s) (fun _ _ => rfl) (fun j hj => by simp [linCfg] at hj)
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, invSrG, xorBits_cons, xorBits_nil, Bool.xor_false,
    bitOf_word _ _ _ (by simp only [invSrSrc]; omega)]

theorem invMixColumns_ok {s : State} (hok : Ok linCfg s) :
    ∃ s', runBlock isa Impl.Aes.X86.invMixColumns s = some s' ∧
      (∀ j < 8, ∀ p < 32, (Q s' j).getLsbD p = termsXor (Q s) (invMcTerms j p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ tmpRegs → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion linCfg s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, rest⟩ := q_linear invMixColumns_check (by decide) rfl
    (by decide +kernel) hok (Q s) (fun _ _ => rfl) (fun j hj => by simp [linCfg] at hj)
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, invMcG, xorBits_map]
  intro wt hwt
  obtain ⟨wk, -, rfl⟩ := List.mem_map.mp hwt
  exact Nat.mod_lt _ (by decide)

/-! ## The rounds -/

theorem keyOff_pred {R m : Nat} (h : 1 ≤ m) (hm : m ≤ R) (hR : R ≤ 14) (B : BitVec 32) :
    B + BitVec.ofNat 32 (keyOff R m) - 32 = B + BitVec.ofNat 32 (keyOff R (m - 1)) := by
  have := keyOff_succ (R := R) (m := m - 1) (by omega) hR B
  rw [Nat.sub_add_cancel h] at this
  rw [← this, BitVec.add_sub_cancel]

/-- `sub kp, 32`. -/
theorem subKp_wp {s₀ s : State} {Q : State → Prop} (hc : Ctx s₀ s)
    (h : ∀ s', Ctx s₀ s' → s'.gpr kp = s.gpr kp - 32 → Proof.Aes.X86.Q s' = Proof.Aes.X86.Q s → Q s') :
    WP isa (.block [subI kp 32]) s Q :=
  wp_subi fun s' u _ _ => WP.block_nil (h s' (hc.upd u (.inr rfl)) u.gpr
    (Q_congr (u.other _ (by decide)) u.mem))

/-- `kp :=` the last round key. -/
theorem kpLast_wp {s₀ s : State} {R : Nat} {Q : State → Prop} (hc : Ctx s₀ s)
    (h : ∀ s', Ctx s₀ s' → s'.gpr kp = s₀.gpr sb + BitVec.ofNat 32 (keyOff R R) →
      Proof.Aes.X86.Q s' = Proof.Aes.X86.Q s → Q s') :
    WP isa (.block kpLast) s Q := by
  refine wp_mov fun s₁ u₁ => wp_addi fun s₂ u₂ => WP.block_nil ?_
  have c₂ := (hc.upd u₁ (.inr rfl)).upd u₂ (.inr rfl)
  refine h s₂ c₂ ?_ (Q_congr (c₂.base.trans hc.base.symm) (by rw [u₂.mem, u₁.mem]))
  rw [u₂.gpr, u₁.gpr, show s.gpr .edi = s₀.gpr sb from hc.base]
  simp [keyOff]

/-- `cmpFirst`: ZF is set when `kp` is at round key 1. -/
theorem cmpFirst_wp {s₀ s : State} {R m : Nat} {w : List Byte} {Q : State → Prop}
    (hp : EncPre s₀ R w) (hc : Ctx s₀ s) (hm : m ≤ R)
    (hk : s.gpr kp = s₀.gpr sb + BitVec.ofNat 32 (keyOff R m))
    (h : ∀ s', Ctx s₀ s' → s'.gpr kp = s.gpr kp → Proof.Aes.X86.Q s' = Proof.Aes.X86.Q s →
      s'.zf = some (decide (m = 1)) → Q s') :
    WP isa (.block cmpFirst) s Q := by
  have hR : R ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  have hR1 : 1 ≤ R := by rcases hp.rounds with h | h | h <;> omega
  have hin : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 8) 4 := by
    rw [hc.rd, hc.wr, hc.esp]; exact hp.argIn
  refine wp_ldm (B := s.gpr .esp) rfl hin fun s₁ u₁ => ?_
  refine wp_add fun s₂ u₂ _ => wp_add fun s₃ u₃ _ => wp_add fun s₄ u₄ _ => wp_add fun s₅ u₅ _ =>
    wp_add fun s₆ u₆ _ => wp_mov fun s₇ u₇ => wp_addi fun s₈ u₈ => wp_sub fun s₉ u₉ _ =>
    wp_cmp fun s₁₀ u₁₀ _ hz => WP.block_nil ?_
  have c₉ : Ctx s₀ s₉ := ((((((((hc.upd u₁ (.inl (by decide))).upd u₂ (.inl (by decide))).upd u₃
    (.inl (by decide))).upd u₄ (.inl (by decide))).upd u₅ (.inl (by decide))).upd u₆
    (.inl (by decide))).upd u₇ (.inl (by decide))).upd u₈ (.inl (by decide))).upd u₉ (.inl (by decide))
  have hk₉ : s₉.gpr kp = s.gpr kp := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide)]
  have c₁₀ : Ctx s₀ s₁₀ := c₉.step u₁₀.rd u₁₀.wr (fun r _ _ => by rw [u₁₀.gpr])
    (by rw [u₁₀.mem]; exact Frame.refl _ _)
  refine h s₁₀ c₁₀ (by rw [u₁₀.gpr, hk₉]) (Q_congr (c₁₀.base.trans hc.base.symm)
    (by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem])) ?_
  have e6 : s₆.gpr .ebx = BitVec.ofNat 32 (32 * R) := by
    rw [u₆.gpr, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, hp.arg hc]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have e7 : s₇.gpr .eax = s₀.gpr sb := by
    rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), ← hc.base]; rfl
  have e9 : s₉.gpr .eax = s₀.gpr sb + BitVec.ofNat 32 (keyOff R 1) := by
    rw [u₉.gpr, u₈.gpr, u₈.other .ebx (by decide), u₇.other .ebx (by decide), e6, e7]
    simp only [keyOff, lastKey]
    bv_omega
  rw [hz, hk₉, hk, e9, sub_self_add, sub_beq (by simp only [keyOff, lastKey]; omega)
    (by simp only [keyOff, lastKey]; omega)]
  simp only [keyOff, lastKey]
  exact congrArg some (decide_eq_decide.mpr ⟨fun _ => by omega, fun _ => by omega⟩)

/-- A middle round of the inverse cipher. -/
theorem invRound_ok {s₀ s : State} {R m : Nat} {w : List Byte} {T : Nat → Spec.Aes.State}
    (hp : EncPre s₀ R w) (hc : Ctx s₀ s) (hk : s.gpr kp = s₀.gpr sb + BitVec.ofNat 32 (keyOff R (R - m)))
    (hm : m + 1 < R) (hbs : BsRel (Q s) T) :
    WP isa (.block invRoundBody) s fun s' => Ctx s₀ s' ∧
      s'.gpr kp = s₀.gpr sb + BitVec.ofNat 32 (keyOff R (R - (m + 1))) ∧
      BsRel (Q s') (fun b => irnd R w m (T b)) ∧ s'.zf = some (decide (m + 2 = R)) := by
  have hR : R ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  simp only [invRoundBody]
  repeat rw [WP.block_append_iff (M := isa)]
  refine subKp_wp hc fun s₁ hc₁ hk₁ hq₁ => ?_
  rw [hk, keyOff_pred (by omega) (by omega) hR, show R - m - 1 = R - (m + 1) by omega] at hk₁
  have hbs₁ : BsRel (Q s₁) T := by rw [hq₁]; exact hbs
  refine layer_wp (invShiftRows_ok (hc₁.linOk hp)) hc₁ fun s₂ hc₂ h₂ hk₂ => ?_
  have hbs₂ := bs_invShiftRows h₂ hbs₁
  refine layer_wp (invSbox_ok (hc₂.linOk hp)) hc₂ fun s₃ hc₃ h₃ hk₃ => ?_
  have hbs₃ := bs_invSubBytes h₃ hbs₂
  refine ark_step hp hc₃ (j := R - (m + 1)) (by rw [hk₃, hk₂, hk₁]) (by omega) hbs₃
    fun s₄ hc₄ hk₄ hbs₄ => ?_
  refine layer_wp (invMixColumns_ok (hc₄.linOk hp)) hc₄ fun s₅ hc₅ h₅ hk₅ => ?_
  have hbs₅ := bs_invMixColumns h₅ hbs₄
  have hk₅' : s₅.gpr kp = s₀.gpr sb + BitVec.ofNat 32 (keyOff R (R - (m + 1))) := by
    rw [hk₅, hk₄, hk₃, hk₂, hk₁]
  refine cmpFirst_wp hp hc₅ (by omega) hk₅' fun s₆ hc₆ hk₆ hq₆ hz₆ => ⟨hc₆, ?_, ?_, ?_⟩
  · rw [hk₆, hk₅']
  · rw [hq₆]
    intro b hb i hi
    rw [hbs₅ b hb i hi]
    simp only [irnd, show R - 1 - m = R - (m + 1) by omega]
  · rw [hz₆]
    exact congrArg some (decide_eq_decide.mpr (by omega))

/-- Two blocks, from `InRel` to `InRel` of their decryptions. -/
theorem decrypt2_ok {s₀ : State} {R : Nat} {w : List Byte} {S : Nat → Spec.Aes.State}
    (hp : EncPre s₀ R w) (hin : InRel (Q s₀) S) :
    WP isa decrypt2 s₀ fun s => Ctx s₀ s ∧ InRel (Q s) (fun b => invCipher R w (S b)) := by
  have hR : R ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  have hR1 : 2 ≤ R := by rcases hp.rounds with h | h | h <;> omega
  let A : Nat → Spec.Aes.State := fun b => addRoundKey (S b) (roundKey w R)
  let Inv : Nat → State → Prop := fun n s => ∃ m, n = R - 1 - m ∧ m + 1 < R ∧ Ctx s₀ s ∧
    s.gpr kp = s₀.gpr sb + BitVec.ofNat 32 (keyOff R (R - m)) ∧
    BsRel (Q s) (fun b => invMid R w m (A b))
  let Mid : State → Prop := fun s => Ctx s₀ s ∧
    s.gpr kp = s₀.gpr sb + BitVec.ofNat 32 (keyOff R 1) ∧
    BsRel (Q s) (fun b => invMid R w (R - 1) (A b))
  refine WP.seq (WP.mono (Q := Inv (R - 1)) ?_ fun s h => WP.seq (WP.mono (Q := Mid) ?_ fun s h => ?_))
  · -- ortho, the last round key.
    repeat rw [WP.block_append_iff (M := isa)]
    refine layer_wp (toBs_ok ((Ctx.refl s₀).linOk hp)) (Ctx.refl s₀) fun s₁ hc₁ h₁ _ => ?_
    have hbs₁ := bs_of_in h₁ hin
    refine kpLast_wp (R := R) hc₁ fun s₂ hc₂ hk₂ hq₂ => ?_
    have hbs₂ : BsRel (Q s₂) S := by rw [hq₂]; exact hbs₁
    exact ark_step hp hc₂ hk₂ (Nat.le_refl R) hbs₂ fun s₃ hc₃ hk₃ hbs₃ =>
      ⟨0, by omega, by omega, hc₃, by rw [hk₃, hk₂, Nat.sub_zero], hbs₃⟩
  · -- The middle rounds.
    refine WP.loop (M := isa) Inv (fun n s hs => ?_) (R - 1) s h
    obtain ⟨m, rfl, hm, hc, hk, hbs⟩ := hs
    refine WP.mono (invRound_ok hp hc hk hm hbs) fun s' ⟨hc', hk', hbs', hz⟩ => ?_
    by_cases hlast : m + 2 = R
    · refine .inl ⟨by simp [X86.eval, hz, hlast], hc', ?_, ?_⟩
      · rw [hk']; congr 3; omega
      · rw [show R - 1 = m + 1 by omega]
        intro b hb i hi
        rw [hbs' b hb i hi]; simp only [invMid_succ]
    · refine .inr ⟨by simp [X86.eval, hz, hlast], R - 1 - (m + 1), by omega, m + 1, rfl, by omega,
        hc', hk', fun b hb i hi => by rw [hbs' b hb i hi]; simp only [invMid_succ]⟩
  · -- The last round, and back to blocks.
    obtain ⟨hc, hk, hbs⟩ := h
    rw [WP.block_append_iff (M := isa)]
    simp only [invLastRound]
    repeat rw [WP.block_append_iff (M := isa)]
    refine subKp_wp hc fun s₁ hc₁ hk₁ hq₁ => ?_
    rw [hk, keyOff_pred (by omega) (by omega) hR] at hk₁
    have hbs₁ : BsRel (Q s₁) (fun b => invMid R w (R - 1) (A b)) := by rw [hq₁]; exact hbs
    refine layer_wp (invShiftRows_ok (hc₁.linOk hp)) hc₁ fun s₂ hc₂ h₂ hk₂ => ?_
    have hbs₂ := bs_invShiftRows h₂ hbs₁
    refine layer_wp (invSbox_ok (hc₂.linOk hp)) hc₂ fun s₃ hc₃ h₃ hk₃ => ?_
    have hbs₃ := bs_invSubBytes h₃ hbs₂
    refine ark_step hp hc₃ (j := 0) (by rw [hk₃, hk₂, hk₁]) (Nat.zero_le R) hbs₃ fun s₄ hc₄ _ hbs₄ => ?_
    refine layer_wp (fromBs_ok (hc₄.linOk hp)) hc₄ fun s₅ hc₅ h₅ _ => ⟨hc₅, ?_⟩
    have := in_of_bs h₅ hbs₄
    intro b hb i hi j hj
    rw [this b hb i hi j hj]; simp only [invCipher_eq]; rfl

end VG.Proof.Aes.X86
