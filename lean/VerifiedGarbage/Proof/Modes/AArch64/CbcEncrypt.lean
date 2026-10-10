import VerifiedGarbage.Proof.Modes.AArch64.CbcEncLoop
import VerifiedGarbage.Proof.Modes.AArch64.Ctr

/-!
# CBC encryption on AArch64, for any core: the whole function

`cbcEncrypt_wp`: `c.cbcEncrypt r`, for a core `c` with `CoreSpec c` whose
cipher is the forward cipher `CIPH_K`, and its arguments in the registers
`r`, replaces the `n` blocks at `D` with their CBC encryption under the key
`k` that its key arguments give, from the IV at `P` (only read); it keeps
the callee-saved registers `x19`–`x28`, and writes nothing but the scratch
buffer and the data.
-/

namespace VG.Proof.Modes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Modes.AArch64
open VG.Impl.Aes.AArch64 (sb movR ldS stS eorR)
open VG.Spec.Aes (bytesAt)

variable {c : Core}

/-- The entry: the scratch buffer to `sb`, the callee-saved registers to the
mode's slots. -/
theorem entry_ok (hL : Layout c) {r : CtrRegs} (s : State) {B : Addr} (hB : s.gpr r.scr = B)
    (hs : ScrIn s B c.total) :
    ∃ s', runBlock isa (c.ctrEntry r) s = some s' ∧ s'.gpr sb = B ∧
      (∀ i < 10, s'.mem.readW (wordAddr B (c.slots + i)) 64 = s.gpr (Core.savedRegs.getD i .x19)) ∧
      Frame [modeRegion c B] s.mem s'.mem ∧ (∀ x, x ≠ sb → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hsm := hL.small
  have hroom := hL.room
  have hN : 8 * c.total < 2 ^ 64 := by omega
  obtain ⟨s₁, e₁, b₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s sb r.scr
  have b₁' : s₁.gpr sb = B := by rw [b₁, hB]
  obtain ⟨s₂, e₂, v₂, f₂, g₂, rd₂, wr₂⟩ := stores_ok (B := B) c.slots (fun i => Core.savedRegs.getD i .x19) 10 s₁
    b₁' (fun i hi => by rw [wr₁]; exact slot_wr hs.wr hN (by omega)) (by omega)
  have hsv : ∀ i < 10, Core.savedRegs.getD i .x19 ≠ sb := by decide
  refine ⟨s₂, by rw [ctrEntry_eq, runBlock_app, e₁, Option.bind_some, e₂], by rw [g₂, b₁'],
    fun i hi => by rw [v₂ i hi, o₁ _ (hsv i hi)], ?_, fun x hx => by rw [g₂, o₁ x hx], by rw [rd₂, rd₁],
    by rw [wr₂, wr₁]⟩
  rw [← m₁]
  exact f₂.sub fun x hx => ⟨_, List.mem_singleton_self _, by
    simp only [List.mem_singleton] at hx; subst hx; exact VG.Offset.sub B (by omega) (by omega)⟩

theorem cbcEncrypt_wp (cs : CoreSpec c) {r : CtrRegs} (hr : RegsOk r) (hdn : c.dataReg ≠ r.n) {s₀ : State}
    {B P D : Addr} {n : Nat} {k : cs.Key} (hB : s₀.gpr r.scr = B) (hP : s₀.gpr r.ctr = P) (hD : s₀.gpr r.data = D)
    (hn : (s₀.gpr r.n).toNat = n) (hs : ScrIn s₀ B c.total) (hrP : (⟨P, 16⟩ : Region) ∈ s₀.rd)
    (hwD : (⟨D, 16 * n⟩ : Region) ∈ s₀.wr) (sPS : Region.Disjoint ⟨P, 16⟩ ⟨B, 8 * c.total⟩)
    (sDS : Region.Disjoint ⟨D, 16 * n⟩ ⟨B, 8 * c.total⟩) (sPD : Region.Disjoint ⟨P, 16⟩ ⟨D, 16 * n⟩)
    (fitD : D.toNat + 16 * n ≤ 2 ^ 64) (hk : cs.KeyArgs s₀ [⟨B, 8 * c.total⟩, ⟨D, 16 * n⟩] k) :
    WP isa (c.cbcEncrypt r) s₀ fun s' =>
      (∀ i < 10, s'.gpr (Core.savedRegs.getD i .x19) = s₀.gpr (Core.savedRegs.getD i .x19)) ∧
      Spec.Cbc.blocksAt s'.mem D n =
        Spec.Cbc.encrypt (cs.cipher k) (bytesAt s₀.mem P 16) (Spec.Cbc.blocksAt s₀.mem D n) ∧
      Frame [⟨B, 8 * c.total⟩, ⟨D, 16 * n⟩] s₀.mem s'.mem ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr := by
  have hL := cs.layout
  have hsm := hL.small
  have hroom := hL.room
  have hN : 8 * c.total < 2 ^ 64 := by omega
  obtain ⟨hregs, hdl⟩ := regsOk_ne cs.regs_ok
  obtain ⟨down, dsb, dk⟩ := hregs c.dataReg List.mem_cons_self
  obtain ⟨lown, lsb, lk⟩ := hregs c.leftReg (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨d6, d7, -⟩ := not_own down
  obtain ⟨l6, l7, -⟩ := not_own lown
  obtain ⟨cs', c6, c7, -⟩ := not_setupRegs hr.ctr
  obtain ⟨ds', dd6, dd7, -⟩ := not_setupRegs hr.data
  obtain ⟨ns', n6, n7, -⟩ := not_setupRegs hr.n
  have subMode : Region.Sub (modeRegion c B) ⟨B, 8 * c.total⟩ := VG.Offset.sub_base B (by omega)
  -- The entry.
  obtain ⟨s₁, e₁, b₁, sv₁, f₁, g₁, rd₁, wr₁⟩ := entry_ok hL s₀ hB hs
  unfold Core.cbcEncrypt
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  have mP : ∀ u < 16, s₁.mem (P + BitVec.ofNat 64 u) = s₀.mem (P + BitVec.ofNat 64 u) := fun u hu =>
    f₁.bytes (R := ⟨P, 16⟩) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact sPS.sub_right subMode) (show 16 ≤ 2 ^ 64 by decide) hu
  have mD : ∀ i < 16 * n, s₁.mem (D + BitVec.ofNat 64 i) = s₀.mem (D + BitVec.ofNat 64 i) := fun i hi =>
    f₁.bytes (R := ⟨D, 16 * n⟩) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact sDS.sub_right subMode) (show 16 * n ≤ 2 ^ 64 by omega) hi
  -- The IV into the first block.
  have hz₁ : isa.eval (.zero .x r.n) s₁ = some (decide (n = 0)) := by
    rw [eval_zero, g₁ _ ns']
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by rw [← hn, h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [hn, h]; rfl)⟩
  unfold Core.cbcWhiten
  let Qw : State → Prop := fun s₂ => s₂.gpr sb = B ∧ (∀ x, x ≠ .x6 → x ≠ .x7 → s₂.gpr x = s₁.gpr x) ∧
    s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr ∧ Frame [⟨D, 16 * n⟩] s₁.mem s₂.mem ∧
    ∀ i < 16 * n, s₂.mem (D + BitVec.ofNat 64 i) =
      if i < 16 then s₀.mem (D + BitVec.ofNat 64 i) ^^^ s₀.mem (P + BitVec.ofNat 64 i)
      else s₀.mem (D + BitVec.ofNat 64 i)
  have hw : WP isa (.ite (.zero .x r.n) (.block [])
      (.block [.ldr .x .x6 r.data 0, .ldr .x .x7 r.ctr 0, eorR .x6 .x6 .x7, .str .x .x6 r.data 0,
        .ldr .x .x6 r.data 8, .ldr .x .x7 r.ctr 8, eorR .x6 .x6 .x7, .str .x .x6 r.data 8])) s₁ Qw := by
    refine WP.ite (decide (n = 0)) hz₁ (fun h0 => ?_) (fun h0 => ?_)
    · have hn0 : n = 0 := by simpa using h0
      exact WP.block_nil ⟨b₁, fun x _ _ => rfl, rfl, rfl, Frame.refl _ _, fun i hi => by omega⟩
    · have hn0 : n ≠ 0 := by simpa using h0
      obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂⟩ := whiten_ok r c6 c7 dd6 dd7 s₁ (by rw [g₁ _ cs', hP])
        (by rw [g₁ _ ds', hD])
        (fun o ho => by rw [rd₁, wr₁]; exact ⟨_, List.mem_append_left _ hrP,
          VG.Offset.contains_base P ho (by omega)⟩)
        (fun o ho => by rw [wr₁]; exact ⟨_, hwD, VG.Offset.contains_base D (by omega) (by omega)⟩)
      have dDP : Region.Disjoint ⟨D, 16⟩ ⟨P, 16⟩ := fun y h1 h2 =>
        sPD y h2 (by simp only [Region.Contains] at h1 ⊢; omega)
      refine WP.of_runBlock ⟨s₂, e₂, by rw [g₂ _ (by decide) (by decide), b₁], fun x h1 h2 => g₂ x h1 h2,
        rd₂, wr₂, ?_, fun i hi => ?_⟩
      · rw [m₂]
        exact fun x hx => two_out fun h => hx _ List.mem_cons_self (by simp only [Region.Contains]; omega)
      · rw [m₂]
        by_cases h16 : i < 16
        · rw [ite_eq_left h16, xor16_in _ dDP h16, mD i hi, mP i h16]
        · have hout : ¬ (D + BitVec.ofNat 64 i - D).toNat < 16 := by rw [off_self D (by omega)]; exact h16
          rw [ite_eq_right h16, show xor16 s₁.mem D P (D + BitVec.ofNat 64 i) = s₁.mem (D + BitVec.ofNat 64 i)
            from two_out hout, mD i hi]
  refine WP.seq (WP.mono hw fun s₂ ⟨b₂, g₂, rd₂, wr₂, f₂, d₂⟩ => ?_)
  -- The data's address and `n`.
  obtain ⟨s₃, e₃, dr₃, lr₃, g₃, m₃, rd₃, wr₃⟩ := ctrArgs_ok s₂ r hdn hdl
  refine WP.seq (WP.of_runBlock ⟨s₃, e₃, ?_⟩)
  have g₃' : ∀ x, x ∉ SetupRegs → x ≠ c.dataReg → x ≠ c.leftReg → s₃.gpr x = s₀.gpr x :=
    fun x h1 h3 h4 => by
      obtain ⟨h5, h6, h7, -⟩ := not_setupRegs h1
      rw [g₃ x h3 h4, g₂ x h6 h7, g₁ x h5]
  have b₃ : s₃.gpr sb = B := by rw [g₃ _ (Ne.symm dsb) (Ne.symm lsb), b₂]
  have rd₃' : s₃.rd = s₀.rd := by rw [rd₃, rd₂, rd₁]
  have wr₃' : s₃.wr = s₀.wr := by rw [wr₃, wr₂, wr₁]
  have f₃ : Frame [⟨B, 8 * c.total⟩, ⟨D, 16 * n⟩] s₀.mem s₃.mem := by
    rw [m₃]
    exact (f₁.sub fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact ⟨_, List.mem_cons_self, subMode⟩).trans
      (f₂.sub fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx
        exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩)
  have kr := keyRegs_ne cs.keyRegs_ok
  have hk₃ : cs.KeyArgs s₃ [⟨B, 8 * c.total⟩, ⟨D, 16 * n⟩] k :=
    cs.keyArgs_congr hk (fun x hx => g₃' x (kr x hx) (fun e => dk (e ▸ hx)) (fun e => lk (e ▸ hx))) rd₃' wr₃' f₃
  -- The key.
  refine WP.seq (WP.mono (cs.prepare_wp b₃ ⟨by rw [wr₃']; exact hs.wr, hs.fit⟩ List.mem_cons_self hk₃)
    fun s₄ ⟨ready₄, b₄, dr₄, lr₄, f₄, rd₄, wr₄⟩ => ?_)
  have rd₄' : s₄.rd = s₀.rd := by rw [rd₄, rd₃']
  have wr₄' : s₄.wr = s₀.wr := by rw [wr₄, wr₃']
  have left₄ : s₄.gpr c.leftReg = s₀.gpr r.n := by rw [lr₄, lr₃, g₂ _ n6 n7, g₁ _ ns']
  have hz₄ : isa.eval (.zero .x c.leftReg) s₄ = some (decide (n = 0)) := by
    rw [eval_zero, left₄]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by rw [← hn, h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [hn, h]; rfl)⟩
  let iv := bytesAt s₀.mem P 16
  have hiv : iv.length = 16 := by simp [iv, bytesAt]
  have hp : GPre c s₄ B D n := ⟨⟨by rw [wr₄']; exact hs.wr, hs.fit⟩, by rw [wr₄']; exact hwD, sDS, fitD⟩
  have dCore : ∀ x ∈ [coreRegion c B], Region.Disjoint ⟨D, 16 * n⟩ x := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; exact sDS.sub_right (Region.sub_prefix (by omega))
  -- The blocks.
  refine WP.seq (WP.mono (M := isa) (Q := EDone cs s₄ s₀.mem B D n k iv)
    (WP.ite (decide (n = 0)) hz₄ (fun h0 => ?_) (fun h0 => ?_)) fun s₆ d₆ => ?_)
  · have hn0 : n = 0 := by simpa using h0
    exact WP.block_nil ⟨b₄, fun _ _ => rfl, fun i hi' => by omega, Frame.refl _ _, rfl, rfl⟩
  · have hn0 : n ≠ 0 := by simpa using h0
    refine cbcEncLoop_wp cs hiv hp ⟨b₄, ready₄, fun _ _ => rfl, ?_, ?_, by omega, fun i hi' => ?_,
      Frame.refl _ _, rfl, rfl⟩
    · rw [dr₄, dr₃, g₂ _ dd6 dd7, g₁ _ ds', hD]; simp
    · rw [left₄, Nat.sub_zero, ← hn]; simp
    · rw [f₄.bytes (R := ⟨D, 16 * n⟩) dCore (show 16 * n ≤ 2 ^ 64 by omega) hi', m₃, d₂ i hi']
      by_cases h16 : i < 16
      · rw [ite_eq_left h16]
        simp only [encByte, Nat.mul_zero, Nat.zero_add, Nat.mul_one, Nat.not_lt_zero, ite_false, h16, ite_true,
          Nat.sub_zero, cbcEncPrev]
        rw [bytesAt_getD _ _ h16]
      · rw [ite_eq_right h16]
        simp only [encByte, Nat.mul_zero, Nat.zero_add, Nat.mul_one, Nat.not_lt_zero, ite_false, h16]
  -- The exit.
  have hsv : ∀ i < 10, Core.savedRegs.getD i .x19 ≠ sb := by decide
  have hinj : ∀ i < 10, ∀ j < 10, Core.savedRegs.getD i .x19 = Core.savedRegs.getD j .x19 → i = j := by decide
  obtain ⟨s₇, e₇, v₇, -, m₇, rd₇, wr₇⟩ := loads_ok (B := B) c.slots (fun i => Core.savedRegs.getD i .x19) 10 s₆
    d₆.base hsv hinj (by omega) (fun i hi' => by
      rw [d₆.rd, d₆.wr, rd₄', wr₄']
      exact inRd (slot_wr hs.wr hN (by omega)))
  refine WP.of_runBlock ⟨s₇, e₇, fun i hi' => ?_, ?_, ?_, by rw [rd₇, d₆.rd, rd₄'], by rw [wr₇, d₆.wr, wr₄']⟩
  · rw [v₇ i hi', d₆.saved i hi', ← sv₁ i hi']
    refine (f₄.readW (Region.contains_self _ _) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx
      exact VG.Offset.disjoint_base B (by omega) (by omega)) (by decide)).trans ?_
    rw [m₃]
    exact f₂.readW (Region.contains_self _ _) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx
      exact (sDS.sub_right (VG.Offset.sub_base B (show 8 * (c.slots + i) + 8 ≤ 8 * c.total by
        omega))).symm) (by decide)
  · rw [m₇, ← blocksOf_16]; exact cbcEnc_of_dinv (cs.cipher_len k) d₆.data
  · rw [m₇]
    exact (f₃.trans (f₄.sub fun x hx => ⟨⟨B, 8 * c.total⟩, List.mem_cons_self, by
        simp only [List.mem_singleton] at hx; subst hx; exact Region.sub_prefix (by omega)⟩)).trans d₆.frame

end VG.Proof.Modes.AArch64
