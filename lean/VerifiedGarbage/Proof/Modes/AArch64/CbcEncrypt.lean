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

theorem cbcEncrypt_wp (cs : BlockSpec c) {r : CtrRegs} (hr : RegsOk r) (hdn : c.dataReg ≠ r.n) {s₀ : State}
    {B P D : Addr} {n : Nat} {k : cs.Key} (hB : s₀.gpr r.scr = B) (hP : s₀.gpr r.ctr = P) (hD : s₀.gpr r.data = D)
    (hn : (s₀.gpr r.n).toNat = n) (hs : ScrIn s₀ B c.total) (hrP : (⟨P, 8 * c.bw⟩ : Region) ∈ s₀.rd)
    (hwD : (⟨D, 8 * c.bw * n⟩ : Region) ∈ s₀.wr) (sPS : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨B, 8 * c.total⟩)
    (sDS : Region.Disjoint ⟨D, 8 * c.bw * n⟩ ⟨B, 8 * c.total⟩) (sPD : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨D, 8 * c.bw * n⟩)
    (fitD : D.toNat + 8 * c.bw * n ≤ 2 ^ 64) (hk : cs.KeyArgs s₀ [⟨B, 8 * c.total⟩, ⟨D, 8 * c.bw * n⟩] k) :
    WP isa (c.cbcEncrypt r) s₀ fun s' =>
      (∀ i < 10, s'.gpr (Core.savedRegs.getD i .x19) = s₀.gpr (Core.savedRegs.getD i .x19)) ∧
      blocksOf (8 * c.bw) s'.mem D n =
        Spec.Cbc.encrypt (cs.cipher k) (bytesAt s₀.mem P (8 * c.bw)) (blocksOf (8 * c.bw) s₀.mem D n) ∧
      Frame [⟨B, 8 * c.total⟩, ⟨D, 8 * c.bw * n⟩] s₀.mem s'.mem ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr := by
  have hL := cs.layout
  have hsm := hL.small
  have hroom := hL.room
  have hbw0 := hL.bw_pos
  have hbw2 := hL.bw_le
  have hL0 : 0 < 8 * c.bw := by omega
  have h8n : 8 * n ≤ 8 * c.bw * n := Nat.mul_le_mul_right n (by omega)
  have hn64 : 8 * c.bw * n ≤ 2 ^ 64 := by omega
  have hqr : ∀ {q r}, q < n → r < 8 * c.bw → 8 * c.bw * q + r < 8 * c.bw * n := fun hq hr => by
    have := idx_lt (L := 8 * c.bw) hq; omega
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
  obtain ⟨s₁, e₁, b₁, sv₁, f₁, g₁, rd₁, wr₁⟩ := entry_ok hsm hroom s₀ hB hs
  unfold Core.cbcEncrypt
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  have mP : ∀ u < 8 * c.bw, s₁.mem (P + BitVec.ofNat 64 u) = s₀.mem (P + BitVec.ofNat 64 u) := fun u hu =>
    f₁.bytes (R := ⟨P, 8 * c.bw⟩) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact sPS.sub_right subMode)
      (show 8 * c.bw ≤ 2 ^ 64 by omega) hu
  have mD : ∀ i < 8 * c.bw * n, s₁.mem (D + BitVec.ofNat 64 i) = s₀.mem (D + BitVec.ofNat 64 i) := fun i hi =>
    f₁.bytes (R := ⟨D, 8 * c.bw * n⟩) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact sDS.sub_right subMode) hn64 hi
  -- The IV into the first block.
  have hz₁ : isa.eval (.zero .x r.n) s₁ = some (decide (n = 0)) := by
    rw [eval_zero, g₁ _ ns']
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by rw [← hn, h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [hn, h]; rfl)⟩
  let Qw : State → Prop := fun s₂ => s₂.gpr sb = B ∧ (∀ x, x ≠ .x6 → x ≠ .x7 → s₂.gpr x = s₁.gpr x) ∧
    s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr ∧ Frame [⟨D, 8 * c.bw * n⟩] s₁.mem s₂.mem ∧
    ∀ q < n, ∀ r < 8 * c.bw, s₂.mem (D + BitVec.ofNat 64 (8 * c.bw * q + r)) =
      if q = 0 then s₀.mem (D + BitVec.ofNat 64 (8 * c.bw * q + r)) ^^^ s₀.mem (P + BitVec.ofNat 64 r)
      else s₀.mem (D + BitVec.ofNat 64 (8 * c.bw * q + r))
  have hw : WP isa (c.cbcWhiten r) s₁ Qw := by
    unfold Core.cbcWhiten
    refine WP.ite (decide (n = 0)) hz₁ (fun h0 => ?_) (fun h0 => ?_)
    · have hn0 : n = 0 := by simpa using h0
      exact WP.block_nil ⟨b₁, fun x _ _ => rfl, rfl, rfl, Frame.refl _ _, fun q hq => by omega⟩
    · have hn0 : 0 < n := by simp at h0; omega
      have sub0 : Region.Sub ⟨D + BitVec.ofNat 64 (8 * c.bw * 0), 8 * c.bw⟩ ⟨D, 8 * c.bw * n⟩ :=
        VG.Offset.sub_base D (idx_lt hn0)
      refine WP.mono (xorN_wp (k := c.bw) (P := D + BitVec.ofNat 64 (8 * c.bw * 0)) (Q := P) (t := .x6) (u := .x7)
        ⟨by rw [g₁ _ ds', hD]; simp, by rw [g₁ _ cs', hP]; simp, Ne.symm dd6, Ne.symm c6, Ne.symm dd7, Ne.symm c7,
          by decide, by decide, by omega, by omega, fun w hw' => ⟨_, by rw [wr₁]; exact hwD, by
            rw [addr_add]
            exact VG.Offset.contains_base D (by
              have := idx_lt (L := c.bw) hn0; rw [Nat.mul_zero] at this ⊢; have := Nat.mul_assoc 8 c.bw n; omega)
              (by rw [Nat.mul_zero]; omega)⟩,
          fun w hw' => by
            rw [rd₁, wr₁]
            exact ⟨_, List.mem_append_left _ hrP, VG.Offset.contains_base P (by omega) (by omega)⟩,
          sPD.symm.sub_left sub0, by omega⟩ (by decide)) fun s₂ h₂ => ?_
      refine ⟨by rw [h₂.regs _ (by decide) (by decide), b₁], fun x h1 h2 => h₂.regs x h1 h2, h₂.rd, h₂.wr, ?_,
        fun q hq r hr => ?_⟩
      · rw [h₂.mem]
        exact (over_frame _ _ _ _).sub fun x hx => by
          simp only [List.mem_singleton] at hx; subst hx; exact ⟨_, List.mem_singleton_self _, sub0⟩
      rw [h₂.mem, over_blk _ _ _ hn0 hq hr hn64]
      split
      · rename_i h; subst h; rw [addr_add, mD _ (hqr hq hr), mP r hr]
      · exact mD _ (hqr hq hr)
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
  have f₃ : Frame [⟨B, 8 * c.total⟩, ⟨D, 8 * c.bw * n⟩] s₀.mem s₃.mem := by
    rw [m₃]
    exact (f₁.sub fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact ⟨_, List.mem_cons_self, subMode⟩).trans
      (f₂.sub fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx
        exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩)
  have kr := keyRegs_ne cs.keyRegs_ok
  have hk₃ : cs.KeyArgs s₃ [⟨B, 8 * c.total⟩, ⟨D, 8 * c.bw * n⟩] k :=
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
  let iv := bytesAt s₀.mem P (8 * c.bw)
  have hiv : iv.length = 8 * c.bw := by simp [iv, bytesAt]
  have hp : GPre c s₄ B D n (8 * c.bw) := ⟨⟨by rw [wr₄']; exact hs.wr, hs.fit⟩, by rw [wr₄']; exact hwD, sDS, fitD⟩
  have dCore : ∀ x ∈ [coreRegion c B], Region.Disjoint ⟨D, 8 * c.bw * n⟩ x := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; exact sDS.sub_right (Region.sub_prefix (by omega))
  -- The blocks.
  refine WP.seq (WP.mono (M := isa) (Q := EDone cs s₄ s₀.mem B D n k iv)
    (WP.ite (decide (n = 0)) hz₄ (fun h0 => ?_) (fun h0 => ?_)) fun s₆ d₆ => ?_)
  · have hn0 : n = 0 := by simpa using h0
    exact WP.block_nil ⟨b₄, fun _ _ => rfl, fun i hi' => by rw [hn0, Nat.mul_zero] at hi'; omega,
      Frame.refl _ _, rfl, rfl⟩
  · have hn0 : n ≠ 0 := by simpa using h0
    refine cbcEncLoop_wp cs hiv hp ⟨b₄, ready₄, fun _ _ => rfl, ?_, ?_, by omega, fun q hq r hr => ?_,
      Frame.refl _ _, rfl, rfl⟩
    · rw [dr₄, dr₃, g₂ _ dd6 dd7, g₁ _ ds', hD]; simp
    · rw [left₄, Nat.sub_zero, ← hn]; simp
    · rw [f₄.bytes (R := ⟨D, 8 * c.bw * n⟩) dCore hn64 (hqr hq hr), m₃, d₂ q hq r hr, encByte,
        ite_eq_right (Nat.not_lt_zero _)]
      split
      · rw [cbcEncPrev, ite_eq_left rfl, bytesAt_getD _ _ hr]
      · rfl
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
  · rw [m₇]; exact cbcEnc_of_dinv (cs.cipher_len k) d₆.data
  · rw [m₇]
    exact (f₃.trans (f₄.sub fun x hx => ⟨⟨B, 8 * c.total⟩, List.mem_cons_self, by
        simp only [List.mem_singleton] at hx; subst hx; exact Region.sub_prefix (by omega)⟩)).trans d₆.frame

end VG.Proof.Modes.AArch64
