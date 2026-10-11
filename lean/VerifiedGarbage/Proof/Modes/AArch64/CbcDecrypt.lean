import VerifiedGarbage.Proof.Modes.AArch64.CbcGroup
import VerifiedGarbage.Proof.Modes.AArch64.Ctr

/-!
# CBC decryption on AArch64, for any core: the whole function

`cbcDecrypt_wp`: `c.cbcDecrypt r`, for a core `c` with `CoreSpec c` whose
cipher is the inverse cipher `CIPH⁻¹_K`, and its arguments in the registers
`r`, replaces the `n` blocks at `D` with their CBC decryption under the key
`k` that its key arguments give, from the IV at `P` (only read); it keeps
the callee-saved registers `x19`–`x28`, and writes nothing but the scratch
buffer and the data. Each cipher's contract follows from it (with the
constant-time check of its own code).
-/

namespace VG.Proof.Modes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Modes.AArch64
open VG.Impl.Aes.AArch64 (sb movR ldS stS)
open VG.Spec.Aes (bytesAt)

variable {c : Core}

theorem cbcDecrypt_wp (cs : BlockSpec c) {r : CtrRegs} (hr : RegsOk r) (hdn : c.dataReg ≠ r.n) {s₀ : State}
    {B P D : Addr} {n : Nat} {k : cs.Key} (hB : s₀.gpr r.scr = B) (hP : s₀.gpr r.ctr = P) (hD : s₀.gpr r.data = D)
    (hn : (s₀.gpr r.n).toNat = n) (hs : ScrIn s₀ B c.total) (hrP : (⟨P, 8 * c.bw⟩ : Region) ∈ s₀.rd)
    (hwD : (⟨D, 8 * c.bw * n⟩ : Region) ∈ s₀.wr) (sPS : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨B, 8 * c.total⟩)
    (sDS : Region.Disjoint ⟨D, 8 * c.bw * n⟩ ⟨B, 8 * c.total⟩)
    (fitD : D.toNat + 8 * c.bw * n ≤ 2 ^ 64) (hk : cs.KeyArgs s₀ [⟨B, 8 * c.total⟩] k) :
    WP isa (c.cbcDecrypt r) s₀ fun s' =>
      (∀ i < 10, s'.gpr (Core.savedRegs.getD i .x19) = s₀.gpr (Core.savedRegs.getD i .x19)) ∧
      blocksOf (8 * c.bw) s'.mem D n =
        Spec.Cbc.decrypt (cs.cipher k) (bytesAt s₀.mem P (8 * c.bw)) (blocksOf (8 * c.bw) s₀.mem D n) ∧
      Frame [⟨B, 8 * c.total⟩, ⟨D, 8 * c.bw * n⟩] s₀.mem s'.mem ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr := by
  have hL := cs.layout
  have hsm := hL.small
  have hroom := hL.room
  have hbw0 := hL.bw_pos
  have hbw2 := hL.bw_le
  have hN : 8 * c.total < 2 ^ 64 := by omega
  obtain ⟨hregs, hdl⟩ := regsOk_ne cs.regs_ok
  obtain ⟨-, dsb, dk⟩ := hregs c.dataReg List.mem_cons_self
  obtain ⟨-, lsb, lk⟩ := hregs c.leftReg (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨cs', c6, -, -⟩ := not_setupRegs hr.ctr
  let H := chainAddr c B
  have subMode : Region.Sub (modeRegion c B) ⟨B, 8 * c.total⟩ := VG.Offset.sub_base B (by omega)
  have subH : Region.Sub ⟨H, 8 * c.bw⟩ (modeRegion c B) := VG.Offset.sub B (by simp only [Core.hiSlot]; omega)
    (by simp only [Core.hiSlot]; omega)
  have dPm : Region.Disjoint ⟨P, 8 * c.bw⟩ (modeRegion c B) := sPS.sub_right subMode
  -- The entry, and the IV to the chaining value.
  obtain ⟨sE, eE, bE, svE, fE, gE, rdE, wrE⟩ := entry_ok hsm hroom s₀ hB hs
  unfold Core.cbcDecrypt
  refine WP.seq (WP.block_append (WP.block_append (WP.of_runBlock ⟨sE, eE, WP.mono (copyN_wp (k := c.bw) (P := H)
    (Q := P) (u := .x6) ⟨by rw [bE], by rw [gE _ cs', hP]; simp, by decide, Ne.symm c6, by decide, Ne.symm c6,
      by omega, by decide, by simp only [Core.hiSlot]; omega, by omega,
      fun w hw => ⟨_, by rw [wrE]; exact hs.wr, by
        rw [addr_add]
        exact VG.Offset.contains_base B (by simp only [Core.hiSlot]; omega) (by simp only [Core.hiSlot]; omega)⟩,
      fun w hw => ⟨_, List.mem_append_left _ (by rw [rdE]; exact hrP),
        VG.Offset.contains_base P (by omega) (by omega)⟩,
      (dPm.sub_left (fun _ h => h)).symm.sub_left subH |>.symm.symm, by omega⟩) fun sC hC => ?_⟩)))
  obtain ⟨s₁, e₁b, dr₁, lr₁, g₁b, m₁b, rd₁b, wr₁b⟩ := ctrArgs_ok sC r hdn hdl
  refine WP.of_runBlock ⟨s₁, e₁b, ?_⟩
  have g₁a : ∀ x, x ∉ SetupRegs → sC.gpr x = s₀.gpr x := fun x hx => by
    obtain ⟨h1, h2, -, -⟩ := not_setupRegs hx
    rw [hC.regs x h2 h2, gE x h1]
  have g₁ : ∀ x, x ∉ SetupRegs → x ≠ c.dataReg → x ≠ c.leftReg → s₁.gpr x = s₀.gpr x :=
    fun x h1 h4 h5 => by rw [g₁b x h4 h5, g₁a x h1]
  have b₁ : s₁.gpr sb = B := by rw [g₁b _ (Ne.symm dsb) (Ne.symm lsb), hC.regs _ (by decide) (by decide), bE]
  have rd₁ : s₁.rd = s₀.rd := by rw [rd₁b, hC.rd, rdE]
  have wr₁ : s₁.wr = s₀.wr := by rw [wr₁b, hC.wr, wrE]
  have mem₁ : s₁.mem = over sE.mem H (8 * c.bw) fun i => sE.mem (P + BitVec.ofNat 64 i) := by rw [m₁b, hC.mem]
  have fC : Frame [⟨H, 8 * c.bw⟩] sE.mem s₁.mem := by rw [mem₁]; exact over_frame _ _ _ _
  have f₁ : Frame [modeRegion c B] s₀.mem s₁.mem :=
    fE.trans (fC.sub fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact ⟨_, List.mem_singleton_self _, subH⟩)
  have sv₁ : ∀ i < 10, s₁.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.gpr (Core.savedRegs.getD i .x19) :=
    fun i hi => by
      rw [← svE i hi]
      exact fC.readW (Region.contains_self _ _) (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx
        exact VG.Offset.disjoint B (.inl (by simp only [Core.hiSlot]; omega)) (by omega)
          (by simp only [Core.hiSlot]; omega)) (by decide)
  have ch₁ : ∀ u < 8 * c.bw, s₁.mem (H + BitVec.ofNat 64 u) = s₀.mem (P + BitVec.ofNat 64 u) := fun u hu => by
    rw [mem₁, over_at hu (by omega)]
    exact fE.bytes (R := ⟨P, 8 * c.bw⟩) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact dPm) (show 8 * c.bw ≤ 2 ^ 64 by omega) hu
  have kr := keyRegs_ne cs.keyRegs_ok
  have subMode : Region.Sub (modeRegion c B) ⟨B, 8 * c.total⟩ := VG.Offset.sub_base B (by omega)
  have f₁' : Frame [⟨B, 8 * c.total⟩] s₀.mem s₁.mem := by
    exact f₁.sub fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact ⟨_, List.mem_singleton_self _, subMode⟩
  have hk₁ : cs.KeyArgs s₁ [⟨B, 8 * c.total⟩] k :=
    cs.keyArgs_congr hk (fun x hx => g₁ x (kr x hx) (fun e => dk (e ▸ hx)) (fun e => lk (e ▸ hx))) rd₁ wr₁ f₁'
  -- The key.
  refine WP.seq (WP.mono (cs.prepare_wp b₁ ⟨by rw [wr₁]; exact hs.wr, hs.fit⟩ List.mem_cons_self hk₁)
    fun s₂ ⟨ready₂, b₂, dr₂, lr₂, f₂, rd₂, wr₂⟩ => ?_)
  have keep₂ : ∀ j, c.slots ≤ j → j < c.total →
      s₂.mem.readW (wordAddr B j) 64 = s₁.mem.readW (wordAddr B j) 64 := fun j h1 h2 =>
    f₂.readW (Region.contains_self _ _) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx
      exact VG.Offset.disjoint_base B (by omega) (by omega)) (by decide)
  have wr₂' : s₂.wr = s₀.wr := by rw [wr₂, wr₁]
  have rd₂' : s₂.rd = s₀.rd := by rw [rd₂, rd₁]
  have left₂ : s₂.gpr c.leftReg = s₀.gpr r.n := by rw [lr₂, lr₁, g₁a _ hr.n]
  have hz₂ : isa.eval (.zero .x c.leftReg) s₂ = some (decide (n = 0)) := by
    rw [eval_zero, left₂]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by rw [← hn, h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [hn, h]; rfl)⟩
  let iv := bytesAt s₀.mem P (8 * c.bw)
  have hiv : iv.length = 8 * c.bw := by simp [iv, bytesAt]
  have hp : GPre c s₂ B D n (8 * c.bw) := ⟨⟨by rw [wr₂']; exact hs.wr, hs.fit⟩, by rw [wr₂']; exact hwD, sDS, fitD⟩
  -- The groups.
  refine WP.seq (WP.mono (M := isa) (Q := CDone cs s₂ B D n k iv)
    (WP.ite (decide (n = 0)) hz₂ (fun h0 => ?_) (fun h0 => ?_)) fun s₄ d₄ => ?_)
  · have hn0 : n = 0 := by simpa using h0
    exact WP.block_nil ⟨b₂, fun _ _ => rfl, fun i hi' => by rw [hn0, Nat.mul_zero] at hi'; omega, Frame.refl _ _,
      rfl, rfl⟩
  · have hn0 : n ≠ 0 := by simpa using h0
    refine cbcDecLoop_wp cs hiv hp ⟨b₂, ready₂, fun _ _ => rfl, ?_, ?_, by omega, fun u hu => ?_,
      fun i _ => by rw [ite_eq_right (by omega)], Frame.refl _ _, rfl, rfl⟩
    · rw [dr₂, dr₁, g₁a _ hr.data, hD]; simp
    · rw [left₂, Nat.mul_zero, Nat.sub_zero, ← hn]; simp
    · have dH : Region.Disjoint ⟨chainAddr c B, 8 * c.bw⟩ (coreRegion c B) :=
        VG.Offset.disjoint_base B (by simp only [Core.hiSlot]; omega) (by simp only [Core.hiSlot]; omega)
      rw [Nat.mul_zero, cbcPrev, ite_eq_left rfl,
        f₂.bytes (R := ⟨chainAddr c B, 8 * c.bw⟩) (fun x hx => by
          simp only [List.mem_singleton] at hx; subst hx; exact dH) (show 8 * c.bw ≤ 2 ^ 64 by omega) hu,
        ch₁ u hu, bytesAt_getD _ _ hu]
  -- The exit.
  have hsv : ∀ i < 10, Core.savedRegs.getD i .x19 ≠ sb := by decide
  have hinj : ∀ i < 10, ∀ j < 10, Core.savedRegs.getD i .x19 = Core.savedRegs.getD j .x19 → i = j := by decide
  obtain ⟨s₅, e₅, v₅, -, m₅, rd₅, wr₅⟩ := loads_ok (B := B) c.slots (fun i => Core.savedRegs.getD i .x19) 10 s₄
    d₄.base hsv hinj (by omega) (fun i hi' => by
      rw [d₄.rd, d₄.wr, rd₂', wr₂']
      exact inRd (slot_wr hs.wr hN (by omega)))
  refine WP.of_runBlock ⟨s₅, e₅, fun i hi' => ?_, ?_, ?_, by rw [rd₅, d₄.rd, rd₂'], by rw [wr₅, d₄.wr, wr₂']⟩
  · rw [v₅ i hi', d₄.saved i hi', keep₂ _ (by omega) (by omega), sv₁ i hi']
  · have subCore : ∀ x ∈ [coreRegion c B], Region.Sub x ⟨B, 8 * c.total⟩ := fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact Region.sub_prefix (by omega)
    rw [m₅, cbc_of_dinv (cs.cipher_len k) hiv d₄.data,
      blocksOf_frame f₂ (by omega) (fun x hx => sDS.sub_right (subCore x hx)),
      blocksOf_frame f₁' (by omega) (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact sDS)]
  · rw [m₅]
    refine (f₁'.trans (f₂.sub fun x hx => ⟨⟨B, 8 * c.total⟩, List.mem_cons_self, by
        simp only [List.mem_singleton] at hx; subst hx; exact Region.sub_prefix (by omega)⟩)).sub
      (fun x hx => ⟨x, by simp only [List.mem_singleton] at hx; subst hx; exact List.mem_cons_self,
        fun _ h => h⟩) |>.trans d₄.frame

end VG.Proof.Modes.AArch64
