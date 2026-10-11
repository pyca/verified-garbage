import VerifiedGarbage.Proof.Modes.X86_64.CbcGroup
import VerifiedGarbage.Proof.Modes.X86_64.Ctr

/-!
# CBC decryption on x86-64, for any core: the whole function

`cbcDecrypt_wp`: `c.cbcDecrypt r`, for a core `c` with `CoreSpec c` whose
cipher is the inverse cipher `CIPH⁻¹_K`, and its arguments in the registers
`r`, replaces the `n` blocks at `D` with their CBC decryption under the key
`k` that its key arguments give, from the IV at `P` (only read); it keeps
the callee-saved registers, and writes nothing but the scratch buffer and
the data. Each cipher's contract follows from it (with the constant-time
check of its own code).
-/

namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Modes.X86_64
open VG.Impl.Aes.X86_64 (sb movR movS st)
open VG.Spec.Aes (bytesAt)

variable {c : Core}

theorem cbcDecrypt_wp (cs : BlockSpec c) {r : CtrRegs} (hr : RegsOk r) (hdn : c.dataReg ≠ r.n) {s₀ : State}
    {B P D : Addr} {n : Nat} {k : cs.Key} (hB : s₀.gpr r.scr = B) (hP : s₀.gpr r.ctr = P) (hD : s₀.gpr r.data = D)
    (hn : (s₀.gpr r.n).toNat = n) (hs : ScrIn s₀ B c.ctrSlots) (hrP : (⟨P, 8 * c.bw⟩ : Region) ∈ s₀.rd)
    (hwD : (⟨D, 8 * c.bw * n⟩ : Region) ∈ s₀.wr) (sPS : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨B, 8 * c.ctrSlots⟩)
    (sDS : Region.Disjoint ⟨D, 8 * c.bw * n⟩ ⟨B, 8 * c.ctrSlots⟩)
    (fitD : D.toNat + 8 * c.bw * n ≤ 2 ^ 64) (hk : cs.KeyArgs s₀ [⟨B, 8 * c.ctrSlots⟩] k) :
    WP isa (c.cbcDecrypt r) s₀ fun s' => (∀ x ∈ calleeSaved, s'.gpr x = s₀.gpr x) ∧
      blocksOf (8 * c.bw) s'.mem D n =
        Spec.Cbc.decrypt (cs.cipher k) (bytesAt s₀.mem P (8 * c.bw)) (blocksOf (8 * c.bw) s₀.mem D n) ∧
      Frame [⟨B, 8 * c.ctrSlots⟩, ⟨D, 8 * c.bw * n⟩] s₀.mem s'.mem ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr := by
  have hL := cs.layout
  have hsm := hL.small
  have hroom := hL.room
  have hbw0 := hL.bw_pos
  have hbw2 := hL.bw_le
  have hN : 8 * c.ctrSlots < 2 ^ 64 := by simp only [Core.ctrSlots]; omega
  obtain ⟨hregs, hdl⟩ := regsOk_ne cs.regs_ok
  obtain ⟨da, db, -, -, -, dsb, dsp, dk⟩ := hregs c.dataReg List.mem_cons_self
  obtain ⟨la, lb, -, -, -, lsb, lsp, lk⟩ := hregs c.leftReg (List.mem_cons_of_mem _ List.mem_cons_self)
  let H := chainAddr c B
  have subMode : Region.Sub (modeRegion c B) ⟨B, 8 * c.ctrSlots⟩ :=
    VG.Offset.sub_base B (by simp only [Core.ctrSlots]; omega)
  have subH : Region.Sub ⟨H, 8 * c.bw⟩ (modeRegion c B) := VG.Offset.sub B (by simp only [Core.hiSlot]; omega)
    (by simp only [Core.hiSlot]; omega)
  have dPm : Region.Disjoint ⟨P, 8 * c.bw⟩ (modeRegion c B) := sPS.sub_right subMode
  -- The entry, and the IV to the chaining value.
  obtain ⟨sE, eE, bE, svE, fE, gE, rdE, wrE⟩ := entry_ok hsm hroom s₀ hB hs
  unfold Core.cbcDecrypt
  refine WP.seq (WP.block_append (WP.block_append (WP.of_runBlock ⟨sE, eE, WP.mono (copyN_wp (k := c.bw) (P := H)
    (Q := P) ⟨by rw [bE], by rw [gE _ hr.ctr.1, hP]; simp, by decide, Ne.symm hr.ctr.2.1,
      fun w hw => ⟨_, by rw [wrE]; exact hs.wr, by
        rw [addr_add]
        exact VG.Offset.contains_base B (by simp only [Core.hiSlot, Core.ctrSlots]; omega)
          (by simp only [Core.hiSlot]; omega)⟩,
      fun w hw => ⟨_, List.mem_append_left _ (by rw [rdE]; exact hrP),
        VG.Offset.contains_base P (by omega) (by omega)⟩,
      (dPm.sub_left (fun _ h => h)).symm.sub_left subH |>.symm.symm, by omega⟩) fun sC hC => ?_⟩)))
  obtain ⟨s₁, e₁b, dr₁, lr₁, g₁b, m₁b, rd₁b, wr₁b⟩ := ctrArgs_ok sC r hdn hdl
  refine WP.of_runBlock ⟨s₁, e₁b, ?_⟩
  have g₁a : ∀ x, x ≠ sb → x ≠ .rax → x ≠ .rbx → sC.gpr x = s₀.gpr x := fun x h1 h2 _ => by
    rw [hC.regs x h2, gE x h1]
  have g₁ : ∀ x, x ≠ sb → x ≠ .rax → x ≠ .rbx → x ≠ c.dataReg → x ≠ c.leftReg → s₁.gpr x = s₀.gpr x :=
    fun x h1 h2 h3 h4 h5 => by rw [g₁b x h4 h5, g₁a x h1 h2 h3]
  have b₁ : s₁.gpr sb = B := by rw [g₁b _ (Ne.symm dsb) (Ne.symm lsb), hC.regs _ (by decide), bE]
  have rd₁ : s₁.rd = s₀.rd := by rw [rd₁b, hC.rd, rdE]
  have wr₁ : s₁.wr = s₀.wr := by rw [wr₁b, hC.wr, wrE]
  have mem₁ : s₁.mem = over sE.mem H (8 * c.bw) fun i => sE.mem (P + BitVec.ofNat 64 i) := by rw [m₁b, hC.mem]
  have fC : Frame [⟨H, 8 * c.bw⟩] sE.mem s₁.mem := fun x hx => by
    rw [mem₁]; exact over_out fun h => hx _ List.mem_cons_self (by simp only [Region.Contains]; omega)
  have f₁ : Frame [modeRegion c B] s₀.mem s₁.mem :=
    fE.trans (fC.sub fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact ⟨_, List.mem_singleton_self _, subH⟩)
  have sv₁ : ∀ i < 6, s₁.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.gpr (Core.savedRegs.getD i .rbx) :=
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
  have subMode : Region.Sub (modeRegion c B) ⟨B, 8 * c.ctrSlots⟩ :=
    VG.Offset.sub_base B (by simp only [Core.ctrSlots]; omega)
  have f₁' : Frame [⟨B, 8 * c.ctrSlots⟩] s₀.mem s₁.mem := by
    exact f₁.sub fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact ⟨_, List.mem_singleton_self _, subMode⟩
  have hk₁ : cs.KeyArgs s₁ [⟨B, 8 * c.ctrSlots⟩] k :=
    cs.keyArgs_congr hk (fun x hx => g₁ x (kr x hx).1 (kr x hx).2.1 (kr x hx).2.2 (fun e => dk (e ▸ hx))
      (fun e => lk (e ▸ hx))) rd₁ wr₁ f₁'
  -- The key.
  refine WP.seq (WP.mono (cs.prepare_wp b₁ ⟨by rw [wr₁]; exact hs.wr, hs.fit⟩ List.mem_cons_self hk₁)
    fun s₂ ⟨ready₂, b₂, rsp₂, dr₂, lr₂, f₂, rd₂, wr₂⟩ => ?_)
  have keep₂ : ∀ j, c.slots ≤ j → j < c.ctrSlots →
      s₂.mem.readW (wordAddr B j) 64 = s₁.mem.readW (wordAddr B j) 64 := fun j h1 h2 =>
    f₂.readW (Region.contains_self _ _) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx
      exact VG.Offset.disjoint_base B (by omega) (by omega)) (by decide)
  have wr₂' : s₂.wr = s₀.wr := by rw [wr₂, wr₁]
  have rd₂' : s₂.rd = s₀.rd := by rw [rd₂, rd₁]
  -- Any blocks?
  obtain ⟨s₃, e₃, z₃, g₃, m₃, rd₃, wr₃⟩ := testSelf_ok s₂ c.leftReg
  refine WP.seq (WP.of_runBlock ⟨s₃, e₃, ?_⟩)
  have left₃ : s₃.gpr c.leftReg = s₀.gpr r.n := by rw [g₃, lr₂, lr₁, g₁a _ hr.n.1 hr.n.2.1 hr.n.2.2]
  have hz₃ : s₃.zf = some (decide (n = 0)) := by
    rw [z₃, ← g₃, left₃]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by rw [← hn, h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [hn, h]; rfl)⟩
  have mem₃ : s₃.mem = s₂.mem := m₃
  have b₃ : s₃.gpr sb = B := by rw [g₃, b₂]
  have rsp₃ : s₃.gpr .rsp = s₀.gpr .rsp := by
    rw [g₃, rsp₂, g₁ _ (by decide) (by decide) (by decide) (Ne.symm dsp) (Ne.symm lsp)]
  have rd₃' : s₃.rd = s₀.rd := by rw [rd₃, rd₂']
  have wr₃' : s₃.wr = s₀.wr := by rw [wr₃, wr₂']
  let iv := bytesAt s₀.mem P (8 * c.bw)
  have hiv : iv.length = 8 * c.bw := by simp [iv, bytesAt]
  have hp : GPre c s₃ B D n (8 * c.bw) := ⟨⟨by rw [wr₃']; exact hs.wr, hs.fit⟩, by rw [wr₃']; exact hwD, sDS, fitD⟩
  -- The groups.
  refine WP.seq (WP.mono (M := isa) (Q := CDone cs s₃ B D n k iv)
    (WP.ite (decide (n = 0)) (by simp [X86_64.eval, hz₃]) (fun h0 => ?_) (fun h0 => ?_)) fun s₄ d₄ => ?_)
  · have hn0 : n = 0 := by simpa using h0
    exact WP.block_nil ⟨b₃, rfl, fun _ _ => rfl, fun i hi' => by rw [hn0, Nat.mul_zero] at hi'; omega, Frame.refl _ _, rfl, rfl⟩
  · have hn0 : n ≠ 0 := by simpa using h0
    refine cbcDecLoop_wp cs hiv hp ⟨b₃, rfl, cs.ready_frame ready₂ (by rw [mem₃]; exact Frame.refl [] _)
        (fun _ h => by simp at h) (fun r _ => by rw [g₃]), fun _ _ => rfl, ?_, ?_, by omega, fun u hu => ?_,
      fun i _ => by rw [ite_eq_right (by omega)], Frame.refl _ _, rfl, rfl⟩
    · rw [g₃, dr₂, dr₁, g₁a _ hr.data.1 hr.data.2.1 hr.data.2.2, hD]; simp
    · rw [left₃, Nat.mul_zero, Nat.sub_zero, ← hn]; simp
    · have dH : Region.Disjoint ⟨chainAddr c B, 8 * c.bw⟩ (coreRegion c B) :=
        VG.Offset.disjoint_base B (by simp only [Core.hiSlot]; omega) (by simp only [Core.hiSlot]; omega)
      rw [Nat.mul_zero, cbcPrev, ite_eq_left rfl, mem₃,
        f₂.bytes (R := ⟨chainAddr c B, 8 * c.bw⟩) (fun x hx => by
          simp only [List.mem_singleton] at hx; subst hx; exact dH) (show 8 * c.bw ≤ 2 ^ 64 by omega) hu,
        ch₁ u hu, bytesAt_getD _ _ hu]
  -- The exit.
  have hsv : ∀ i < 6, Core.savedRegs.getD i .rbx ≠ sb := by decide
  have hinj : ∀ i < 6, ∀ j < 6, Core.savedRegs.getD i .rbx = Core.savedRegs.getD j .rbx → i = j := by decide
  obtain ⟨s₅, e₅, v₅, o₅, m₅, rd₅, wr₅⟩ := loads_ok (B := B) c.slots (fun i => Core.savedRegs.getD i .rbx) 6 s₄
    d₄.base hsv hinj (fun i hi' => by
      rw [d₄.rd, d₄.wr, rd₃', wr₃']
      exact inRd (slot_wr hs.wr hN (by simp only [Core.ctrSlots]; omega)))
  refine WP.of_runBlock ⟨s₅, e₅, fun x hx => ?_, ?_, ?_, by rw [rd₅, d₄.rd, rd₃'], by rw [wr₅, d₄.wr, wr₃']⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hx
    have hsaved : ∀ i < 6, s₅.gpr (Core.savedRegs.getD i .rbx) = s₀.gpr (Core.savedRegs.getD i .rbx) :=
      fun i hi' => by
        rw [v₅ i hi', d₄.saved i hi', mem₃, keep₂ _ (by omega) (by simp only [Core.ctrSlots]; omega), sv₁ i hi']
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsaved 0 (by decide)
    · exact hsaved 1 (by decide)
    · rw [o₅ _ (fun i hi' => by revert i; decide), d₄.rsp, rsp₃]
    · exact hsaved 2 (by decide)
    · exact hsaved 3 (by decide)
    · exact hsaved 4 (by decide)
    · exact hsaved 5 (by decide)
  · have subCore : ∀ x ∈ [coreRegion c B], Region.Sub x ⟨B, 8 * c.ctrSlots⟩ := fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact Region.sub_prefix (by simp only [Core.ctrSlots]; omega)
    rw [m₅, cbc_of_dinv (cs.cipher_len k) hiv d₄.data, mem₃,
      blocksOf_frame f₂ (by omega) (fun x hx => sDS.sub_right (subCore x hx)),
      blocksOf_frame f₁' (by omega) (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact sDS)]
  · rw [m₅]
    refine (f₁'.trans (f₂.sub fun x hx => ⟨⟨B, 8 * c.ctrSlots⟩, List.mem_cons_self, by
        simp only [List.mem_singleton] at hx; subst hx; exact Region.sub_prefix (by simp only [Core.ctrSlots]; omega)⟩)).sub
      (fun x hx => ⟨x, by simp only [List.mem_singleton] at hx; subst hx; exact List.mem_cons_self,
        fun _ h => h⟩) |>.trans ?_
    rw [← mem₃]
    exact d₄.frame

end VG.Proof.Modes.X86_64
