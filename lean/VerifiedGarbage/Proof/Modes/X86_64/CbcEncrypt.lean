import VerifiedGarbage.Proof.Modes.X86_64.CbcEncLoop
import VerifiedGarbage.Proof.Modes.X86_64.Ctr

/-!
# CBC encryption on x86-64, for any core: the whole function

`cbcEncrypt_wp`: `c.cbcEncrypt r`, for a core `c` with `CoreSpec c` whose
cipher is the forward cipher `CIPH_K`, and its arguments in the registers
`r`, replaces the `n` blocks at `D` with their CBC encryption under the key
`k` that its key arguments give, from the IV at `P` (only read); it keeps
the callee-saved registers, and writes nothing but the scratch buffer and
the data.
-/

namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Modes.X86_64
open VG.Impl.Aes.X86_64 (sb movR movS st)
open VG.Spec.Aes (bytesAt)

variable {c : Core}

theorem cbcEncrypt_wp (cs : BlockSpec c) {r : CtrRegs} (hr : RegsOk r) (hdn : c.dataReg ≠ r.n) {s₀ : State}
    {B P D : Addr} {n : Nat} {k : cs.Key} (hB : s₀.gpr r.scr = B) (hP : s₀.gpr r.ctr = P) (hD : s₀.gpr r.data = D)
    (hn : (s₀.gpr r.n).toNat = n) (hs : ScrIn s₀ B c.ctrSlots) (hrP : (⟨P, 8 * c.bw⟩ : Region) ∈ s₀.rd)
    (hwD : (⟨D, 8 * c.bw * n⟩ : Region) ∈ s₀.wr) (sPS : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨B, 8 * c.ctrSlots⟩)
    (sDS : Region.Disjoint ⟨D, 8 * c.bw * n⟩ ⟨B, 8 * c.ctrSlots⟩)
    (sPD : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨D, 8 * c.bw * n⟩) (fitD : D.toNat + 8 * c.bw * n ≤ 2 ^ 64)
    (hk : cs.KeyArgs s₀ [⟨B, 8 * c.ctrSlots⟩, ⟨D, 8 * c.bw * n⟩] k) :
    WP isa (c.cbcEncrypt r) s₀ fun s' => (∀ x ∈ calleeSaved, s'.gpr x = s₀.gpr x) ∧
      blocksOf (8 * c.bw) s'.mem D n =
        Spec.Cbc.encrypt (cs.cipher k) (bytesAt s₀.mem P (8 * c.bw)) (blocksOf (8 * c.bw) s₀.mem D n) ∧
      Frame [⟨B, 8 * c.ctrSlots⟩, ⟨D, 8 * c.bw * n⟩] s₀.mem s'.mem ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr := by
  have hL := cs.layout
  have hsm := hL.small
  have hroom := hL.room
  have hbw0 := hL.bw_pos
  have hbw2 := hL.bw_le
  have hL0 : 0 < 8 * c.bw := by omega
  have h8n : 8 * n ≤ 8 * c.bw * n := Nat.mul_le_mul_right n (by omega)
  have hn64 : 8 * c.bw * n ≤ 2 ^ 64 := by omega
  have hLn : 8 * c.bw * n = 8 * (c.bw * n) := Nat.mul_assoc _ _ _
  have hqr : ∀ {q r}, q < n → r < 8 * c.bw → 8 * c.bw * q + r < 8 * c.bw * n := fun hq hr => by
    have := idx_lt (L := 8 * c.bw) hq; omega
  have hN : 8 * c.ctrSlots < 2 ^ 64 := by simp only [Core.ctrSlots]; omega
  obtain ⟨hregs, hdl⟩ := regsOk_ne cs.regs_ok
  obtain ⟨da, db, -, -, -, dsb, dsp, dk⟩ := hregs c.dataReg List.mem_cons_self
  obtain ⟨la, lb, -, -, -, lsb, lsp, lk⟩ := hregs c.leftReg (List.mem_cons_of_mem _ List.mem_cons_self)
  have subMode : Region.Sub (modeRegion c B) ⟨B, 8 * c.ctrSlots⟩ :=
    VG.Offset.sub_base B (by simp only [Core.ctrSlots]; omega)
  -- The entry.
  obtain ⟨s₁, e₁, b₁, sv₁, f₁, g₁, rd₁, wr₁⟩ := entry_ok hsm hroom s₀ hB hs
  unfold Core.cbcEncrypt
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  have mP : ∀ u < 8 * c.bw, s₁.mem (P + BitVec.ofNat 64 u) = s₀.mem (P + BitVec.ofNat 64 u) := fun u hu =>
    f₁.bytes (R := ⟨P, 8 * c.bw⟩) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact sPS.sub_right subMode) (show 8 * c.bw ≤ 2 ^ 64 by omega) hu
  have mD : ∀ i < 8 * c.bw * n, s₁.mem (D + BitVec.ofNat 64 i) = s₀.mem (D + BitVec.ofNat 64 i) := fun i hi =>
    f₁.bytes (R := ⟨D, 8 * c.bw * n⟩) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact sDS.sub_right subMode) hn64 hi
  -- The IV into the first block.
  obtain ⟨s₂a, e₂a, z₂a, g₂a, m₂a, rd₂a, wr₂a⟩ := testSelf_ok s₁ r.n
  have hz₂ : s₂a.zf = some (decide (n = 0)) := by
    rw [z₂a, g₁ _ hr.n.1]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by rw [← hn, h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [hn, h]; rfl)⟩
  let Qw : State → Prop := fun s₂ => s₂.gpr sb = B ∧ (∀ x, x ≠ .rax → s₂.gpr x = s₁.gpr x) ∧ s₂.rd = s₁.rd ∧
    s₂.wr = s₁.wr ∧ Frame [⟨D, 8 * c.bw * n⟩] s₁.mem s₂.mem ∧
    ∀ q < n, ∀ r < 8 * c.bw, s₂.mem (D + BitVec.ofNat 64 (8 * c.bw * q + r)) =
      if q = 0 then s₀.mem (D + BitVec.ofNat 64 (8 * c.bw * q + r)) ^^^ s₀.mem (P + BitVec.ofNat 64 r)
      else s₀.mem (D + BitVec.ofNat 64 (8 * c.bw * q + r))
  have hw : WP isa (c.cbcWhiten r) s₁ Qw := by
    unfold Core.cbcWhiten
    refine WP.seq (WP.of_runBlock ⟨s₂a, e₂a, WP.ite (decide (n = 0)) (by simp [X86_64.eval, hz₂])
      (fun h0 => ?_) (fun h0 => ?_)⟩)
    · have hn0 : n = 0 := by simpa using h0
      exact WP.block_nil ⟨by rw [g₂a, b₁], fun x _ => by rw [g₂a], rd₂a, wr₂a, by rw [m₂a]; exact Frame.refl _ _,
        fun q hq => by omega⟩
    · have hn0 : 0 < n := by simp at h0; omega
      have sub0 : Region.Sub ⟨D + BitVec.ofNat 64 (8 * c.bw * 0), 8 * c.bw⟩ ⟨D, 8 * c.bw * n⟩ :=
        VG.Offset.sub_base D (idx_lt hn0)
      refine WP.mono (xorN_wp (k := c.bw) (P := D + BitVec.ofNat 64 (8 * c.bw * 0)) (Q := P)
        ⟨by rw [g₂a, g₁ _ hr.data.1, hD]; simp, by rw [g₂a, g₁ _ hr.ctr.1, hP]; simp, Ne.symm hr.data.2.1,
          Ne.symm hr.ctr.2.1, fun w hw' => ⟨_, by rw [wr₂a, wr₁]; exact hwD, by
            rw [addr_add]
            exact VG.Offset.contains_base D (by have := idx_lt (L := c.bw) hn0; omega) (by omega)⟩,
          fun w hw' => by
            rw [rd₂a, wr₂a, rd₁, wr₁]
            exact ⟨_, List.mem_append_left _ hrP, VG.Offset.contains_base P (by omega) (by omega)⟩,
          sPD.symm.sub_left sub0, by omega⟩) fun s₂ h₂ => ?_
      refine ⟨by rw [h₂.regs _ (by decide), g₂a, b₁], fun x hx => by rw [h₂.regs x hx, g₂a], by rw [h₂.rd, rd₂a],
        by rw [h₂.wr, wr₂a], ?_, fun q hq r hr => ?_⟩
      · rw [h₂.mem, m₂a]
        exact (over_frame _ _ _ _).sub fun x hx => by
          simp only [List.mem_singleton] at hx; subst hx; exact ⟨_, List.mem_singleton_self _, sub0⟩
      rw [h₂.mem, m₂a, over_blk _ _ _ hn0 hq hr hn64]
      split
      · rename_i h; subst h; rw [addr_add, mD _ (hqr hq hr), mP r hr]
      · exact mD _ (hqr hq hr)
  refine WP.seq (WP.mono hw fun s₂ ⟨b₂, g₂, rd₂, wr₂, f₂, d₂⟩ => ?_)
  -- The data's address and `n`.
  obtain ⟨s₃, e₃, dr₃, lr₃, g₃, m₃, rd₃, wr₃⟩ := ctrArgs_ok s₂ r hdn hdl
  refine WP.seq (WP.of_runBlock ⟨s₃, e₃, ?_⟩)
  have g₃' : ∀ x, x ≠ sb → x ≠ .rax → x ≠ c.dataReg → x ≠ c.leftReg → s₃.gpr x = s₀.gpr x :=
    fun x h1 h2 h3 h4 => by rw [g₃ x h3 h4, g₂ x h2, g₁ x h1]
  have b₃ : s₃.gpr sb = B := by rw [g₃ _ (Ne.symm dsb) (Ne.symm lsb), b₂]
  have rd₃' : s₃.rd = s₀.rd := by rw [rd₃, rd₂, rd₁]
  have wr₃' : s₃.wr = s₀.wr := by rw [wr₃, wr₂, wr₁]
  have f₃ : Frame [⟨B, 8 * c.ctrSlots⟩, ⟨D, 8 * c.bw * n⟩] s₀.mem s₃.mem := by
    rw [m₃]
    exact (f₁.sub fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact ⟨_, List.mem_cons_self, subMode⟩).trans
      (f₂.sub fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx
        exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩)
  have kr := keyRegs_ne cs.keyRegs_ok
  have hk₃ : cs.KeyArgs s₃ [⟨B, 8 * c.ctrSlots⟩, ⟨D, 8 * c.bw * n⟩] k :=
    cs.keyArgs_congr hk (fun x hx => g₃' x (kr x hx).1 (kr x hx).2.1 (fun e => dk (e ▸ hx))
      (fun e => lk (e ▸ hx))) rd₃' wr₃' f₃
  -- The key.
  refine WP.seq (WP.mono (cs.prepare_wp b₃ ⟨by rw [wr₃']; exact hs.wr, hs.fit⟩ List.mem_cons_self hk₃)
    fun s₄ ⟨ready₄, b₄, rsp₄, dr₄, lr₄, f₄, rd₄, wr₄⟩ => ?_)
  have rd₄' : s₄.rd = s₀.rd := by rw [rd₄, rd₃']
  have wr₄' : s₄.wr = s₀.wr := by rw [wr₄, wr₃']
  -- Any blocks?
  obtain ⟨s₅, e₅, z₅, g₅, m₅, rd₅, wr₅⟩ := testSelf_ok s₄ c.leftReg
  refine WP.seq (WP.of_runBlock ⟨s₅, e₅, ?_⟩)
  have left₅ : s₅.gpr c.leftReg = s₀.gpr r.n := by
    rw [g₅, lr₄, lr₃, g₂ _ hr.n.2.1, g₁ _ hr.n.1]
  have hz₅ : s₅.zf = some (decide (n = 0)) := by
    rw [z₅, ← g₅, left₅]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by rw [← hn, h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [hn, h]; rfl)⟩
  have mem₅ : s₅.mem = s₄.mem := m₅
  have b₅ : s₅.gpr sb = B := by rw [g₅, b₄]
  have rsp₅ : s₅.gpr .rsp = s₀.gpr .rsp := by
    rw [g₅, rsp₄, g₃' _ (by decide) (by decide) (Ne.symm dsp) (Ne.symm lsp)]
  have rd₅' : s₅.rd = s₀.rd := by rw [rd₅, rd₄']
  have wr₅' : s₅.wr = s₀.wr := by rw [wr₅, wr₄']
  let iv := bytesAt s₀.mem P (8 * c.bw)
  have hiv : iv.length = 8 * c.bw := by simp [iv, bytesAt]
  have hp : GPre c s₅ B D n (8 * c.bw) := ⟨⟨by rw [wr₅']; exact hs.wr, hs.fit⟩, by rw [wr₅']; exact hwD, sDS, fitD⟩
  have dCore : ∀ x ∈ [coreRegion c B], Region.Disjoint ⟨D, 8 * c.bw * n⟩ x := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; exact sDS.sub_right (Region.sub_prefix (by
      simp only [Core.ctrSlots]; omega))
  -- The blocks.
  refine WP.seq (WP.mono (M := isa) (Q := EDone cs s₅ s₀.mem B D n k iv)
    (WP.ite (decide (n = 0)) (by simp [X86_64.eval, hz₅]) (fun h0 => ?_) (fun h0 => ?_)) fun s₆ d₆ => ?_)
  · have hn0 : n = 0 := by simpa using h0
    exact WP.block_nil ⟨b₅, rfl, fun _ _ => rfl, fun i hi' => by rw [hn0, Nat.mul_zero] at hi'; omega,
      Frame.refl _ _, rfl, rfl⟩
  · have hn0 : n ≠ 0 := by simpa using h0
    refine cbcEncLoop_wp cs hiv hp ⟨b₅, rfl, cs.ready_frame ready₄ (by rw [mem₅]; exact Frame.refl [] _)
        (fun _ h => by simp at h) (fun r _ => by rw [g₅]), fun _ _ => rfl, ?_, ?_, by omega, fun q hq r hr => ?_,
      Frame.refl _ _, rfl, rfl⟩
    · rw [g₅, dr₄, dr₃, g₂ _ hr.data.2.1, g₁ _ hr.data.1, hD]; simp
    · rw [left₅, Nat.sub_zero, ← hn]; simp
    · rw [mem₅, f₄.bytes (R := ⟨D, 8 * c.bw * n⟩) dCore hn64 (hqr hq hr), m₃, d₂ q hq r hr, encByte,
        ite_eq_right (Nat.not_lt_zero _)]
      split
      · rw [cbcEncPrev, ite_eq_left rfl, bytesAt_getD _ _ hr]
      · rfl
  -- The exit.
  have hsv : ∀ i < 6, Core.savedRegs.getD i .rbx ≠ sb := by decide
  have hinj : ∀ i < 6, ∀ j < 6, Core.savedRegs.getD i .rbx = Core.savedRegs.getD j .rbx → i = j := by decide
  obtain ⟨s₇, e₇, v₇, o₇, m₇, rd₇, wr₇⟩ := loads_ok (B := B) c.slots (fun i => Core.savedRegs.getD i .rbx) 6 s₆
    d₆.base hsv hinj (fun i hi' => by
      rw [d₆.rd, d₆.wr, rd₅', wr₅']
      exact inRd (slot_wr hs.wr hN (by simp only [Core.ctrSlots]; omega)))
  refine WP.of_runBlock ⟨s₇, e₇, fun x hx => ?_, ?_, ?_, by rw [rd₇, d₆.rd, rd₅'], by rw [wr₇, d₆.wr, wr₅']⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hx
    have hsaved : ∀ i < 6, s₇.gpr (Core.savedRegs.getD i .rbx) = s₀.gpr (Core.savedRegs.getD i .rbx) :=
      fun i hi' => by
        rw [v₇ i hi', d₆.saved i hi', mem₅, ← sv₁ i hi']
        refine (f₄.readW (Region.contains_self _ _) (fun x hx => by
          simp only [List.mem_singleton] at hx; subst hx
          exact VG.Offset.disjoint_base B (by omega) (by omega)) (by decide)).trans ?_
        rw [m₃]
        exact f₂.readW (Region.contains_self _ _) (fun x hx => by
          simp only [List.mem_singleton] at hx; subst hx
          exact (sDS.sub_right (VG.Offset.sub_base B (show 8 * (c.slots + i) + 8 ≤ 8 * c.ctrSlots by
            simp only [Core.ctrSlots]; omega))).symm) (by decide)
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsaved 0 (by decide)
    · exact hsaved 1 (by decide)
    · rw [o₇ _ (fun i hi' => by revert i; decide), d₆.rsp, rsp₅]
    · exact hsaved 2 (by decide)
    · exact hsaved 3 (by decide)
    · exact hsaved 4 (by decide)
    · exact hsaved 5 (by decide)
  · rw [m₇]; exact cbcEnc_of_dinv (cs.cipher_len k) d₆.data
  · rw [m₇]
    refine (f₃.trans (f₄.sub fun x hx => ⟨⟨B, 8 * c.ctrSlots⟩, List.mem_cons_self, by
        simp only [List.mem_singleton] at hx; subst hx; exact Region.sub_prefix (by
          simp only [Core.ctrSlots]; omega)⟩)).trans ?_
    rw [← mem₅]
    exact d₆.frame

end VG.Proof.Modes.X86_64
