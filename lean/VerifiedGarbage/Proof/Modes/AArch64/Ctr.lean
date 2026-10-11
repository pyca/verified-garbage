import VerifiedGarbage.Proof.Modes.AArch64.Group

/-!
# CTR on AArch64, for any core: the whole function

`ctr_wp`: `c.ctr r`, for a core `c` with `CoreSpec c` and its arguments in
the registers `r`, transforms the `n` blocks at `D` by CTR with the
core's cipher under the key `k` that its key arguments give, from the
counter block at `P`, which it replaces with the one to continue from;
it keeps the callee-saved registers `x19`–`x28`, and writes nothing but
the scratch buffer, the counter block and the data. Each cipher's contract follows
from it (with the constant-time check of its own code).
-/

namespace VG.Proof.Modes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Modes.AArch64
open VG.Impl.Aes.AArch64 (sb movR ldS stS)
open VG.Spec.Aes (bytesAt)

variable {c : Core}

theorem ctrLoop_wp (cs : CoreSpec c) {s₀ : State} {B D : Addr} {n : Nat} {k : cs.Key} {V : Nat}
    (hp : GPre c s₀ B D n) {s : State} (hi : GInv cs s₀ B D n k V 0 s) :
    WP isa (.loop c.ctrGroup (.nonzero .x c.leftReg)) s (GDone cs s₀ B D n k V) := by
  refine WP.loop (M := isa) (fun m s => ∃ g, m = n - c.G * g ∧ GInv cs s₀ B D n k V g s) (fun m s hs => ?_) n s
    ⟨0, by simp, hi⟩
  obtain ⟨g, rfl, hg⟩ := hs
  refine WP.mono (ctrGroup_wp cs hp hg) fun s' h => ?_
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨z, d⟩
  · have hG := cs.layout.G_pos
    exact .inr ⟨z, n - c.G * (g + 1),
      by have := d.lt; have := hg.lt; rw [Nat.mul_succ] at *; omega, g + 1, rfl, d⟩

/-- The blocks at `D` outside a frame. -/
theorem blocksOf_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {L : Nat} (hL : L ≤ 2 ^ 64)
    {D : Addr} {n : Nat} (hd : ∀ r ∈ rs, Region.Disjoint ⟨D, L * n⟩ r) : blocksOf L m' D n = blocksOf L m D n := by
  simp only [blocksOf]
  refine List.map_congr_left fun j hj => ?_
  have hj := idx_lt (L := L) (List.mem_range.mp hj)
  exact bytesAt_frame hf (fun r hr => (hd r hr).sub_left (VG.Offset.sub_base D hj)) hL

theorem cbcBlocks_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {D : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨D, 16 * n⟩ r) : Spec.Cbc.blocksAt m' D n = Spec.Cbc.blocksAt m D n :=
  blocksOf_frame hf (by decide) hd

theorem keyRegs_ne {c : Core} (h : c.keyRegs.all (fun r => r != sb && r != .x6 && r != .x7 && r != .x10) = true) :
    ∀ x ∈ c.keyRegs, x ∉ SetupRegs := fun x hx => by
  have := List.all_eq_true.mp h x hx
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
  simp only [SetupRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩

/-- `CoreSpec.Ready`, `prepare`'s and the test's states, and the loop. -/
theorem ctr_wp (cs : CoreSpec c) {r : CtrRegs} (hr : RegsOk r) (hdn : c.dataReg ≠ r.n) {s₀ : State} {B P D : Addr}
    {n : Nat} {k : cs.Key} (hB : s₀.gpr r.scr = B) (hP : s₀.gpr r.ctr = P) (hD : s₀.gpr r.data = D)
    (hn : (s₀.gpr r.n).toNat = n) (hs : ScrIn s₀ B c.total) (hwP : (⟨P, 16⟩ : Region) ∈ s₀.wr)
    (hwD : (⟨D, 16 * n⟩ : Region) ∈ s₀.wr) (sPS : Region.Disjoint ⟨P, 16⟩ ⟨B, 8 * c.total⟩)
    (sDS : Region.Disjoint ⟨D, 16 * n⟩ ⟨B, 8 * c.total⟩) (sPD : Region.Disjoint ⟨P, 16⟩ ⟨D, 16 * n⟩)
    (fitD : D.toNat + 16 * n ≤ 2 ^ 64) (hk : cs.KeyArgs s₀ [⟨B, 8 * c.total⟩, ⟨P, 16⟩] k) :
    WP isa (c.ctr r) s₀ fun s' => (∀ i < 10, s'.gpr (Core.savedRegs.getD i .x19) = s₀.gpr (Core.savedRegs.getD i .x19)) ∧
      Spec.Cbc.blocksAt s'.mem D n =
        Spec.Ctr.crypt (cs.cipher k) (bytesAt s₀.mem P 16) (Spec.Cbc.blocksAt s₀.mem D n) ∧
      bytesAt s'.mem P 16 = Spec.Ctr.next (bytesAt s₀.mem P 16) n ∧
      Frame [⟨B, 8 * c.total⟩, ⟨P, 16⟩, ⟨D, 16 * n⟩] s₀.mem s'.mem ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr := by
  have hL := cs.layout
  have hsm := hL.small
  have hroom := hL.room
  have hN : 8 * c.total < 2 ^ 64 := by omega
  obtain ⟨hregs, hdl⟩ := regsOk_ne cs.regs_ok
  obtain ⟨-, dsb, dk⟩ := hregs c.dataReg List.mem_cons_self
  obtain ⟨-, lsb, lk⟩ := hregs c.leftReg (List.mem_cons_of_mem _ List.mem_cons_self)
  -- The entry.
  obtain ⟨s₁a, e₁a, b₁a, sv₁, hi₁, lo₁, bP₁, f₁, g₁a, rd₁a, wr₁a⟩ := setup_ok hL hr s₀ hB hs hP hwP sPS
  obtain ⟨s₁, e₁b, dr₁, lr₁, g₁b, m₁b, rd₁b, wr₁b⟩ := ctrArgs_ok s₁a r hdn hdl
  have g₁ : ∀ x, x ∉ SetupRegs → x ≠ c.dataReg → x ≠ c.leftReg → s₁.gpr x = s₀.gpr x :=
    fun x h1 h4 h5 => by rw [g₁b x h4 h5, g₁a x h1]
  have b₁ : s₁.gpr sb = B := by rw [g₁b _ (Ne.symm dsb) (Ne.symm lsb), b₁a]
  have rd₁ : s₁.rd = s₀.rd := by rw [rd₁b, rd₁a]
  have wr₁ : s₁.wr = s₀.wr := by rw [wr₁b, wr₁a]
  have mem₁ : s₁.mem = s₁a.mem := m₁b
  unfold Core.ctr
  refine WP.seq (WP.of_runBlock ⟨s₁, by rw [runBlock_app, e₁a, Option.bind_some, e₁b], ?_⟩)
  have kr := keyRegs_ne cs.keyRegs_ok
  have subMode : Region.Sub (modeRegion c B) ⟨B, 8 * c.total⟩ := VG.Offset.sub_base B (by omega)
  have f₁' : Frame [⟨B, 8 * c.total⟩, ⟨P, 16⟩] s₀.mem s₁.mem := by
    rw [mem₁]
    exact f₁.sub fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact ⟨_, List.mem_cons_self, subMode⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  have hk₁ : cs.KeyArgs s₁ [⟨B, 8 * c.total⟩, ⟨P, 16⟩] k :=
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
  have left₂ : s₂.gpr c.leftReg = s₀.gpr r.n := by
    rw [lr₂, lr₁, g₁a _ hr.n]
  have hz₂ : isa.eval (.zero .x c.leftReg) s₂ = some (decide (n = 0)) := by
    rw [eval_zero, left₂]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by rw [← hn, h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [hn, h]; rfl)⟩
  let V := ctrVal s₀.mem P
  have hp : GPre c s₂ B D n := ⟨⟨by rw [wr₂']; exact hs.wr, hs.fit⟩, by rw [wr₂']; exact hwD, sDS, fitD⟩
  -- The groups.
  refine WP.seq (WP.mono (M := isa) (Q := GDone cs s₂ B D n k V)
    (WP.ite (decide (n = 0)) hz₂ (fun h0 => ?_) (fun h0 => ?_)) fun s₄ d₄ => ?_)
  · have hn0 : n = 0 := by simpa using h0
    exact WP.block_nil ⟨b₂, fun _ _ => rfl, fun i hi' => by omega, Frame.refl _ _, rfl, rfl⟩
  · have hn0 : n ≠ 0 := by simpa using h0
    have hsl : ∀ j, j = c.hiSlot ∨ j = c.loSlot →
        s₂.mem.readW (wordAddr B j) 64 = s₁.mem.readW (wordAddr B j) 64 := fun j hj =>
      keep₂ j (by rcases hj with rfl | rfl <;> simp only [Core.hiSlot, Core.loSlot] <;> omega)
        (by rcases hj with rfl | rfl <;> simp only [Core.hiSlot, Core.loSlot] <;> omega)
    refine ctrLoop_wp cs hp ⟨b₂, ready₂, fun _ _ => rfl, ?_, ?_, by omega, ?_, ?_,
      fun i _ => by rw [ite_eq_right (by omega)], Frame.refl _ _, rfl, rfl⟩
    · rw [dr₂, dr₁, g₁a _ hr.data, hD]; simp
    · rw [left₂, Nat.mul_zero, Nat.sub_zero, ← hn]; simp
    · rw [hsl _ (.inl rfl), mem₁, hi₁, Nat.mul_zero, Nat.add_zero]
    · rw [hsl _ (.inr rfl), mem₁, lo₁, Nat.mul_zero, Nat.add_zero]
  -- The exit.
  have hsv : ∀ i < 10, Core.savedRegs.getD i .x19 ≠ sb := by decide
  have hinj : ∀ i < 10, ∀ j < 10, Core.savedRegs.getD i .x19 = Core.savedRegs.getD j .x19 → i = j := by decide
  obtain ⟨s₅, e₅, v₅, -, m₅, rd₅, wr₅⟩ := loads_ok (B := B) c.slots (fun i => Core.savedRegs.getD i .x19) 10 s₄
    d₄.base hsv hinj (by omega) (fun i hi' => by
      rw [d₄.rd, d₄.wr, rd₂', wr₂']
      exact inRd (slot_wr hs.wr hN (by omega)))
  refine WP.of_runBlock ⟨s₅, e₅, fun i hi' => ?_, ?_, ?_, ?_, by rw [rd₅, d₄.rd, rd₂'], by rw [wr₅, d₄.wr, wr₂']⟩
  · rw [v₅ i hi', d₄.saved i hi', keep₂ _ (by omega) (by omega), mem₁, sv₁ i hi']
  · have subCore : ∀ x ∈ [coreRegion c B], Region.Sub x ⟨B, 8 * c.total⟩ := fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact Region.sub_prefix (by omega)
    have ht : (bytesAt s₀.mem P 16).length = 16 := by simp [bytesAt]
    rw [m₅, ctr_of_dinv (cs.cipher_len k) ht d₄.data,
      cbcBlocks_frame f₂ (fun x hx => sDS.sub_right (subCore x hx)),
      cbcBlocks_frame f₁' (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact sDS
        · exact sPD.symm)]
  · rw [m₅, bytesAt_frame d₄.frame (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact sPS
        · exact sPD) (by decide),
      bytesAt_frame f₂ (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact sPS.sub_right (Region.sub_prefix (by omega)))
        (by decide), mem₁, bP₁, AesCtr.next_eq (by simp [bytesAt]), hn]
  · rw [m₅]
    refine ((f₁'.sub fun x hx => ⟨x, by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> simp, fun _ h => h⟩).trans
      (f₂.sub fun x hx => ⟨⟨B, 8 * c.total⟩, List.mem_cons_self, by
        simp only [List.mem_singleton] at hx; subst hx; exact Region.sub_prefix (by omega)⟩)).trans ?_
    exact d₄.frame.sub fun x hx => ⟨x, by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> simp, fun _ h => h⟩

end VG.Proof.Modes.AArch64
