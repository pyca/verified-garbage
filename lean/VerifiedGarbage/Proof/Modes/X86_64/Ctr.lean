import VerifiedGarbage.Proof.Modes.X86_64.Group
import VerifiedGarbage.TCB.X86_64.Target

/-!
# CTR on x86-64, for any core: the whole function

`ctr_wp`: `c.ctr r`, for a core `c` with `CoreSpec c` and its arguments in
the registers `r`, transforms the `n` blocks at `D` by CTR with the
core's cipher under the key `k` that its key arguments give, from the
counter block at `P`, which it replaces with the one to continue from;
it keeps the callee-saved registers, and writes nothing but the scratch
buffer, the counter block and the data. Each cipher's contract follows
from it (with the constant-time check of its own code).
-/

namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Modes.X86_64
open VG.Impl.Aes.X86_64 (sb movR movS st)
open VG.Spec.Aes (bytesAt)

variable {c : Core}

theorem ctrLoop_wp (cs : CoreSpec c) {s₀ : State} {B D : Addr} {n : Nat} {k : cs.Key} {V : Nat}
    (hp : GPre c s₀ B D n) {s : State} (hi : GInv cs s₀ B D n k V 0 s) :
    WP isa (.loop c.ctrGroup .ne) s (GDone cs s₀ B D n k V) := by
  refine WP.loop (M := isa) (fun m s => ∃ g, m = n - c.G * g ∧ GInv cs s₀ B D n k V g s) (fun m s hs => ?_) n s
    ⟨0, by simp, hi⟩
  obtain ⟨g, rfl, hg⟩ := hs
  refine WP.mono (ctrGroup_wp cs hp hg) fun s' h => ?_
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨by simp [X86_64.eval, z], d⟩
  · have hG := cs.layout.G_pos
    exact .inr ⟨by simp [X86_64.eval, z], n - c.G * (g + 1),
      by have := d.lt; have := hg.lt; rw [Nat.mul_succ] at *; omega, g + 1, rfl, d⟩

/-- The blocks at `D` outside a frame. -/
theorem cbcBlocks_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {D : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨D, 16 * n⟩ r) : Spec.Cbc.blocksAt m' D n = Spec.Cbc.blocksAt m D n := by
  simp only [Spec.Cbc.blocksAt]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  exact bytesAt_frame hf (fun r hr => (hd r hr).sub_left (VG.Offset.sub_base D (by omega))) (by omega)

theorem keyRegs_ne {c : Core} (h : c.keyRegs.all (fun r => r != .rax && r != .rbx && r != sb) = true) :
    ∀ x ∈ c.keyRegs, x ≠ sb ∧ x ≠ .rax ∧ x ≠ .rbx := fun x hx => by
  have := List.all_eq_true.mp h x hx
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
  exact ⟨this.2, this.1.1, this.1.2⟩

/-- `CoreSpec.Ready`, `prepare`'s and the test's states, and the loop. -/
theorem ctr_wp (cs : CoreSpec c) {r : CtrRegs} (hr : RegsOk r) {s₀ : State} {B P D : Addr} {n : Nat}
    {k : cs.Key} (hB : s₀.gpr r.scr = B) (hP : s₀.gpr r.ctr = P) (hD : s₀.gpr r.data = D)
    (hn : (s₀.gpr r.n).toNat = n) (hs : ScrIn s₀ B c.ctrSlots) (hwP : (⟨P, 16⟩ : Region) ∈ s₀.wr)
    (hwD : (⟨D, 16 * n⟩ : Region) ∈ s₀.wr) (sPS : Region.Disjoint ⟨P, 16⟩ ⟨B, 8 * c.ctrSlots⟩)
    (sDS : Region.Disjoint ⟨D, 16 * n⟩ ⟨B, 8 * c.ctrSlots⟩) (sPD : Region.Disjoint ⟨P, 16⟩ ⟨D, 16 * n⟩)
    (fitD : D.toNat + 16 * n ≤ 2 ^ 64) (hk : cs.KeyArgs s₀ [⟨B, 8 * c.ctrSlots⟩, ⟨P, 16⟩] k) :
    WP isa (c.ctr r) s₀ fun s' => (∀ x ∈ calleeSaved, s'.gpr x = s₀.gpr x) ∧
      Spec.Cbc.blocksAt s'.mem D n =
        Spec.Ctr.crypt (cs.cipher k) (bytesAt s₀.mem P 16) (Spec.Cbc.blocksAt s₀.mem D n) ∧
      bytesAt s'.mem P 16 = Spec.Ctr.next (bytesAt s₀.mem P 16) n ∧
      Frame [⟨B, 8 * c.ctrSlots⟩, ⟨P, 16⟩, ⟨D, 16 * n⟩] s₀.mem s'.mem ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr := by
  have hL := cs.layout
  have hsm := hL.small
  have hN : 8 * c.ctrSlots < 2 ^ 64 := by simp only [Core.ctrSlots]; omega
  have hNs : c.slots ≤ c.ctrSlots := by simp only [Core.ctrSlots]; omega
  have b8 : ∀ j, j < c.ctrSlots → 8 * j < 2 ^ 64 := fun j hj => by omega
  -- The entry.
  obtain ⟨s₁, e₁, b₁, sv₁, dp₁, lf₁, hi₁, lo₁, bP₁, f₁, g₁, rd₁, wr₁⟩ := setup_ok hL hr s₀ hB hs hP hwP sPS
  unfold Core.ctr
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  have kr := keyRegs_ne cs.keyRegs_ok
  have subMode : Region.Sub (modeRegion c B) ⟨B, 8 * c.ctrSlots⟩ :=
    VG.Offset.sub_base B (by simp only [Core.ctrSlots]; omega)
  have f₁' : Frame [⟨B, 8 * c.ctrSlots⟩, ⟨P, 16⟩] s₀.mem s₁.mem := f₁.sub fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨_, List.mem_cons_self, subMode⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  have hk₁ : cs.KeyArgs s₁ [⟨B, 8 * c.ctrSlots⟩, ⟨P, 16⟩] k :=
    cs.keyArgs_congr hk (fun x hx => g₁ x (kr x hx).1 (kr x hx).2.1 (kr x hx).2.2) rd₁ wr₁ f₁'
  -- The key.
  refine WP.seq (WP.mono (cs.prepare_wp b₁ hNs ⟨by rw [wr₁]; exact hs.wr, hs.fit⟩ List.mem_cons_self hk₁)
    fun s₂ ⟨ready₂, b₂, rsp₂, f₂, rd₂, wr₂⟩ => ?_)
  have keep₂ : ∀ j, c.slots ≤ j → j < c.ctrSlots →
      s₂.mem.readW (wordAddr B j) 64 = s₁.mem.readW (wordAddr B j) 64 := fun j h1 h2 =>
    f₂.readW (Region.contains_self _ _) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx
      exact VG.Offset.disjoint_base B (by omega) (by omega)) (by decide)
  have wr₂' : s₂.wr = s₀.wr := by rw [wr₂, wr₁]
  have rd₂' : s₂.rd = s₀.rd := by rw [rd₂, rd₁]
  -- Any blocks?
  have hlS : c.leftSlot < c.ctrSlots := by simp only [Core.leftSlot, Core.ctrSlots]; omega
  obtain ⟨s₃a, e₃a, r₃a, o₃a, m₃a, rd₃a, wr₃a⟩ := movS_ok (s := s₂) (b := B) (k := c.leftSlot) .rcx b₂
    (by rw [rd₂', wr₂']; exact inRd (slot_wr hs.wr hN hlS))
  obtain ⟨s₃, e₃, z₃, g₃, m₃, rd₃, wr₃⟩ := testSelf_ok s₃a .rcx
  refine WP.seq (WP.of_runBlock ⟨s₃, by
    rw [show ([movS .rcx c.leftSlot, .alu .test .rcx (.reg .rcx)] : List Instr) =
      [movS .rcx c.leftSlot] ++ [.alu .test .rcx (.reg .rcx)] from rfl, runBlock_app, e₃a, Option.bind_some, e₃],
    ?_⟩)
  have left₃ : s₃.gpr .rcx = s₀.gpr r.n := by
    rw [g₃, r₃a, keep₂ _ (by simp only [Core.leftSlot]; omega) hlS, lf₁]
  have hz₃ : s₃.zf = some (decide (n = 0)) := by
    rw [z₃, ← g₃, left₃]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by rw [← hn, h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [hn, h]; rfl)⟩
  have mem₃ : s₃.mem = s₂.mem := by rw [m₃, m₃a]
  have b₃ : s₃.gpr sb = B := by rw [g₃, o₃a _ (by decide), b₂]
  have rsp₃ : s₃.gpr .rsp = s₀.gpr .rsp := by
    rw [g₃, o₃a _ (by decide), rsp₂, g₁ _ (by decide) (by decide) (by decide)]
  have rd₃' : s₃.rd = s₀.rd := by rw [rd₃, rd₃a, rd₂']
  have wr₃' : s₃.wr = s₀.wr := by rw [wr₃, wr₃a, wr₂']
  let V := ctrVal s₀.mem P
  have hp : GPre c s₃ B D n := ⟨⟨by rw [wr₃']; exact hs.wr, hs.fit⟩, by rw [wr₃']; exact hwD, sDS, fitD⟩
  -- The groups.
  refine WP.seq (WP.mono (M := isa) (Q := GDone cs s₃ B D n k V)
    (WP.ite (decide (n = 0)) (by simp [X86_64.eval, hz₃]) (fun h0 => ?_) (fun h0 => ?_)) fun s₄ d₄ => ?_)
  · have hn0 : n = 0 := by simpa using h0
    exact WP.block_nil ⟨b₃, rfl, fun _ _ => rfl, fun i hi' => by omega, Frame.refl _ _, rfl, rfl⟩
  · have hn0 : n ≠ 0 := by simpa using h0
    have hsl : ∀ j, j = c.dataSlot ∨ j = c.leftSlot ∨ j = c.hiSlot ∨ j = c.loSlot →
        s₃.mem.readW (wordAddr B j) 64 = s₁.mem.readW (wordAddr B j) 64 := fun j hj => by
      rw [mem₃]
      exact keep₂ j (by rcases hj with rfl | rfl | rfl | rfl <;>
          simp only [Core.dataSlot, Core.leftSlot, Core.hiSlot, Core.loSlot] <;> omega)
        (by rcases hj with rfl | rfl | rfl | rfl <;>
          simp only [Core.dataSlot, Core.leftSlot, Core.hiSlot, Core.loSlot, Core.ctrSlots] <;> omega)
    refine ctrLoop_wp cs hp ⟨b₃, rfl, by rw [mem₃]; exact ready₂, fun _ _ => rfl, ?_, ?_, by omega, ?_, ?_,
      fun i _ => by rw [ite_eq_right (by omega)], Frame.refl _ _, rfl, rfl⟩
    · rw [hsl _ (.inl rfl), dp₁, hD]; simp
    · rw [hsl _ (.inr (.inl rfl)), lf₁, Nat.mul_zero, Nat.sub_zero, ← hn]; simp
    · rw [hsl _ (.inr (.inr (.inl rfl))), hi₁, Nat.mul_zero, Nat.add_zero]
    · rw [hsl _ (.inr (.inr (.inr rfl))), lo₁, Nat.mul_zero, Nat.add_zero]
  -- The exit.
  have hsv : ∀ i < 6, Core.savedRegs.getD i .rbx ≠ sb := by decide
  have hinj : ∀ i < 6, ∀ j < 6, Core.savedRegs.getD i .rbx = Core.savedRegs.getD j .rbx → i = j := by decide
  obtain ⟨s₅, e₅, v₅, o₅, m₅, rd₅, wr₅⟩ := loads_ok (B := B) c.slots (fun i => Core.savedRegs.getD i .rbx) 6 s₄
    d₄.base hsv hinj (fun i hi' => by
      rw [d₄.rd, d₄.wr, rd₃', wr₃']
      exact inRd (slot_wr hs.wr hN (by simp only [Core.ctrSlots]; omega)))
  refine WP.of_runBlock ⟨s₅, e₅, fun x hx => ?_, ?_, ?_, ?_, by rw [rd₅, d₄.rd, rd₃'], by rw [wr₅, d₄.wr, wr₃']⟩
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
      simp only [List.mem_singleton] at hx; subst hx; exact Region.sub_prefix (by omega)
    have ht : (bytesAt s₀.mem P 16).length = 16 := by simp [bytesAt]
    rw [m₅, ctr_of_dinv (cs.cipher_len k) ht d₄.data, mem₃,
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
        · exact sPD) (by decide), mem₃,
      bytesAt_frame f₂ (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact sPS.sub_right (Region.sub_prefix (by omega)))
        (by decide), bP₁, AesCtr.next_eq (by simp [bytesAt]), hn]
  · rw [m₅]
    refine ((f₁'.sub fun x hx => ⟨x, by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> simp, fun _ h => h⟩).trans
      (f₂.sub fun x hx => ⟨⟨B, 8 * c.ctrSlots⟩, List.mem_cons_self, by
        simp only [List.mem_singleton] at hx; subst hx; exact Region.sub_prefix (by omega)⟩)).trans ?_
    rw [← mem₃]
    exact d₄.frame.sub fun x hx => ⟨x, by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> simp, fun _ h => h⟩

end VG.Proof.Modes.X86_64
