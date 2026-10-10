import VerifiedGarbage.Proof.Modes.AArch64.Words
import VerifiedGarbage.Proof.Modes.AArch64.Xor
import VerifiedGarbage.Impl.Modes.AArch64.Cbc

/-!
# Loops over blocks on AArch64

As on x86-64 (`Proof/Modes/X86_64/Copy.lean`). `blockLoop_wp`: a loop whose
body works on the block at `x14` and `x15` and then steps both by a block
(`nextBlock`) and counts `x17` down, from an invariant `J` of everything
but those three registers. `copyBlocks_wp`: `copyBlocks` copies `n ≥ 1`
blocks at `x15` to `x14` (areas that do not overlap) and changes nothing
else in memory.
-/

namespace VG.Proof.Modes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Modes.AArch64

variable {c : Core}

theorem nextBlock_ok (s : State) (hL : 8 * c.bw < 4096) :
    ∃ s', runBlock isa c.nextBlock s = some s' ∧ s'.gpr .x14 = s.gpr .x14 + BitVec.ofNat 64 (8 * c.bw) ∧
      s'.gpr .x15 = s.gpr .x15 + BitVec.ofNat 64 (8 * c.bw) ∧ s'.gpr .x17 = s.gpr .x17 - BitVec.ofNat 64 1 ∧
      (∀ r, r ≠ .x14 → r ≠ .x15 → r ≠ .x17 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, a₁, o₁, m₁, rd₁, wr₁⟩ := addImm_ok s .x14 .x14 hL
  obtain ⟨s₂, e₂, a₂, o₂, m₂, rd₂, wr₂⟩ := addImm_ok s₁ .x15 .x15 hL
  obtain ⟨s₃, e₃, c₃, o₃, m₃, rd₃, wr₃⟩ := subImm_ok s₂ .x17 .x17 (v := 1) (by decide)
  refine ⟨s₃, ?_, by rw [o₃ _ (by decide), o₂ _ (by decide), a₁],
    by rw [o₃ _ (by decide), a₂, o₁ _ (by decide)], by rw [c₃, o₂ _ (by decide), o₁ _ (by decide)],
    fun r h1 h2 h3 => by rw [o₃ r h3, o₂ r h2, o₁ r h1], by rw [m₃, m₂, m₁], by rw [rd₃, rd₂, rd₁],
    by rw [wr₃, wr₂, wr₁]⟩
  rw [Core.nextBlock, show ([.addImm .x .x14 .x14 (8 * c.bw), .addImm .x .x15 .x15 (8 * c.bw),
      .subImm .x .x17 .x17 1] : List Instr) =
      [.addImm .x .x14 .x14 (8 * c.bw)] ++ ([.addImm .x .x15 .x15 (8 * c.bw)] ++ [.subImm .x .x17 .x17 1]) from rfl,
    runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, e₃]

/-- The loop over `n` blocks at `T` (in `x14`) and `A` (in `x15`), counting
down `x17`: `J j` holds before block `j` whatever `x14`, `x15` and `x17`
hold, and the body of block `j` keeps those three and makes `J (j + 1)`. -/
theorem blockLoop_wp (body : List Instr) {T A : Addr} {n : Nat} (J : Nat → State → Prop)
    (hL : 8 * c.bw < 4096) (hn : 0 < n) (hn64 : n < 2 ^ 64)
    (hJ : ∀ j s s', J j s → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r, r ≠ .x14 → r ≠ .x15 → r ≠ .x17 → s'.gpr r = s.gpr r) → J j s')
    (hb : ∀ j < n, ∀ s, J j s → s.gpr .x14 = T + BitVec.ofNat 64 (8 * c.bw * j) →
      s.gpr .x15 = A + BitVec.ofNat 64 (8 * c.bw * j) →
      WP isa (.block body) s fun s' => J (j + 1) s' ∧ s'.gpr .x14 = s.gpr .x14 ∧ s'.gpr .x15 = s.gpr .x15 ∧
        s'.gpr .x17 = s.gpr .x17)
    {s₀ : State} (h0 : J 0 s₀) (ha : s₀.gpr .x14 = T) (hb' : s₀.gpr .x15 = A)
    (hc : s₀.gpr .x17 = BitVec.ofNat 64 n) :
    WP isa (.loop (.block (body ++ c.nextBlock)) (.nonzero .x .x17)) s₀ fun s => J n s ∧
      s.gpr .x14 = T + BitVec.ofNat 64 (8 * c.bw * n) ∧ s.gpr .x15 = A + BitVec.ofNat 64 (8 * c.bw * n) := by
  refine WP.loop (M := isa) (fun m s => ∃ j, m = n - j ∧ j < n ∧ J j s ∧
      s.gpr .x14 = T + BitVec.ofNat 64 (8 * c.bw * j) ∧ s.gpr .x15 = A + BitVec.ofNat 64 (8 * c.bw * j) ∧
      s.gpr .x17 = BitVec.ofNat 64 (n - j))
    (fun m s hs => ?_) n s₀ ⟨0, by omega, hn, h0, by rw [ha]; simp, by rw [hb']; simp, by rw [hc, Nat.sub_zero]⟩
  obtain ⟨j, rfl, hj, hJj, hax, hbx, hcx⟩ := hs
  rw [WP.block_append_iff]
  refine WP.mono (hb j hj s hJj hax hbx) fun s₁ ⟨hJ₁, a₁, b₁, c₁⟩ => ?_
  obtain ⟨s₂, e₂, a₂, b₂, c₂, o₂, m₂, rd₂, wr₂⟩ := nextBlock_ok (c := c) s₁ hL
  have hJ₂ : J (j + 1) s₂ := hJ _ _ _ hJ₁ m₂ rd₂ wr₂ o₂
  have ec : s₂.gpr .x17 = BitVec.ofNat 64 (n - (j + 1)) := by
    rw [c₂, c₁, hcx, VG.Offset.ofNat_sub_ofNat (by omega), show n - j - 1 = n - (j + 1) by omega]
  have hz : isa.eval (.nonzero .x .x17) s₂ = some !(decide (n - (j + 1) = 0)) := by
    rw [eval_nonzero, ec, ofNat_beq_zero (by omega)]
  have hstep : ∀ (X : Addr), X + BitVec.ofNat 64 (8 * c.bw * j) + BitVec.ofNat 64 (8 * c.bw) =
      X + BitVec.ofNat 64 (8 * c.bw * (j + 1)) := fun X => by rw [addr_add, Nat.mul_succ]
  refine WP.of_runBlock ⟨s₂, e₂, ?_⟩
  by_cases hl : j + 1 = n
  · refine .inl ⟨by rw [hz, decide_eq_true (by omega)]; rfl, by rw [← hl]; exact hJ₂,
      by rw [a₂, a₁, hax, hstep, hl], by rw [b₂, b₁, hbx, hstep, hl]⟩
  · exact .inr ⟨by rw [hz, decide_eq_false (by omega)]; rfl, n - (j + 1), by omega, j + 1, rfl, by omega, hJ₂,
      by rw [a₂, a₁, hax, hstep], by rw [b₂, b₁, hbx, hstep], ec⟩

/-- Copying, after `j` of `n` blocks of `bw` words from `S` to `T`. -/
structure CopyInv (c : Core) (S T : Addr) (n : Nat) (s₀ : State) (j : Nat) (s : State) : Prop where
  copied : ∀ t < 8 * c.bw * j, s.mem (T + BitVec.ofNat 64 t) = s₀.mem (S + BitVec.ofNat 64 t)
  frame : Frame [⟨T, 8 * c.bw * n⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ .x8 → r ≠ .x14 → r ≠ .x15 → r ≠ .x17 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem copyBlocks_wp {S T : Addr} {n : Nat} {s₀ : State} (hbw : 0 < c.bw) (hbw2 : c.bw ≤ 2) (hn : 0 < n)
    (hfit : 8 * c.bw * n < 2 ^ 63)
    (hS : ∀ t < c.bw * n, InRegions (s₀.rd ++ s₀.wr) (S + BitVec.ofNat 64 (8 * t)) 8)
    (hT : ∀ t < c.bw * n, InRegions s₀.wr (T + BitVec.ofNat 64 (8 * t)) 8)
    (hsep : Region.Disjoint ⟨S, 8 * c.bw * n⟩ ⟨T, 8 * c.bw * n⟩) (ha : s₀.gpr .x14 = T) (hb : s₀.gpr .x15 = S)
    (hc : s₀.gpr .x17 = BitVec.ofNat 64 n) :
    WP isa c.copyBlocks s₀ fun s => CopyInv c S T n s₀ n s ∧ s.gpr .x15 = S + BitVec.ofNat 64 (8 * c.bw * n) := by
  have hn64 : n ≤ 8 * c.bw * n := Nat.le_mul_of_pos_left n (by omega)
  unfold Core.copyBlocks
  refine WP.mono (blockLoop_wp (c := c) _ (CopyInv c S T n s₀) (by omega) hn (by omega)
    (fun j s s' h hm hrd hwr hg => ⟨fun t ht => by rw [hm]; exact h.copied t ht, by rw [hm]; exact h.frame,
      fun r h1 h2 h3 h4 => by rw [hg r h2 h3 h4, h.regs r h1 h2 h3 h4], by rw [hrd, h.rd], by rw [hwr, h.wr]⟩)
    (fun j hj s hi hax hbx => ?_) ⟨fun t ht => by omega, Frame.refl _ _, fun _ _ _ _ _ => rfl, rfl, rfl⟩ ha hb hc)
    fun _ h => ⟨h.1, h.2.2⟩
  have hlt := idx_lt (L := 8 * c.bw) hj
  have hw : ∀ w, 8 * c.bw * j + 8 * w = 8 * (c.bw * j + w) := fun w => by rw [Nat.mul_add, Nat.mul_assoc]
  have hbj : ∀ w < c.bw, c.bw * j + w < c.bw * n := fun w hw' => by have := idx_lt (L := c.bw) hj; omega
  have hSs : ∀ t < 8 * c.bw * n, s.mem (S + BitVec.ofNat 64 t) = s₀.mem (S + BitVec.ofNat 64 t) := fun t ht =>
    hi.frame.bytes (R := ⟨S, 8 * c.bw * n⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsep)
      (by simp only; omega) ht
  have hPT : Region.Sub ⟨T + BitVec.ofNat 64 (8 * c.bw * j), 8 * c.bw⟩ ⟨T, 8 * c.bw * n⟩ :=
    VG.Offset.sub_base T (by omega)
  refine WP.mono (copyN_wp (k := c.bw) (P := T + BitVec.ofNat 64 (8 * c.bw * j)) (u := .x8)
    (Q := S + BitVec.ofNat 64 (8 * c.bw * j)) ⟨by rw [hax]; simp, by rw [hbx]; simp,
    by decide, by decide, by decide, by decide, by decide, by decide, by omega, by omega,
    fun w hw' => by rw [hi.wr, addr_add, hw w]; exact hT _ (hbj w hw'),
    fun w hw' => by rw [hi.rd, hi.wr, addr_add, hw w]; exact hS _ (hbj w hw'),
    (hsep.symm.sub_left hPT).sub_right (VG.Offset.sub_base S (by omega)), by omega⟩) fun s' h' => ?_
  refine ⟨⟨fun t ht => ?_, hi.frame.trans fun x hx => ?_, fun r h1 h2 h3 h4 => by
      rw [h'.regs r h1 h1, hi.regs r h1 h2 h3 h4], by rw [h'.rd, hi.rd], by rw [h'.wr, hi.wr]⟩,
    h'.regs _ (by decide) (by decide), h'.regs _ (by decide) (by decide), h'.regs _ (by decide) (by decide)⟩
  · have : 8 * c.bw * (j + 1) = 8 * c.bw * j + 8 * c.bw := Nat.mul_succ _ _
    rw [h'.mem]
    by_cases h1 : 8 * c.bw * j ≤ t
    · rw [show T + BitVec.ofNat 64 t = T + BitVec.ofNat 64 (8 * c.bw * j) + BitVec.ofNat 64 (t - 8 * c.bw * j) by
        rw [addr_add, show 8 * c.bw * j + (t - 8 * c.bw * j) = t by omega], over_at (by omega) (by omega), addr_add,
        show 8 * c.bw * j + (t - 8 * c.bw * j) = t by omega, hSs t (by omega)]
    · rw [over_out (off_sub_not T (by omega) (by omega) (by omega) (by omega))]
      exact hi.copied t (by omega)
  · rw [h'.mem]
    exact over_out fun h => hx _ (List.mem_singleton_self _) (hPT x (by simp only [Region.Contains]; omega))

end VG.Proof.Modes.AArch64
