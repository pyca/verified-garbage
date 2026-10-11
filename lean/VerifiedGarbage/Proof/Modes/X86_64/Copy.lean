import VerifiedGarbage.Proof.Modes.X86_64.Words
import VerifiedGarbage.Impl.Modes.X86_64.Cbc

/-!
# Loops over blocks on x86-64

`blockLoop_wp`: a loop whose body works on the block at `rax` and `rbx` and
then steps both by a block (`nextBlock`) and counts `rcx` down, from an
invariant `J` of everything but those three registers. `copyBlocks_wp`:
`copyBlocks` copies `n ≥ 1` blocks at `rbx` to `rax` (areas that do not
overlap) and changes nothing else in memory.
-/

namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Modes.X86_64

variable {c : Core}

theorem nextBlock_ok (s : State) (hL : 8 * c.bw < 2 ^ 31) :
    ∃ s', runBlock isa c.nextBlock s = some s' ∧ s'.gpr .rax = s.gpr .rax + BitVec.ofNat 64 (8 * c.bw) ∧
      s'.gpr .rbx = s.gpr .rbx + BitVec.ofNat 64 (8 * c.bw) ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) ∧ (∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, a₁, o₁, m₁, rd₁, wr₁⟩ := addImm_ok s .rax (BitVec.ofNat 32 (8 * c.bw))
  obtain ⟨s₂, e₂, a₂, o₂, m₂, rd₂, wr₂⟩ := addImm_ok s₁ .rbx (BitVec.ofNat 32 (8 * c.bw))
  obtain ⟨s₃, e₃, c₃, z₃, o₃, m₃, rd₃, wr₃⟩ := subImm_ok s₂ .rcx 1
  have hc : s₂.gpr .rcx = s.gpr .rcx := by rw [o₂ _ (by decide), o₁ _ (by decide)]
  refine ⟨s₃, ?_, by rw [o₃ _ (by decide), o₂ _ (by decide), a₁, signExtend_small hL],
    by rw [o₃ _ (by decide), a₂, o₁ _ (by decide), signExtend_small hL], by rw [c₃, hc]; rfl, by rw [z₃, hc]; rfl,
    fun r h1 h2 h3 => by rw [o₃ r h3, o₂ r h2, o₁ r h1], by rw [m₃, m₂, m₁], by rw [rd₃, rd₂, rd₁],
    by rw [wr₃, wr₂, wr₁]⟩
  rw [Core.nextBlock, show ([.alu .add .rax (.imm (BitVec.ofNat 32 (8 * c.bw))),
      .alu .add .rbx (.imm (BitVec.ofNat 32 (8 * c.bw))), .alu .sub .rcx (.imm 1)] : List Instr) =
      [.alu .add .rax (.imm (BitVec.ofNat 32 (8 * c.bw)))] ++ ([.alu .add .rbx (.imm (BitVec.ofNat 32 (8 * c.bw)))] ++
      [.alu .sub .rcx (.imm 1)]) from rfl, runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, e₃]

/-- The loop over `n` blocks at `T` (in `rax`) and `A` (in `rbx`), counting
down `rcx`: `J j` holds before block `j` whatever `rax`, `rbx` and `rcx`
hold, and the body of block `j` keeps those three and makes `J (j + 1)`. -/
theorem blockLoop_wp (body : List Instr) {T A : Addr} {n : Nat} (J : Nat → State → Prop)
    (hL : 8 * c.bw < 2 ^ 31) (hn : 0 < n) (hn64 : n < 2 ^ 64)
    (hJ : ∀ j s s', J j s → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → s'.gpr r = s.gpr r) → J j s')
    (hb : ∀ j < n, ∀ s, J j s → s.gpr .rax = T + BitVec.ofNat 64 (8 * c.bw * j) →
      s.gpr .rbx = A + BitVec.ofNat 64 (8 * c.bw * j) →
      WP isa (.block body) s fun s' => J (j + 1) s' ∧ s'.gpr .rax = s.gpr .rax ∧ s'.gpr .rbx = s.gpr .rbx ∧
        s'.gpr .rcx = s.gpr .rcx)
    {s₀ : State} (h0 : J 0 s₀) (ha : s₀.gpr .rax = T) (hb' : s₀.gpr .rbx = A)
    (hc : s₀.gpr .rcx = BitVec.ofNat 64 n) :
    WP isa (.loop (.block (body ++ c.nextBlock)) .ne) s₀ fun s => J n s ∧
      s.gpr .rax = T + BitVec.ofNat 64 (8 * c.bw * n) ∧ s.gpr .rbx = A + BitVec.ofNat 64 (8 * c.bw * n) := by
  refine WP.loop (M := isa) (fun m s => ∃ j, m = n - j ∧ j < n ∧ J j s ∧
      s.gpr .rax = T + BitVec.ofNat 64 (8 * c.bw * j) ∧ s.gpr .rbx = A + BitVec.ofNat 64 (8 * c.bw * j) ∧
      s.gpr .rcx = BitVec.ofNat 64 (n - j))
    (fun m s hs => ?_) n s₀ ⟨0, by omega, hn, h0, by rw [ha]; simp, by rw [hb']; simp, by rw [hc, Nat.sub_zero]⟩
  obtain ⟨j, rfl, hj, hJj, hax, hbx, hcx⟩ := hs
  rw [WP.block_append_iff]
  refine WP.mono (hb j hj s hJj hax hbx) fun s₁ ⟨hJ₁, a₁, b₁, c₁⟩ => ?_
  obtain ⟨s₂, e₂, a₂, b₂, c₂, z₂, o₂, m₂, rd₂, wr₂⟩ := nextBlock_ok (c := c) s₁ hL
  have hJ₂ : J (j + 1) s₂ := hJ _ _ _ hJ₁ m₂ rd₂ wr₂ o₂
  have ec : s₁.gpr .rcx - 1 = BitVec.ofNat 64 (n - (j + 1)) := by
    rw [c₁, hcx, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, VG.Offset.ofNat_sub_ofNat (by omega),
      show n - j - 1 = n - (j + 1) by omega]
  have hz : s₂.zf = some (decide (n - j = 1)) := by
    rw [z₂, c₁, hcx, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      VG.Offset.ofNat_sub_ofNat_beq (by omega) (by decide)]
  have hstep : ∀ (X : Addr), X + BitVec.ofNat 64 (8 * c.bw * j) + BitVec.ofNat 64 (8 * c.bw) =
      X + BitVec.ofNat 64 (8 * c.bw * (j + 1)) := fun X => by rw [addr_add, Nat.mul_succ]
  refine WP.of_runBlock ⟨s₂, e₂, ?_⟩
  by_cases hl : j + 1 = n
  · refine .inl ⟨by simp [X86_64.eval, hz]; omega, by rw [← hl]; exact hJ₂, by rw [a₂, a₁, hax, hstep, hl],
      by rw [b₂, b₁, hbx, hstep, hl]⟩
  · exact .inr ⟨by simp [X86_64.eval, hz]; omega, n - (j + 1), by omega, j + 1, rfl, by omega, hJ₂,
      by rw [a₂, a₁, hax, hstep], by rw [b₂, b₁, hbx, hstep], by rw [c₂, ec]⟩

/-- Copying, after `j` of `n` blocks of `bw` words from `S` to `T`. -/
structure CopyInv (c : Core) (S T : Addr) (n : Nat) (s₀ : State) (j : Nat) (s : State) : Prop where
  copied : ∀ t < 8 * c.bw * j, s.mem (T + BitVec.ofNat 64 t) = s₀.mem (S + BitVec.ofNat 64 t)
  frame : Frame [⟨T, 8 * c.bw * n⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .rbp → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem copyBlocks_wp {S T : Addr} {n : Nat} {s₀ : State} (hbw : 0 < c.bw) (hL : 8 * c.bw < 2 ^ 31) (hn : 0 < n)
    (hfit : 8 * c.bw * n < 2 ^ 63)
    (hS : ∀ t < c.bw * n, InRegions (s₀.rd ++ s₀.wr) (S + BitVec.ofNat 64 (8 * t)) 8)
    (hT : ∀ t < c.bw * n, InRegions s₀.wr (T + BitVec.ofNat 64 (8 * t)) 8)
    (hsep : Region.Disjoint ⟨S, 8 * c.bw * n⟩ ⟨T, 8 * c.bw * n⟩) (ha : s₀.gpr .rax = T) (hb : s₀.gpr .rbx = S)
    (hc : s₀.gpr .rcx = BitVec.ofNat 64 n) :
    WP isa c.copyBlocks s₀ (CopyInv c S T n s₀ n) := by
  have hn64 : n ≤ 8 * c.bw * n := Nat.le_mul_of_pos_left n (by omega)
  refine WP.mono (blockLoop_wp (c := c) _ (CopyInv c S T n s₀) hL hn (by omega)
    (fun j s s' h hm hrd hwr hg => ⟨fun t ht => by rw [hm]; exact h.copied t ht, by rw [hm]; exact h.frame,
      fun r h1 h2 h3 h4 => by rw [hg r h1 h2 h3, h.regs r h1 h2 h3 h4], by rw [hrd, h.rd], by rw [hwr, h.wr]⟩)
    (fun j hj s hi hax hbx => ?_) ⟨fun t ht => by omega, Frame.refl _ _, fun _ _ _ _ _ => rfl, rfl, rfl⟩ ha hb hc)
    fun _ h => h.1
  have hlt := idx_lt (L := 8 * c.bw) hj
  have hw : ∀ w, 8 * c.bw * j + 8 * w = 8 * (c.bw * j + w) := fun w => by rw [Nat.mul_add, Nat.mul_assoc]
  have hbj : ∀ w < c.bw, c.bw * j + w < c.bw * n := fun w hw' => by have := idx_lt (L := c.bw) hj; omega
  have hSs : ∀ t < 8 * c.bw * n, s.mem (S + BitVec.ofNat 64 t) = s₀.mem (S + BitVec.ofNat 64 t) := fun t ht =>
    hi.frame.bytes (R := ⟨S, 8 * c.bw * n⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsep)
      (by simp only; omega) ht
  have hPT : Region.Sub ⟨T + BitVec.ofNat 64 (8 * c.bw * j), 8 * c.bw⟩ ⟨T, 8 * c.bw * n⟩ :=
    VG.Offset.sub_base T (by omega)
  refine WP.mono (copyN_wp (k := c.bw) (P := T + BitVec.ofNat 64 (8 * c.bw * j))
    (Q := S + BitVec.ofNat 64 (8 * c.bw * j)) ⟨by rw [hax]; simp, by rw [hbx]; simp,
    by decide, by decide, fun w hw' => by rw [hi.wr, addr_add, hw w]; exact hT _ (hbj w hw'),
    fun w hw' => by rw [hi.rd, hi.wr, addr_add, hw w]; exact hS _ (hbj w hw'),
    (hsep.symm.sub_left hPT).sub_right (VG.Offset.sub_base S (by omega)), by omega⟩) fun s' h' => ?_
  have hm : ∀ t < 8 * c.bw * n, s'.mem (T + BitVec.ofNat 64 t) =
      if 8 * c.bw * j ≤ t ∧ t < 8 * c.bw * j + 8 * c.bw then s.mem (S + BitVec.ofNat 64 t)
      else s.mem (T + BitVec.ofNat 64 t) := fun t ht => by
    rw [h'.mem]
    split
    · rename_i h1
      rw [show T + BitVec.ofNat 64 t = T + BitVec.ofNat 64 (8 * c.bw * j) + BitVec.ofNat 64 (t - 8 * c.bw * j) by
        rw [addr_add, show 8 * c.bw * j + (t - 8 * c.bw * j) = t by omega], over_at (by omega) (by omega), addr_add,
        show 8 * c.bw * j + (t - 8 * c.bw * j) = t by omega]
    · exact over_out (off_sub_not T (by omega) (by omega) (by omega) (by omega))
  refine ⟨⟨fun t ht => ?_, hi.frame.trans fun x hx => ?_, fun r h1 h2 h3 h4 => by rw [h'.regs r h4, hi.regs r h1 h2 h3 h4],
    by rw [h'.rd, hi.rd], by rw [h'.wr, hi.wr]⟩, h'.regs _ (by decide), h'.regs _ (by decide), h'.regs _ (by decide)⟩
  · have : 8 * c.bw * (j + 1) = 8 * c.bw * j + 8 * c.bw := Nat.mul_succ _ _
    rw [hm t (by omega)]
    split
    · rw [hSs t (by omega)]
    · exact hi.copied t (by omega)
  · rw [h'.mem]
    exact over_out fun h => hx _ (List.mem_singleton_self _) (hPT x (by simp only [Region.Contains]; omega))

end VG.Proof.Modes.X86_64
