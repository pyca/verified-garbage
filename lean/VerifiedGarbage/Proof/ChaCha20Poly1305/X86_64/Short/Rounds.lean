module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Loop
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2Tail.Two
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2Tail.RoundsVL
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.RoundsVL

/-!
# ChaCha20-Poly1305 for short records (x86-64): the rounds as loops

`Stitch.rounds10 r` runs `r` ten times, counted in `rax` (`rounds10_ok`, from
`cntLoopR_ok`), for an invariant that writes of `rax` and the flags keep.
For one or two sets of `Avx2Tail`'s code that is `RoundsOk`
(`rounds10S_roundsOk`), as for the unrolled rounds, and for three sets
`rounds10S3_ok`.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.X86_64.Short

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Proof.ChaCha20Poly1305.X86_64.Stitch (cntLoopR_ok mov32Imm_ok)
open VG.Proof.ChaCha20.X86_64.Avx2Tail (HB YM YM3 RoundsOk roundsS_ok roundsS3_ok)
open VG.Proof.ChaCha20 (CState)
open VG.Spec.ChaCha20 (innerBlock)

/-- `rounds10 r`: ten runs of `r`, each advancing `I` and keeping `rax`, which
counts them. -/
theorem rounds10_ok {r : Prog isa} (I : Nat → State → Prop)
    (hstep : ∀ i, i < 10 → ∀ s, I i s → WP isa r s fun s' => I (i + 1) s' ∧ s'.gpr .rax = s.gpr .rax)
    (hkeep : ∀ i s s', I i s → (∀ q, q ≠ .rax → s'.gpr q = s.gpr q) → s'.xmm = s.xmm →
      s'.ymmHi = s.ymmHi → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → I i s')
    {s : State} (h0 : I 0 s) : WP isa (rounds10 r) s fun s' => I 10 s' ∧ s'.gpr .rax = 0 := by
  unfold rounds10
  refine WP.seq (WP.mono (mov32Imm_ok .rax 10 s) fun s₁ ⟨d₁, g₁, x₁, y₁, m₁, rd₁, wr₁⟩ => ?_)
  exact cntLoopR_ok .rax I (by decide) (by decide)
    (fun i hi t ht => WP.seq (WP.mono (hstep i hi t ht) fun _ h' => WP.block_nil h')) hkeep
    (hkeep 0 s s₁ h0 g₁ x₁ y₁ m₁ rd₁ wr₁) (by rw [d₁]; rfl)

/-- The rounds' invariant: the sets after `n` double rounds, the masks, and
nothing else written but `rax`. -/
def TR (S : Nat) (vs : Nat → CState) (s₀ : State) (n : Nat) (s : State) : Prop :=
  HB S (fun j => Nat.repeat innerBlock n (vs j)) s ∧ YM s ∧ (∀ q, q ≠ .rax → s.gpr q = s₀.gpr q) ∧
    s.mem = s₀.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr

/-- One or two sets' ten double rounds, as a loop. -/
theorem rounds10S_roundsOk (vl : Bool) {S : Nat} (hS : S = 1 ∨ S = 2) :
    RoundsOk S (rounds10 (Impl.ChaCha20.X86_64.Avx2Tail.roundsS vl S 1)) := by
  intro vs s₀ h hm
  refine WP.mono (rounds10_ok (TR S vs s₀) (fun i _ t ⟨ht, hy, hg, hm', hrd, hwr⟩ => ?_)
    (fun i t t' ⟨ht, hy, hg, hm', hrd, hwr⟩ g x y m rd wr => ⟨?_, ?_, fun q hq => by rw [g q hq, hg q hq],
      by rw [m, hm'], by rw [rd, hrd], by rw [wr, hwr]⟩)
    ⟨h, hm, fun _ _ => rfl, rfl, rfl, rfl⟩) fun s ⟨⟨h', hy', hg', hm', hrd', hwr'⟩, _⟩ =>
    ⟨h', hy', hg', hm', hrd', hwr'⟩
  · exact WP.mono (roundsS_ok vl hS ht hy 1) fun t' ⟨h₁, hy₁, f₁⟩ =>
      ⟨⟨h₁, hy₁, fun q hq => by rw [f₁.gpr, hg q hq], by rw [f₁.mem, hm'], by rw [f₁.rd, hrd],
        by rw [f₁.wr, hwr]⟩, by rw [f₁.gpr]⟩
  · intro k hk l hl i hi
    simp only [State.lane, x, y]; exact ht k hk l hl i hi
  · intro l; simp only [State.lane, x, y]; exact hy l

/-- As `TR`, with the masks of three sets. -/
def TR3 (vs : Nat → CState) (s₀ : State) (n : Nat) (s : State) : Prop :=
  HB 3 (fun j => Nat.repeat innerBlock n (vs j)) s ∧ YM3 s ∧ (∀ q, q ≠ .rax → s.gpr q = s₀.gpr q) ∧
    s.mem = s₀.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr

/-- Three sets' ten double rounds, as a loop. -/
theorem rounds10S3_ok (vl : Bool) {vs : Nat → CState} {s₀ : State} (h : HB 3 vs s₀) (hm : YM3 s₀) :
    WP isa (rounds10 (Impl.ChaCha20.X86_64.Avx2Tail.roundsS vl 3 1)) s₀ fun s => TR3 vs s₀ 10 s := by
  refine WP.mono (rounds10_ok (TR3 vs s₀) (fun i _ t ⟨ht, hy, hg, hm', hrd, hwr⟩ => ?_)
    (fun i t t' ⟨ht, hy, hg, hm', hrd, hwr⟩ g x y m rd wr => ⟨?_, ?_, fun q hq => by rw [g q hq, hg q hq],
      by rw [m, hm'], by rw [rd, hrd], by rw [wr, hwr]⟩)
    ⟨h, hm, fun _ _ => rfl, rfl, rfl, rfl⟩) fun s ⟨h', _⟩ => h'
  · exact WP.mono (roundsS3_ok vl ht hy 1) fun t' ⟨h₁, hy₁, f₁⟩ =>
      ⟨⟨h₁, hy₁, fun q hq => by rw [f₁.gpr, hg q hq], by rw [f₁.mem, hm'], by rw [f₁.rd, hrd],
        by rw [f₁.wr, hwr]⟩, by rw [f₁.gpr]⟩
  · intro k hk l hl i hi
    simp only [State.lane, x, y]; exact ht k hk l hl i hi
  · intro l; simp only [State.lane, x, y]; exact hy l

/-! ## The kernel's rounds -/

open VG.Proof.ChaCha20.X86_64.Avx2 (Holds HoldsV RI RV M8 M16 bufR slotsR vw doubleRound_ok doubleRoundV_ok
  loadV_ok storeV_ok)

/-- A state as `s` but for `rax`. -/
theorem gpr_setRax {s t : State} (h : ∀ q, q ≠ .rax → t.gpr q = s.gpr q) :
    t.gpr = (s.setReg .rax (t.gpr .rax)).gpr := by
  funext q
  rw [RegUpd.gpr_setReg]
  split
  · next h' => subst h'; rfl
  · next h' => exact h q h'

theorem holds_keep {buf : Addr} {p : Bool} {vs : Nat → CState} {s s' : State} (h : Holds buf p vs s)
    (x : s'.xmm = s.xmm) (y : s'.ymmHi = s.ymmHi) (m : s'.mem = s.mem) : Holds buf p vs s' := by
  intro k hk l q hl hq
  have e := h k hk l q hl hq
  simpa only [vw, State.lane, x, y, m] using e

theorem holdsV_keep {vs : Nat → CState} {s s' : State} (h : HoldsV vs s)
    (x : s'.xmm = s.xmm) (y : s'.ymmHi = s.ymmHi) : HoldsV vs s' := by
  intro k hk l q hl hq
  have e := h k hk l q hl hq
  simpa only [vw, State.lane, x, y] using e

/-- `RI` reads of `s₀` only its registers, memory and regions. -/
theorem ri_congr {buf : Addr} {p : Bool} {vs : Nat → CState} {s₀ s₀' s : State} (h : RI buf p vs s₀ s)
    (hg : s₀'.gpr = s₀.gpr) (hm : s₀'.mem = s₀.mem) (hrd : s₀'.rd = s₀.rd) (hwr : s₀'.wr = s₀.wr) :
    RI buf p vs s₀' s :=
  ⟨h.holds, h.m16, by rw [hm]; exact h.frame, by rw [hg]; exact h.gpr, by rw [hrd]; exact h.rd,
    by rw [hwr]; exact h.wr⟩

/-- The kernel's ten double rounds, looped (`roundsK`): as `roundsFor`, but
for `rax`. -/
theorem roundsK_ok (vl : Bool) {buf : Addr} {vs : Nat → CState} {s₀ : State} (h : Holds buf false vs s₀)
    (h15 : ∀ l, s₀.lane .xmm15 l = rot16Mask) (hrcx : s₀.gpr .rcx = buf) (hb : bufR buf ∈ s₀.wr)
    (h8 : M8 s₀.mem buf) (h16 : M16 s₀.mem buf) :
    WP isa (roundsK vl) s₀ fun s =>
      ∃ v, RI buf false (fun j => Nat.repeat innerBlock 10 (vs j)) (s₀.setReg .rax v) s := by
  cases vl
  · -- Without `vprold`: the double rounds, from the state but for `rax`.
    let I : Nat → State → Prop := fun i s => ∃ v, RI buf false (fun j => Nat.repeat innerBlock i (vs j))
      (s₀.setReg .rax v) s
    refine WP.mono (rounds10_ok I (fun i _ t ⟨v, ht⟩ => ?_) (fun i t t' ⟨v, ht⟩ g x y m rd wr => ?_)
      ⟨s₀.gpr .rax, ⟨h, h15, Frame.refl _ _, gpr_setRax (fun _ _ => rfl), rfl, rfl⟩⟩) fun s ⟨h', _⟩ => h'
    · refine WP.seq (WP.block_nil (doubleRound_ok ht (by rw [RegUpd.gpr_setReg]; exact hrcx)
        (by rw [RegUpd.wr_setReg]; exact hb) (by rw [RegUpd.mem_setReg]; exact h8))) |>.mono fun t' ht' =>
        ⟨⟨v, ht'⟩, by rw [ht'.gpr, ht.gpr]⟩
    · refine ⟨t'.gpr .rax, holds_keep ht.holds x y m, fun l => by simp only [State.lane, x, y]; exact ht.m16 l,
        by have f := ht.frame; rw [RegUpd.mem_setReg] at f; rw [m, RegUpd.mem_setReg]; exact f, ?_,
        by rw [rd, ht.rd]; rfl, by rw [wr, ht.wr]; rfl⟩
      rw [gpr_setRax g]
      funext q
      simp only [RegUpd.gpr_setReg]
      split
      · rfl
      · next hq => rw [ht.gpr, RegUpd.gpr_setReg]; simp only [hq, ite_false]
  · -- With `vprold`: words 10 and 11 in `ymm14`, `ymm15` meanwhile.
    unfold roundsK
    simp only [ite_true]
    refine WP.seq (WP.mono (loadV_ok h hrcx hb) fun s₁ ⟨h₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
    let I : Nat → State → Prop := fun i s => ∃ v, RV (fun j => Nat.repeat innerBlock i (vs j))
      (s₁.setReg .rax v) s
    refine WP.seq (WP.mono (rounds10_ok I (fun i _ t ⟨v, ht⟩ => ?_) (fun i t t' ⟨v, ht⟩ g x y m rd wr => ?_)
      ⟨s₁.gpr .rax, h₁, gpr_setRax (fun _ _ => rfl), rfl, rfl, rfl⟩) fun s₂ ⟨⟨v, h₂⟩, _⟩ => ?_)
    · refine WP.seq (WP.block_nil (doubleRoundV_ok ht)) |>.mono fun t' ht' =>
        ⟨⟨v, ht'⟩, by rw [ht'.2.1, ht.2.1]⟩
    · refine ⟨t'.gpr .rax, holdsV_keep ht.1 x y, ?_, by rw [m, ht.2.2.1]; rfl, by rw [rd, ht.2.2.2.1]; rfl,
        by rw [wr, ht.2.2.2.2]; rfl⟩
      rw [gpr_setRax g]
      funext q
      simp only [RegUpd.gpr_setReg]
      split
      · rfl
      · next hq => rw [ht.2.1, RegUpd.gpr_setReg]; simp only [hq, ite_false]
    · refine WP.mono (storeV_ok h₂ (by rw [RegUpd.gpr_setReg, g₁]; exact hrcx)
        (by rw [RegUpd.wr_setReg, wr₁]; exact hb) (by rw [RegUpd.mem_setReg, m₁]; exact h16)) fun s₃ h₃ =>
        ⟨v, ri_congr h₃ (by funext q; rw [RegUpd.gpr_setReg, RegUpd.gpr_setReg, g₁])
          (by rw [RegUpd.mem_setReg, RegUpd.mem_setReg, m₁]) (by rw [RegUpd.rd_setReg, RegUpd.rd_setReg, rd₁])
          (by rw [RegUpd.wr_setReg, RegUpd.wr_setReg, wr₁])⟩

end VG.Proof.ChaCha20Poly1305.X86_64.Short
