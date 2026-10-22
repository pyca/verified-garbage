module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelectY
public import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacOddP
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# The selection with SSE2 and a counter on x86-64

`selEntryX` (`Impl/Weierstrass/X86_64/WinJacOddP.lean`) is `selEntryAt` with
the mask of entry `m` from `pcmpeqd` of the broadcasts of `m` (a counter in
`xmm11`, incremented by `paddd`) and of the magnitude `a` (in `xmm13`), as
`selEntryY` takes it with AVX2, rather than from `r8`: after entry `m` the
accumulators hold their pieces of entry `a` if `1 ≤ a ≤ m`, else zero
(`accVal`, `selEntriesFromX_ok`), and no general-purpose register but `rdx`
is read or written.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass

theorem selAcc_neX : ∀ c < 10, selAcc c ≠ .xmm11 ∧ selAcc c ≠ .xmm12 ∧ selAcc c ≠ .xmm13 ∧
    selAcc c ≠ .xmm14 ∧ selAcc c ≠ .xmm15 := by decide

/-- `pshufd` by `0` of `movq`'s result: doubleword `0` in every one. -/
theorem shuf0_movq {a : Nat} (ha : a < 2 ^ 32) :
    shufDwords ((0 : BitVec 64) ++ BitVec.ofNat 64 a) 0 = bcast32 (BitVec.ofNat 32 a) := by
  have e : ∀ i, ((0 : BitVec 8).extractLsb' i 2).toNat = 0 := fun i => by
    simp
  simp only [shufDwords, e, dword_movq ha]

/-- `r = a` broadcast to every doubleword of `d`. -/
theorem bcastX_ok (s : State) (d : XReg) (r : Reg) {a : Nat} (ha : a < 2 ^ 32)
    (hr : s.gpr r = BitVec.ofNat 64 a) :
    WP isa (.block [.xop (.movq d r), .xop (.pshufd d d 0)]) s fun t =>
      t.xmm d = bcast32 (BitVec.ofNat 32 a) ∧ XKeep [] (· = d) s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, RegUpd.xmm_setXmm_self, hr,
    shuf0_movq ha, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun _ _ => rfl, rfl, rfl, rfl, fun x hx => by
    rw [RegUpd.xmm_setXmm_of_ne _ _ hx, RegUpd.xmm_setXmm_of_ne _ _ hx]⟩

/-- The magnitude `r8 = a` broadcast to `xmm13`, and one to `xmm12` and the
counter `xmm11`, through `rcx`. -/
theorem selSetX_ok (s : State) {a : Nat} (ha : a < 2 ^ 31) (h8 : s.gpr .r8 = BitVec.ofNat 64 a) :
    WP isa (.block [.xop (.movq .xmm13 .r8), .xop (.pshufd .xmm13 .xmm13 0), .mov32 .rcx (.imm 1),
      .xop (.movq .xmm12 .rcx), .xop (.pshufd .xmm12 .xmm12 0), .xop (.bin .movdqa .xmm11 .xmm12)]) s fun t =>
      t.xmm .xmm13 = bcast32 (BitVec.ofNat 32 a) ∧ t.xmm .xmm12 = bcast32 (BitVec.ofNat 32 1) ∧
      t.xmm .xmm11 = bcast32 (BitVec.ofNat 32 1) ∧
      XKeep [.rcx] (fun r => r = .xmm11 ∨ r = .xmm12 ∨ r = .xmm13) s t := by
  rw [show ([.xop (.movq .xmm13 .r8), .xop (.pshufd .xmm13 .xmm13 0), .mov32 .rcx (.imm 1),
      .xop (.movq .xmm12 .rcx), .xop (.pshufd .xmm12 .xmm12 0), .xop (.bin .movdqa .xmm11 .xmm12)] : List Instr) =
    [.xop (.movq .xmm13 .r8), .xop (.pshufd .xmm13 .xmm13 0)] ++ ([.mov32 .rcx (.imm 1)] ++
      ([.xop (.movq .xmm12 .rcx), .xop (.pshufd .xmm12 .xmm12 0)] ++
        [.xop (.bin .movdqa .xmm11 .xmm12)])) from rfl, WP.block_append_iff]
  refine WP.mono (bcastX_ok s .xmm13 .r8 (by omega) h8) fun s₁ ⟨b₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.mov32 .rcx (.imm 1)]) s₁ (fun s₂ =>
      s₂.gpr .rcx = BitVec.ofNat 64 1 ∧ XKeep [.rcx] (fun _ => False) s₁ s₂) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
      Option.some.injEq, exists_eq_left', State.setReg32, RegUpd.gpr_setReg, ite_true]
    refine ⟨by decide, fun r hr => ?_, rfl, rfl, rfl, fun _ _ => rfl⟩
    simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s₂ ⟨c₂, k₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (bcastX_ok s₂ .xmm12 .rcx (by decide) c₂) fun s₃ ⟨b₃, k₃⟩ => ?_
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, XBinOp.eval, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, ?_, ?_, ⟨fun r hr => ?_, ?_, ?_, ?_, fun x hx => ?_⟩⟩
  · rw [RegUpd.xmm_setXmm_of_ne _ _ (by decide), k₃.xmm _ (by decide), k₂.xmm _ id, b₁]
  · rw [RegUpd.xmm_setXmm_of_ne _ _ (by decide), b₃]
  · rw [RegUpd.xmm_setXmm_self, b₃]
  · rw [RegUpd.gpr_setXmm, k₃.gpr r List.not_mem_nil, k₂.gpr r hr, k₁.gpr r List.not_mem_nil]
  · rw [RegUpd.mem_setXmm, k₃.mem, k₂.mem, k₁.mem]
  · show s₃.rd = s.rd; rw [k₃.rd, k₂.rd, k₁.rd]
  · show s₃.wr = s.wr; rw [k₃.wr, k₂.wr, k₁.wr]
  · simp only [not_or] at hx
    rw [RegUpd.xmm_setXmm_of_ne _ _ hx.1, k₃.xmm _ hx.2.1, k₂.xmm _ id, k₁.xmm _ hx.2.2]

/-- The mask of `a = m` in `xmm15`, from the counter `xmm11 = m` and the
broadcast magnitude `xmm13 = a`, and the counter incremented by `xmm12 = 1`. -/
theorem selMaskX_ok (s : State) {a m : Nat} (ha : a < 2 ^ 31) (hm : m < 2 ^ 31)
    (h13 : s.xmm .xmm13 = bcast32 (BitVec.ofNat 32 a)) (h12 : s.xmm .xmm12 = bcast32 (BitVec.ofNat 32 1))
    (h11 : s.xmm .xmm11 = bcast32 (BitVec.ofNat 32 m)) :
    WP isa (.block [.xop (.bin .movdqa .xmm15 .xmm11), .xop (.bin .pcmpeqd .xmm15 .xmm13),
        .xop (.bin .paddd .xmm11 .xmm12)]) s fun t =>
      t.xmm .xmm15 = bmask128 (decide (a = m)) ∧ t.xmm .xmm11 = bcast32 (BitVec.ofNat 32 (m + 1)) ∧
      XKeep [] (fun r => r = .xmm11 ∨ r = .xmm15) s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ⟨fun _ _ => rfl, rfl, rfl, rfl, fun r hr => ?_⟩⟩
  · rw [RegUpd.xmm_setXmm_of_ne _ _ (by decide), RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_self,
      RegUpd.xmm_setXmm_of_ne _ _ (by decide), h13, XBinOp.eval, h11, pcmpeqd_bcast,
      ofNat32_eq (show a < 2 ^ 32 by omega) (show m < 2 ^ 32 by omega)]
  · simp only [RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne _ _ (show ¬ XReg.xmm11 = .xmm15 by decide),
      RegUpd.xmm_setXmm_of_ne _ _ (show ¬ XReg.xmm12 = .xmm15 by decide), h11, h12, paddd_bcast,
      ← BitVec.ofNat_add]
  · simp only [not_or] at hr
    rw [RegUpd.xmm_setXmm_of_ne _ _ hr.1, RegUpd.xmm_setXmm_of_ne _ _ hr.2, RegUpd.xmm_setXmm_of_ne _ _ hr.2]

/-- The accumulators after entries `1 … m`, 16 bytes at a time: accumulator
`c` is piece `c` (`accVal`). -/
def AccX (t : State) (mem : Mem) (X : Addr) (st a m np : Nat) : Prop :=
  ∀ c < np, t.xmm (selAcc c) = accVal mem X st (16 * ·) a m c

/-- Entry `m` of the table at `rdx = X` kept in the accumulators under the
mask of `a = m`, and the counter incremented. -/
theorem selEntryX_ok {st np : Nat} {s : State} {X : Addr} {a m : Nat} (hn : np ≤ 10)
    (hm1 : 1 ≤ m) (hm : m < 2 ^ 31) (ha : a < 2 ^ 31) (hx : s.gpr .rdx = X)
    (h13 : s.xmm .xmm13 = bcast32 (BitVec.ofNat 32 a)) (h12 : s.xmm .xmm12 = bcast32 (BitVec.ofNat 32 1))
    (h11 : s.xmm .xmm11 = bcast32 (BitVec.ofNat 32 m))
    (hr : ∀ c < np, InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (st * (m - 1) + 16 * c)) 16)
    (hacc : AccX s s.mem X st a (m - 1) np) :
    WP isa (.block (selEntryX st np m)) s fun t =>
      AccX t s.mem X st a m np ∧ t.xmm .xmm11 = bcast32 (BitVec.ofNat 32 (m + 1)) ∧
      XKeep [] (fun r => (∃ c < np, r = selAcc c) ∨ r = .xmm11 ∨ r = .xmm14 ∨ r = .xmm15) s t := by
  rw [selEntryX, WP.block_append_iff]
  refine WP.mono (selMaskX_ok s ha hm h13 h12 h11) fun s₁ ⟨x₁, c₁, k₁⟩ => ?_
  refine WP.mono (selSteps_ok (X := X) (po := (16 * ·)) (by omega) np (Nat.le_refl _) s₁
    (by rw [k₁.gpr _ List.not_mem_nil, hx]) (by rw [k₁.rd, k₁.wr]; exact hr)) fun t ⟨a₂, k₂⟩ =>
    ⟨fun c hc => ?_, ?_, ?_⟩
  · obtain ⟨n11, -, -, -, n15⟩ := selAcc_neX c (by omega)
    rw [a₂ c (by omega), ite_eq_left_of_eq_true _ _ (eq_true hc), x₁, k₁.mem,
      k₁.xmm _ (by rintro (h | h); exacts [n11 h, n15 h]), hacc c hc]
    exact accVal_step _ _ _ (16 * ·) _ _ _ hm1
  · rw [k₂.xmm _ (by
      rintro (⟨c, hc, h⟩ | h)
      · exact (selAcc_neX c (by omega)).1 h.symm
      · exact absurd h (by decide)), c₁]
  · exact (k₁.mono (fun _ h => h) fun r h => by
      rcases h with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr h))).trans (k₂.mono (fun _ h => h) fun r h => by
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h)))

/-- Entries `lo + 1 … lo + h` of the table at `rdx = X` kept in the
accumulators (holding entries `1 … lo`) under the masks of `a`, the counter
from `lo + 1`. -/
theorem selEntriesFromX_ok {st np : Nat} {X : Addr} {a lo : Nat} (hn : np ≤ 10) (ha : a < 2 ^ 31) :
    ∀ h, lo + h < 2 ^ 31 → ∀ (s : State), s.gpr .rdx = X →
    s.xmm .xmm13 = bcast32 (BitVec.ofNat 32 a) → s.xmm .xmm12 = bcast32 (BitVec.ofNat 32 1) →
    s.xmm .xmm11 = bcast32 (BitVec.ofNat 32 (lo + 1)) →
    (∀ e < h, ∀ c < np, InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (st * (lo + e) + 16 * c)) 16) →
    AccX s s.mem X st a lo np →
    WP isa (.block ((List.range h).flatMap fun e => selEntryX st np (lo + e + 1))) s fun t =>
      AccX t s.mem X st a (lo + h) np ∧ t.xmm .xmm11 = bcast32 (BitVec.ofNat 32 (lo + h + 1)) ∧
      XKeep [] (fun r => (∃ c < np, r = selAcc c) ∨ r = .xmm11 ∨ r = .xmm14 ∨ r = .xmm15) s t
  | 0, _, s, _, _, _, h11, _, h0 => WP.block_nil ⟨h0, h11, XKeep.refl _ _ _⟩
  | h + 1, hh, s, hx, h13, h12, h11, hr, h0 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (selEntriesFromX_ok hn ha h (by omega) s hx h13 h12 h11 (fun e he => hr e (by omega)) h0)
      fun s₁ ⟨a₁, c₁, k₁⟩ => ?_
    have n13 : ¬ ((∃ c < np, XReg.xmm13 = selAcc c) ∨ XReg.xmm13 = .xmm11 ∨ XReg.xmm13 = .xmm14 ∨
        XReg.xmm13 = .xmm15) := by
      rintro (⟨c, hc, h⟩ | h | h | h)
      · exact (selAcc_neX c (by omega)).2.2.1 h.symm
      all_goals exact absurd h (by decide)
    have n12 : ¬ ((∃ c < np, XReg.xmm12 = selAcc c) ∨ XReg.xmm12 = .xmm11 ∨ XReg.xmm12 = .xmm14 ∨
        XReg.xmm12 = .xmm15) := by
      rintro (⟨c, hc, h⟩ | h | h | h)
      · exact (selAcc_neX c (by omega)).2.1 h.symm
      all_goals exact absurd h (by decide)
    refine WP.mono (selEntryX_ok (X := X) (m := lo + h + 1) hn (by omega) hh ha
      (by rw [k₁.gpr _ List.not_mem_nil, hx]) (by rw [k₁.xmm _ n13, h13])
      (by rw [k₁.xmm _ n12, h12]) c₁
      (fun c hc => by rw [k₁.rd, k₁.wr, Nat.add_sub_cancel]; exact hr h (by omega) c hc)
      (fun c hc => by rw [a₁ c hc, k₁.mem, Nat.add_sub_cancel])) fun t ⟨a₂, c₂, k₂⟩ =>
      ⟨fun c hc => by rw [a₂ c hc, k₁.mem, ← Nat.add_assoc], by
        rw [show lo + (h + 1) + 1 = lo + h + 1 + 1 by omega]; exact c₂, k₁.trans k₂⟩

end VG.Proof.Weierstrass.X86_64
