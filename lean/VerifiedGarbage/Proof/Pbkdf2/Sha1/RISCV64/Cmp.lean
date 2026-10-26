module

public import VerifiedGarbage.Proof.Pbkdf2.Sha1.RISCV64.Round
public import VerifiedGarbage.Proof.Pbkdf2.Sha1Words
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.RISCV64.Align
import Mathlib.Tactic.SplitIfs

/-!
# PBKDF2-HMAC-SHA-1's iteration on RISC-V: one compression

Untrusted: everything here is checked by Lean. `cmp_ok`: with the frame in
`B` and the five words `x` in the window's first five registers, `cmp L`
leaves `compress H (blk x)` in the working variables' registers, for the
hash value `H` at `hO` in the frame, and keeps every register but the
working variables', the window's, `KR` and `T1`, and memory. The rounds run
with the invariant `RInv`: the working variables after `t` rounds, the
window's last 16 words (all 16 words of the block before round 16), and
`Kₜ` in `KR` (but where it changes).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Sha1.RISCV64

open VG VG.RISCV64 VG.Impl.Pbkdf2.Sha1.RISCV64
open VG.RISCV64.ByteLoad (li32_ok)
open VG.RISCV64.Align (al_add)
open VG.Spec.Sha1 (HashValue Word Block K W f compress)
open VG.Proof.Sha1 (roundKW round_eq rounds_zero rounds_succ W_lt)
open VG.Proof.Pbkdf2.Sha1Words (blk)

/-- The registers a compression may change. -/
def Clob (L : Lay) (r : Reg) : Prop := r ∈ L.vs ∨ r ∈ L.w ∨ r = KR ∨ r = T1

/-- `Kₜ` changes only every 20 rounds. -/
theorem K_succ {t : Nat} (h : (t + 1) % 20 ≠ 0) : K (t + 1) = K t := by
  unfold Spec.Sha1.K
  split_ifs <;> first | rfl | omega

/-- The block's words. -/
theorem blk_lt (x : HashValue) {j : Nat} (hj : j < 5) : W (blk x) j = x[j] := by
  rw [W_lt _ (by omega)]; simp [blk, hj]

theorem blk_5 (x : HashValue) : W (blk x) 5 = 0x80000000 := by rw [W_lt _ (by decide)]; rfl
theorem blk_15 (x : HashValue) : W (blk x) 15 = 672 := by rw [W_lt _ (by decide)]; rfl
theorem blk_mid (x : HashValue) {j : Nat} (h₁ : 6 ≤ j) (h₂ : j < 15) : W (blk x) j = 0 := by
  rw [W_lt _ (by omega)]; simp [blk, show ¬ j < 5 by omega, show j ≠ 5 by omega, show j ≠ 15 by omega]

/-! ## The working variables and the padding -/

/-- The first `k` working variables loaded from the frame. -/
structure LdI (L : Lay) (s₀ : State) (H : HashValue) (k : Nat) (s : State) : Prop where
  vars : ∀ j < k, (s.gpr (L.var 0 j)).setWidth 32 = H[j]!
  keep : ∀ r, r ∉ L.vs → s.gpr r = s₀.gpr r
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

/-- After `t` rounds, from the state `s₀` before them. -/
structure RInv (L : Lay) (H : HashValue) (M : Block) (s₀ : State) (t : Nat) (s : State) : Prop where
  vars : Vars L t s (Spec.Sha1.rounds H M t)
  win : ∀ j, j < max 16 t → t ≤ j + 16 → (s.gpr (L.wr j)).setWidth 32 = W M j
  kr : t % 20 ≠ 0 → (s.gpr KR).setWidth 32 = K t
  keep : ∀ r, ¬ Clob L r → s.gpr r = s₀.gpr r
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

/-- The first `k` words of the hash value added. -/
structure AddI (L : Lay) (s₀ : State) (V H : HashValue) (k : Nat) (s : State) : Prop where
  done : ∀ j < k, (s.gpr (L.var 0 j)).setWidth 32 = V[j]! + H[j]!
  todo : ∀ j, k ≤ j → j < 5 → s.gpr (L.var 0 j) = s₀.gpr (L.var 0 j)
  keep : ∀ r, r ∉ L.vs → r ≠ T1 → s.gpr r = s₀.gpr r
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp


section
variable {L : Lay} (hL : LayOk L)
include hL

theorem load_ok (s₀ : State) (H : HashValue) {bv : Addr} (hB : s₀.gpr B = bv) (hal : bv.toNat % 8 = 0)
    (hin : ∀ k < 5, InRegions (s₀.rd ++ s₀.wr) (bv + BitVec.ofNat 64 (L.hO + 4 * k)) 4)
    (hH : ∀ k < 5, s₀.mem.readW (bv + BitVec.ofNat 64 (L.hO + 4 * k)) 32 = H[k]!) :
    WP isa (.block (load L)) s₀ (LdI L s₀ H 5) := by
  refine wp_range_flatMap (M := isa) (LdI L s₀ H) (fun k s hk h => ?_) 5 (Nat.le_refl _) s₀
    ⟨fun _ h => absurd h (by omega), fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  have m := var_mem hL 0 k hk
  have hb : s.gpr B = bv := by rw [h.keep _ fun e => (hL.vsp _ e).2.2.1 rfl, hB]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_w (s := s) (t := L.var 0 k) (show L.hO + 4 * k < 2048 by have := hL.hO; omega)
      (by rw [hb]; exact al_add hal (by decide) (by have := hL.hal; omega))
      (by rw [hb, h.rd, h.wr]; exact hin k hk),
    Option.some.injEq, exists_eq_left']
  refine ⟨fun j hj => ?_, fun r hr => ?_, h.mem, h.rd, h.wr, h.sp⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [RegUpd.gpr_write_of_ne _ _ (var_ne hL (by omega) hk (by omega))]; exact h.vars j hj
    · rw [RegUpd.gpr_write_self, lo32_ext, h.mem, hb, hH j hk]
  · rw [RegUpd.gpr_write_of_ne _ _ fun e => hr (by rw [e]; exact m)]; exact h.keep r hr

/-- After the padding: the window holds the block's first 16 words. -/
theorem consts_ok (s : State) (x : HashValue) (hx : ∀ k < 5, (s.gpr (L.wr k)).setWidth 32 = x[k]!) :
    WP isa (.block (consts L)) s fun s' =>
      (∀ j < 16, (s'.gpr (L.wr j)).setWidth 32 = W (blk x) j) ∧ (∀ r, r ∉ L.w → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have ne (i j : Nat) (hi : i < 16) (hj : j < 16) (h : i ≠ j) : L.wr i ≠ L.wr j :=
    wr_ne hL (by rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj]; exact h)
  unfold consts
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (li32_ok (d := L.wr 5) (s := s) 0x80000000) fun s₁ e₁ => ?_
  subst e₁
  rw [WP.block_append_iff]
  -- The nine zeros.
  let Z : Nat → State → Prop := fun k s' => (∀ i < k, (s'.gpr (L.wr (6 + i))).setWidth 32 = 0) ∧
    (∀ r, (∀ i < k, r ≠ L.wr (6 + i)) → s'.gpr r = (s.write (L.wr 5) (sext32 0x80000000)).gpr r) ∧
    s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp
  refine WP.mono (wp_range_flatMap (M := isa) Z (fun k s' hk h => ?_) 9 (Nat.le_refl _) _
    ⟨fun _ h => absurd h (by omega), fun _ _ => rfl, rfl, rfl, rfl, rfl⟩) fun s₂ h₂ => ?_
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_li (show imm12 0 by decide), Option.some.injEq,
      exists_eq_left']
    refine ⟨fun i hi => ?_, fun r hr => ?_, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [RegUpd.gpr_write_of_ne _ _ (ne _ _ (by omega) (by omega) (by omega))]; exact h.1 i hi
      · rw [RegUpd.gpr_write_self]; rfl
    · rw [RegUpd.gpr_write_of_ne _ _ (hr k (by omega))]
      exact h.2.1 r fun i hi => hr i (by omega)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_li (show imm12 672 by decide), Option.some.injEq,
    exists_eq_left']
  obtain ⟨z₂, k₂, m₂, rd₂, wr₂, sp₂⟩ := h₂
  have keep (r : Reg) (h15 : r ≠ L.wr 15) (hz : ∀ i < 9, r ≠ L.wr (6 + i)) (h5 : r ≠ L.wr 5) :
      (s₂.write (L.wr 15) (BitVec.ofInt 64 672)).gpr r = s.gpr r := by
    rw [RegUpd.gpr_write_of_ne _ _ h15, k₂ r hz, RegUpd.gpr_write_of_ne _ _ h5]
  refine ⟨fun j hj => ?_, fun r hr => ?_, m₂, rd₂, wr₂, sp₂⟩
  · rcases (show j < 5 ∨ j = 5 ∨ (6 ≤ j ∧ j < 15) ∨ j = 15 by omega) with h | rfl | h | rfl
    · rw [keep _ (ne _ _ (by omega) (by omega) (by omega)) (fun i _ => ne _ _ (by omega) (by omega) (by omega))
        (ne _ _ (by omega) (by omega) (by omega)), hx j h, blk_lt x h, getElem!_pos x j h]
    · rw [RegUpd.gpr_write_of_ne _ _ (ne _ _ (by omega) (by omega) (by omega)),
        k₂ _ (fun i _ => ne _ _ (by omega) (by omega) (by omega)), RegUpd.gpr_write_self, lo32_sext, blk_5]
    · obtain ⟨i, rfl⟩ : ∃ i, j = 6 + i := ⟨j - 6, by omega⟩
      rw [RegUpd.gpr_write_of_ne _ _ (ne _ _ (by omega) (by omega) (by omega)), z₂ i (by omega),
        blk_mid x (by omega) (by omega)]
    · rw [RegUpd.gpr_write_self, blk_15]; rfl
  · have hn : ∀ j < 16, r ≠ L.wr j := fun j _ e => hr (e ▸ wr_mem hL j)
    exact keep r (hn 15 (by decide)) (fun i hi => hn (6 + i) (by omega)) (hn 5 (by decide))

/-! ## The rounds -/

theorem step_ok (H : HashValue) (M : Block) (s₀ : State) (t : Nat) (s : State) (h : RInv L H M s₀ t s) :
    WP isa (.block (step L t)) s (RInv L H M s₀ (t + 1)) := by
  -- The schedule.
  unfold step
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (Q := fun (s₁ : State) => (s₁.gpr (L.wr t)).setWidth 32 = W M t ∧
    (∀ r, r ≠ L.wr t → r ≠ T1 → s₁.gpr r = s.gpr r) ∧
    s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.sp = s.sp) ?_ fun s₁ ⟨w₁, k₁, m₁, rd₁, wr₁, sp₁⟩ => ?_
  · by_cases ht : 16 ≤ t
    · simp only [ht, ite_true]
      exact sched_ok hL M t ht s fun j hj hj' => h.win j (by omega) hj'
    · simp only [ht, ite_false]
      exact WP.block_nil ⟨h.win t (by omega) (by omega), fun _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
  -- `Kₜ`.
  rw [WP.block_append_iff]
  refine WP.mono (Q := fun (s₂ : State) => (s₂.gpr KR).setWidth 32 = K t ∧ (∀ r, r ≠ KR → s₂.gpr r = s₁.gpr r) ∧
    s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr ∧ s₂.sp = s₁.sp) ?_ fun s₂ ⟨kv₂, k₂, m₂, rd₂, wr₂, sp₂⟩ => ?_
  · by_cases hk : t % 20 = 0
    · simp only [kload, hk, ite_true]
      exact WP.mono (li32_ok (K t)) fun s' e => by
        subst e
        exact ⟨by rw [RegUpd.gpr_write_self, lo32_sext], fun r hr => RegUpd.gpr_write_of_ne _ _ hr, rfl, rfl, rfl,
          rfl⟩
    · simp only [kload, hk, ite_false]
      refine WP.block_nil ⟨?_, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
      rw [k₁ _ (fun e => (hL.wsp _ (wr_mem hL t)).1 e.symm) (by decide)]
      exact h.kr hk
  -- The round.
  have hv₁ : Vars L t s₂ (Spec.Sha1.rounds H M t) := by
    have hv := h.vars
    have e : ∀ k, k < 5 → s₂.gpr (L.var t k) = s.gpr (L.var t k) := fun k hk => by
      have sp := hL.vsp _ (var_mem hL t k hk)
      rw [k₂ _ sp.1, k₁ _ (var_wr hL t k t hk) sp.2.1]
    simp only [Vars, e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e 4 (by decide)] at hv ⊢
    exact hv
  have hw₂ : (s₂.gpr (L.wr t)).setWidth 32 = W M t := by
    rw [k₂ _ fun e => (hL.wsp _ (wr_mem hL t)).1 e]; exact w₁
  refine WP.mono (round_ok hL t s₂ _ _ hv₁ hw₂ kv₂) fun s₃ ⟨hv₃, k₃, m₃, rd₃, wr₃, sp₃⟩ => ?_
  have wkeep (r : Reg) (hw : r ∈ L.w) : s₃.gpr r = s₂.gpr r :=
    k₃ r (fun hv => hL.vw r hv hw) (hL.wsp r hw).2.1
  refine ⟨?_, fun j hj hj' => ?_, fun hk => ?_, fun r hr => ?_, by rw [m₃, m₂, m₁, h.mem],
    by rw [rd₃, rd₂, rd₁, h.rd], by rw [wr₃, wr₂, wr₁, h.wr], by rw [sp₃, sp₂, sp₁, h.sp]⟩
  · rw [rounds_succ, round_eq]; exact hv₃
  · rw [wkeep _ (wr_mem hL j), k₂ _ fun e => (hL.wsp _ (wr_mem hL j)).1 e]
    by_cases hjt : j = t
    · subst hjt; exact w₁
    · rw [k₁ _ (wr_ne hL (by omega)) (hL.wsp _ (wr_mem hL j)).2.1]
      exact h.win j (by omega) (by omega)
  · rw [k₃ _ (fun hv => (hL.vsp _ hv).1 rfl) (by decide), kv₂, K_succ hk]
  · simp only [Clob, not_or] at hr
    obtain ⟨hv, hw, hk, h1⟩ := hr
    rw [k₃ r hv h1, k₂ r hk, k₁ r (fun e => hw (e ▸ wr_mem hL t)) h1]
    exact h.keep r (by simp only [Clob, not_or]; exact ⟨hv, hw, hk, h1⟩)

/-! ## The hash value added -/

theorem addH_ok (s₀ : State) (V H : HashValue) {bv : Addr} (hB : s₀.gpr B = bv) (hal : bv.toNat % 8 = 0)
    (hin : ∀ k < 5, InRegions (s₀.rd ++ s₀.wr) (bv + BitVec.ofNat 64 (L.hO + 4 * k)) 4)
    (hH : ∀ k < 5, s₀.mem.readW (bv + BitVec.ofNat 64 (L.hO + 4 * k)) 32 = H[k]!)
    (hV : ∀ k < 5, (s₀.gpr (L.var 0 k)).setWidth 32 = V[k]!) :
    WP isa (.block (addH L)) s₀ (AddI L s₀ V H 5) := by
  refine wp_range_flatMap (M := isa) (AddI L s₀ V H) (fun k s hk h => ?_) 5 (Nat.le_refl _) s₀
    ⟨fun _ h => absurd h (by omega), fun _ _ _ => rfl, fun _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
  have m := var_mem hL 0 k hk
  have sp := hL.vsp _ m
  have hb : s.gpr B = bv := by
    rw [h.keep _ (fun e => (hL.vsp _ e).2.2.1 rfl) (by decide), hB]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_w (s := s) (t := T1) (show L.hO + 4 * k < 2048 by have := hL.hO; omega)
      (by rw [hb]; exact al_add hal (by decide) (by have := hL.hal; omega))
      (by rw [hb, h.rd, h.wr]; exact hin k hk),
    exec_add, Option.some.injEq, exists_eq_left']
  refine ⟨fun j hj => ?_, fun j hj hj' => ?_, fun r hr h1 => ?_, h.mem, h.rd, h.wr, h.sp⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [RegUpd.gpr_write_of_ne _ _ (var_ne hL (by omega) hk (by omega)),
        RegUpd.gpr_write_of_ne _ _ (hL.vsp _ (var_mem hL 0 j (by omega))).2.1]
      exact h.done j hj
    · rw [RegUpd.gpr_write_self, lo32_add, RegUpd.gpr_write_of_ne _ _ sp.2.1, RegUpd.gpr_write_self, lo32_ext,
        h.todo j (Nat.le_refl _) hk, hV j hk, h.mem, hb, hH j hk]
  · rw [RegUpd.gpr_write_of_ne _ _ (var_ne hL hj' hk (by omega)),
      RegUpd.gpr_write_of_ne _ _ (hL.vsp _ (var_mem hL 0 j hj')).2.1]
    exact h.todo j (by omega) hj'
  · rw [RegUpd.gpr_write_of_ne _ _ fun e => hr (by rw [e]; exact m), RegUpd.gpr_write_of_ne _ _ h1]
    exact h.keep r hr h1

/-! ## The compression -/

theorem cmp_ok (s : State) (x H : HashValue) {bv : Addr} (hB : s.gpr B = bv) (hal : bv.toNat % 8 = 0)
    (hin : ∀ k < 5, InRegions (s.rd ++ s.wr) (bv + BitVec.ofNat 64 (L.hO + 4 * k)) 4)
    (hH : ∀ k < 5, s.mem.readW (bv + BitVec.ofNat 64 (L.hO + 4 * k)) 32 = H[k]!)
    (hx : ∀ k < 5, (s.gpr (L.wr k)).setWidth 32 = x[k]!) :
    WP isa (.block (cmp L)) s fun s' =>
      (∀ k < 5, (s'.gpr (L.var 0 k)).setWidth 32 = (compress H (blk x))[k]!) ∧
      (∀ r, ¬ Clob L r → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  unfold cmp
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (load_ok hL s H hB hal hin hH) fun s₁ h₁ => ?_
  rw [WP.block_append_iff]
  have hx₁ : ∀ k < 5, (s₁.gpr (L.wr k)).setWidth 32 = x[k]! := fun k hk => by
    rw [h₁.keep _ fun e => hL.vw _ e (wr_mem hL k)]; exact hx k hk
  refine WP.mono (consts_ok hL s₁ x hx₁) fun s₂ ⟨w₂, k₂, m₂, rd₂, wr₂, sp₂⟩ => ?_
  rw [WP.block_append_iff]
  have hv₂ : Vars L 0 s₂ (Spec.Sha1.rounds H (blk x) 0) := by
    have e : ∀ k, k < 5 → (s₂.gpr (L.var 0 k)).setWidth 32 = H[k]! := fun k hk => by
      rw [k₂ _ fun e => hL.vw _ (var_mem hL 0 k hk) e]; exact h₁.vars k hk
    rw [rounds_zero]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | (rw [e 0 (by decide)]; rfl) | (rw [e 1 (by decide)]; rfl) | (rw [e 2 (by decide)]; rfl)
    | (rw [e 3 (by decide)]; rfl) | (rw [e 4 (by decide)]; rfl)
  refine WP.mono (wp_range_flatMap (M := isa) (RInv L H (blk x) s₂) (fun t s' _ h => step_ok hL H _ s₂ t s' h)
    80 (Nat.le_refl _) s₂ ⟨hv₂, fun j hj _ => w₂ j (by omega), fun h => absurd rfl h, fun _ _ => rfl, rfl, rfl,
      rfl, rfl⟩) fun s₃ h₃ => ?_
  have hb₃ : s₃.gpr B = bv := by
    rw [h₃.keep _ (by simp only [Clob, not_or]; exact ⟨fun e => (hL.vsp _ e).2.2.1 rfl,
      fun e => (hL.wsp _ e).2.2.1 rfl, by decide, by decide⟩), k₂ _ (fun e => (hL.wsp _ e).2.2.1 rfl),
      h₁.keep _ (fun e => (hL.vsp _ e).2.2.1 rfl), hB]
  have rdwr₃ : s₃.rd ++ s₃.wr = s.rd ++ s.wr := by rw [h₃.rd, h₃.wr, rd₂, wr₂, h₁.rd, h₁.wr]
  have hv₃ : ∀ k < 5, (s₃.gpr (L.var 0 k)).setWidth 32 = (Spec.Sha1.rounds H (blk x) 80)[k]! := by
    obtain ⟨v0, v1, v2, v3, v4⟩ := h₃.vars
    intro k hk
    rw [getElem!_pos _ k hk]
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 by omega) with rfl | rfl | rfl | rfl | rfl
    exacts [v0, v1, v2, v3, v4]
  refine WP.mono (addH_ok hL s₃ _ H hb₃ hal (fun k hk => by rw [rdwr₃]; exact hin k hk)
    (fun k hk => by rw [h₃.mem, m₂, h₁.mem]; exact hH k hk) hv₃) fun s₄ h₄ => ?_
  refine ⟨fun k hk => ?_, fun r hr => ?_, by rw [h₄.mem, h₃.mem, m₂, h₁.mem], by rw [h₄.rd, h₃.rd, rd₂, h₁.rd],
    by rw [h₄.wr, h₃.wr, wr₂, h₁.wr], by rw [h₄.sp, h₃.sp, sp₂, h₁.sp]⟩
  · rw [h₄.done k hk, getElem!_pos _ k hk, getElem!_pos _ k hk, getElem!_pos _ k hk]
    simp only [compress, Vector.getElem_zipWith]
  · simp only [Clob, not_or] at hr
    obtain ⟨hv, hw, hk, h1⟩ := hr
    rw [h₄.keep r hv h1, h₃.keep r (by simp only [Clob, not_or]; exact ⟨hv, hw, hk, h1⟩), k₂ r hw, h₁.keep r hv]

end

end VG.Proof.Pbkdf2.Sha1.RISCV64
