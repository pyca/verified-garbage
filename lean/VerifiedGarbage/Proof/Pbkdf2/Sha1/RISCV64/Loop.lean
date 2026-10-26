module

public import VerifiedGarbage.Proof.Pbkdf2.Sha1.RISCV64.Frame
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Pbkdf2.Sha1.RISCV64.Round
public import VerifiedGarbage.Proof.Pbkdf2.Sha1.RISCV64.Cmp

/-!
# PBKDF2-HMAC-SHA-1's iteration on RISC-V: the loop

Untrusted: everything here is checked by Lean. One step (`body_ok`): the
inner compression of `U`'s block into `V`, the outer one of that into `A`
(`cmp_ok`), which is `U`'s next value, `T ← T ⊕ U` in the frame (`xorT_ok`),
and one step fewer left; the loop (`loop_ok`) runs them all, from the
invariant `LI`.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Sha1.RISCV64

open VG VG.RISCV64 VG.Impl.Pbkdf2.Sha1.RISCV64
open VG.RISCV64.Steps (Upd Mupd wp_xor wp_subi eval_zero eval_nonzero ofNat_beq_zero)
open VG.Proof.Pbkdf2.RISCV64 (Pre Sizes tp sc scR sc_al sc_sub)
open VG.Proof.Pbkdf2.RISCV64.Sha1 (it)
open VG.Spec.Sha1 (HashValue Word compress)
open VG.Proof.Pbkdf2.Sha1Words (blk wstep wIter)

/-! ## Word loads and stores -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_lw {t n : Reg} {off : Nat} {a : Addr} (ho : off < 2048) (ha : s.gpr n + BitVec.ofNat 64 off = a)
    (hal : a.toNat % 4 = 0) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Upd s s' t ((s.mem.readW a 32).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.load .w t n off :: is)) s Q := by
  refine Steps.WP.cons (s' := s.write t ((s.mem.readW a 32).setWidth 64)) ?_ (k _ (Upd.write _ _ _))
  rw [exec_load_w ho (by rw [ha]; exact hal) (by rw [ha]; exact hin), ha]

theorem wp_sw {t n : Reg} {off : Nat} {a : Addr} (ho : off < 2048) (ha : s.gpr n + BitVec.ofNat 64 off = a)
    (hal : a.toNat % 4 = 0) (hout : InRegions s.wr a 4)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 32)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store .w t n off :: is)) s Q := by
  refine Steps.WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr t).setWidth 32) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)
  rw [exec_store_w ho (by rw [ha]; exact hal) (by rw [ha]; exact hout), ha]

end

/-! ## Registers of the two layouts -/

theorem inner_wr : ∀ k < 5, inner.wr k = A.getD k .t0 := by decide
theorem inner_var : ∀ k < 5, inner.var 0 k = V.getD k .t0 := by decide
theorem outer_wr : ∀ k < 5, outer.wr k = V.getD k .t0 := by decide
theorem outer_var : ∀ k < 5, outer.var 0 k = A.getD k .t0 := by decide

theorem inner_keep : ¬ Clob inner B ∧ ¬ Clob inner N ∧ ¬ Clob inner TP := by simp only [Clob]; decide
theorem outer_keep : ¬ Clob outer B ∧ ¬ Clob outer N ∧ ¬ Clob outer TP := by simp only [Clob]; decide

theorem A_ne : ∀ k < 5, A.getD k .t0 ≠ T1 ∧ A.getD k .t0 ≠ B ∧ A.getD k .t0 ≠ N := by decide

/-! ## `T ← T ⊕ U` -/

/-- The first `k` words of `T` updated, from the state `s₁` before. -/
structure XI (s₀ s₁ : State) (x y : HashValue) (k : Nat) (s : State) : Prop where
  done : ∀ j < k, fw s₀ s.mem (tO + 4 * j) = y[j]! ^^^ x[j]!
  todo : ∀ j, k ≤ j → j < 5 → fw s₀ s.mem (tO + 4 * j) = y[j]!
  gpr : ∀ r, r ≠ T1 → s.gpr r = s₁.gpr r
  other : ∀ d, d + 4 ≤ tO → fw s₀ s.mem d = fw s₀ s₁.mem d
  saved : Spill.Saved (sc s₀) s₀.gpr saved s₁.mem → Spill.Saved (sc s₀) s₀.gpr saved s.mem
  frame : Frame [⟨sc s₀ + BitVec.ofNat 64 tO, 20⟩] s₁.mem s.mem
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  sp : s.sp = s₁.sp


section
variable {Wi : Nat} {s₀ : State} (hp : Pre it Wi s₀) (hz : Sizes it Wi)
include hp hz

theorem xorT_ok (s₁ : State) (x y : HashValue) (hb : s₁.gpr B = sc s₀)
    (hx : ∀ k < 5, (s₁.gpr (A.getD k .t0)).setWidth 32 = x[k]!) (hy : ∀ k < 5, fw s₀ s₁.mem (tO + 4 * k) = y[k]!)
    (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) :
    WP isa (.block xorT) s₁ (XI s₀ s₁ x y 5) := by
  refine wp_range_flatMap (M := isa) (XI s₀ s₁ x y) (fun k s hk h => ?_) 5 (Nat.le_refl _) s₁
    ⟨fun _ h => absurd h (by omega), fun j _ hj => hy j hj, fun _ _ => rfl, fun _ _ => rfl, id, Frame.refl _ _,
      rfl, rfl, rfl⟩
  have an := A_ne k hk
  have hb' : s.gpr B = sc s₀ := by rw [h.gpr _ (by decide), hb]
  have rd' : s.rd = s₀.rd := h.rd.trans hrd
  have wr' : s.wr = s₀.wr := h.wr.trans hwr
  refine wp_lw (a := sc s₀ + BitVec.ofNat 64 (tO + 4 * k)) (by simp only [tO]; omega) (by rw [hb'])
    (fal s₀ (by simp only [tO]; omega)) (frd hp hz rd' wr' (by simp only [tO]; omega)) fun s₂ u₂ => ?_
  refine wp_xor fun s₃ u₃ => ?_
  refine wp_sw (a := sc s₀ + BitVec.ofNat 64 (tO + 4 * k)) (by simp only [tO]; omega)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), hb']) (fal s₀ (by simp only [tO]; omega))
    (by rw [u₃.wr, u₂.wr]; exact fin hp hz wr' (by simp only [tO]; omega)) fun s₄ u₄ => WP.block_nil ?_
  have hv : (s₃.gpr T1).setWidth 32 = y[k]! ^^^ x[k]! := by
    rw [u₃.gpr, u₂.gpr, lo32_xor, lo32_ext, u₂.other _ an.1, h.gpr _ an.1, hx k hk]
    have := h.todo k (Nat.le_refl _) hk
    simp only [fw] at this
    rw [this]
  have m₄ : s₄.mem = s.mem.writeW (sc s₀ + BitVec.ofNat 64 (tO + 4 * k)) (y[k]! ^^^ x[k]!) := by
    rw [u₄.mem, hv, u₃.mem, u₂.mem]
  refine ⟨fun j hj => ?_, fun j hj hj' => ?_, fun r hr => ?_, fun d hd => ?_, fun hsv => ?_, ?_,
    by rw [u₄.rd, u₃.rd, u₂.rd, h.rd], by rw [u₄.wr, u₃.wr, u₂.wr, h.wr], by rw [u₄.sp, u₃.sp, u₂.sp, h.sp]⟩
  · rw [m₄]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [fw_write s₀ _ _ (by omega) (by simp only [tO]; omega) (by simp only [tO]; omega)]; exact h.done j hj
    · exact Mem.readW_writeW_self32 _ _ _
  · rw [m₄, fw_write s₀ _ _ (by omega) (by simp only [tO]; omega) (by simp only [tO]; omega)]
    exact h.todo j (by omega) hj'
  · rw [u₄.gpr, u₃.other _ hr, u₂.other _ hr, h.gpr _ hr]
  · rw [m₄, fw_write s₀ _ _ (by omega) (by simp only [tO] at hd ⊢; omega) (by simp only [tO]; omega)]
    exact h.other d hd
  · rw [m₄]; exact saved_write (h.saved hsv) _ (by simp only [tO]; omega) (by simp only [tO]; omega)
  · rw [m₄]
    exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by simp only [tO]; omega)
      (by simp only [tO]; omega) (by simp only [tO]; omega))

/-! ## One step -/

theorem body_ok {R : HashValue} {m : Nat} {s : State} (h : LI Wi s₀ R (m + 1) s) (hm : m + 1 < 2 ^ 64) :
    WP isa (.block body) s (LI Wi s₀ R m) := by
  obtain ⟨x, y, hx, hy, hR⟩ := h.xy
  have rdwr : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  unfold body
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  -- The inner compression.
  refine WP.mono (cmp_ok inner_ok s x (Hi s₀) h.b sc_al
    (fun k hk => frd hp hz h.rd h.wr (by simp only [inner, hiO]; omega)) (fun k hk => h.hs.hi k hk)
    (fun k hk => by rw [inner_wr k hk]; exact hx k hk)) fun s₁ ⟨v₁, k₁, m₁, rd₁, wr₁, sp₁⟩ => ?_
  rw [WP.block_append_iff]
  have b₁ : s₁.gpr B = sc s₀ := by rw [k₁ _ inner_keep.1, h.b]
  -- The outer compression.
  refine WP.mono (cmp_ok outer_ok s₁ (compress (Hi s₀) (blk x)) (Ho s₀) b₁ sc_al
    (fun k hk => frd hp hz (rd₁.trans h.rd) (wr₁.trans h.wr) (by simp only [outer, hoO]; omega))
    (fun k hk => by rw [m₁]; exact h.hs.ho k hk)
    (fun k hk => by rw [outer_wr k hk, ← inner_var k hk]; exact v₁ k hk)) fun s₂ ⟨v₂, k₂, m₂, rd₂, wr₂, sp₂⟩ => ?_
  rw [WP.block_append_iff]
  have b₂ : s₂.gpr B = sc s₀ := by rw [k₂ _ outer_keep.1, b₁]
  have hx₂ : ∀ k < 5, (s₂.gpr (A.getD k .t0)).setWidth 32 = (wstep (Hi s₀) (Ho s₀) x)[k]! := fun k hk => by
    rw [← outer_var k hk]; exact v₂ k hk
  -- `T ← T ⊕ U`.
  refine WP.mono (xorT_ok hp hz s₂ _ y b₂ hx₂ (fun k hk => by rw [m₂, m₁]; exact hy k hk)
    (rd₂.trans (rd₁.trans h.rd)) (wr₂.trans (wr₁.trans h.wr))) fun s₃ h₃ => ?_
  refine wp_subi (imm := 1) (by decide) fun s₄ u₄ => WP.block_nil ?_
  have g₃ : ∀ r, r ≠ T1 → ¬ Clob outer r → ¬ Clob inner r → s₃.gpr r = s.gpr r := fun r h1 ho hi => by
    rw [h₃.gpr r h1, k₂ r ho, k₁ r hi]
  refine ⟨?_, ?_, ?_, ⟨wstep (Hi s₀) (Ho s₀) x, Vector.zipWith (· ^^^ ·) y (wstep (Hi s₀) (Ho s₀) x), fun k hk => ?_,
    fun k hk => ?_, ?_⟩, ⟨fun k hk => ?_, fun k hk => ?_⟩, ?_, by rw [u₄.rd, h₃.rd, rd₂, rd₁, h.rd],
    by rw [u₄.wr, h₃.wr, wr₂, wr₁, h.wr], by rw [u₄.sp, h₃.sp, sp₂, sp₁, h.sp], ?_⟩
  · rw [u₄.other _ (by decide), g₃ _ (by decide) outer_keep.1 inner_keep.1, h.b]
  · rw [u₄.gpr, g₃ _ (by decide) outer_keep.2.1 inner_keep.2.1, h.n]
    rw [Offset.ofNat_sub_ofNat (show 1 ≤ m + 1 by omega), Nat.add_sub_cancel]
  · rw [u₄.other _ (by decide), g₃ _ (by decide) outer_keep.2.2 inner_keep.2.2, h.tp]
  · rw [u₄.other _ (A_ne k hk).2.2, h₃.gpr _ (A_ne k hk).1]; exact hx₂ k hk
  · rw [u₄.mem, h₃.done k hk, getElem!_pos _ k hk, getElem!_pos _ k hk, getElem!_pos _ k hk,
      Vector.getElem_zipWith]
  · rw [← hR]; rfl
  · rw [u₄.mem, h₃.other _ (by simp only [hiO, tO]; omega), m₂, m₁]; exact h.hs.hi k hk
  · rw [u₄.mem, h₃.other _ (by simp only [hoO, tO]; omega), m₂, m₁]; exact h.hs.ho k hk
  · rw [u₄.mem]; exact h₃.saved (by rw [m₂, m₁]; exact h.saved)
  · rw [u₄.mem]
    refine h.frame.trans ?_
    rw [← m₁, ← m₂]
    exact h₃.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scR Wi s₀, by simp, sc_sub (by have := hz.fits; simp only [it, tO] at this ⊢; omega)⟩

/-! ## The loop -/

theorem loop_ok {R : HashValue} {n : Nat} (hn : n < 2 ^ 32) {s : State} (h : LI Wi s₀ R n s) :
    WP isa (.ite (.zero N) (.block []) (.loop (.block body) (.nonzero N))) s (LI Wi s₀ R 0) := by
  have hlt : n < 2 ^ 64 := by omega
  refine WP.ite (decide (n = 0)) (by rw [eval_zero, h.n, ofNat_beq_zero hlt]) (fun hb => ?_) (fun hb => ?_)
  · obtain rfl : n = 0 := by simpa using hb
    exact WP.block_nil h
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hb; omega⟩
    refine WP.loop (M := isa) (fun m s => m + 1 < 2 ^ 32 ∧ LI Wi s₀ R (m + 1) s)
      (fun m s ⟨hm, hs'⟩ => WP.mono (body_ok hp hz hs' (by omega)) fun s' hi => ?_) m s ⟨hn, h⟩
    have hz' : isa.eval (.nonzero N) s' = some (decide (m ≠ 0)) := by
      rw [eval_nonzero, hi.n, bne, ofNat_beq_zero (by omega)]; simp
    cases m with
    | zero => exact .inl ⟨by rw [hz']; rfl, hi⟩
    | succ m => exact .inr ⟨by rw [hz']; simp, m, by omega, by omega, hi⟩

end

end VG.Proof.Pbkdf2.Sha1.RISCV64
