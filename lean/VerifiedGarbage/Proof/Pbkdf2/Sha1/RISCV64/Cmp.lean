module

public import VerifiedGarbage.Proof.Pbkdf2.Sha1.RISCV64.Round
public import VerifiedGarbage.Proof.Pbkdf2.Sha1Words
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.RISCV64.Align
/-!
# PBKDF2-HMAC-SHA-1's iteration on RISC-V: one compression

Untrusted: everything here is checked by Lean. `cmp_ok`: with the frame in
`B` and the five words `x` in the window's first five registers, `cmp L`
leaves `compress H (blk x)` in the working variables' registers, for the
hash value `H` at `hO` in the frame, and keeps every register but the
working variables', the window's, `KR` and `T1`, and memory. The rounds run
with the invariant `RInv`: the working variables after `t` rounds, the
window's last 16 words but the padding's constants (only `U`'s five words
before round 16), and `Kₜ` in `KR` (but where it changes). A step of the
schedule (`sched_ok`) is the exclusive or of the words in registers
(`xors_ok`), rotated, and then of the constants', rotated (`W_split`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Sha1.RISCV64

open VG VG.RISCV64 VG.Impl.Pbkdf2.Sha1.RISCV64
open VG.RISCV64.ByteLoad (li32_ok)
open VG.RISCV64.Align (al_add)
open VG.Spec.Sha1 (HashValue Word Block K W f compress)
open VG.Proof.Sha1 (roundKW round_eq rounds_zero rounds_succ W_lt W_ge)
open VG.Proof.Pbkdf2.Sha1Words (blk)

/-- The registers a compression may change. -/
def Clob (L : Lay) (r : Reg) : Prop := r ∈ L.vs ∨ r ∈ L.w ∨ r = KR ∨ r = T1

/-- `Kₜ` changes only every 20 rounds. -/
theorem K_succ {t : Nat} (h : (t + 1) % 20 ≠ 0) : K (t + 1) = K t := by
  unfold Spec.Sha1.K
  (repeat' split) <;> first | rfl | omega

/-- The block's words. -/
theorem blk_lt (x : HashValue) {j : Nat} (hj : j < 5) : W (blk x) j = x[j] := by
  rw [W_lt _ (by omega)]; simp [blk, hj]

theorem blk_5 (x : HashValue) : W (blk x) 5 = 0x80000000 := by rw [W_lt _ (by decide)]; rfl
theorem blk_15 (x : HashValue) : W (blk x) 15 = 672 := by rw [W_lt _ (by decide)]; rfl
theorem blk_mid (x : HashValue) {j : Nat} (h₁ : 6 ≤ j) (h₂ : j < 15) : W (blk x) j = 0 := by
  rw [W_lt _ (by omega)]; simp [blk, show ¬ j < 5 by omega, show j ≠ 5 by omega, show j ≠ 15 by omega]

/-- The padding's words are `cval`'s. -/
theorem blk_c (x : HashValue) {j : Nat} (h : isC j = true) : W (blk x) j = cval j := by
  simp only [isC, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases (show j = 5 ∨ (6 ≤ j ∧ j < 15) ∨ j = 15 by omega) with rfl | h' | rfl
  · rw [blk_5]; rfl
  · rw [blk_mid x h'.1 h'.2]; simp [cval, show j ≠ 5 by omega, show j ≠ 15 by omega]
  · rw [blk_15]; rfl

/-! ## The working variables -/

/-- The first `k` working variables loaded from the frame. -/
structure LdI (L : Lay) (s₀ : State) (H : HashValue) (k : Nat) (s : State) : Prop where
  vars : ∀ j < k, s.gpr (L.var 0 j) = H[j]!.setWidth 64
  keep : ∀ r, r ∉ L.vs → s.gpr r = s₀.gpr r
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

/-- After `t` rounds, from the state `s₀` before them. -/
structure RInv (L : Lay) (H : HashValue) (M : Block) (s₀ : State) (t : Nat) (s : State) : Prop where
  vars : Vars L t s (Spec.Sha1.rounds H M t)
  win : ∀ j, j < max 16 t → t ≤ j + 16 → isC j = false → (s.gpr (L.wr j)).setWidth 32 = W M j
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

theorem loads_ok (s₀ : State) (H : HashValue) {bv : Addr} (hB : s₀.gpr B = bv) (hal : bv.toNat % 8 = 0)
    (hin : ∀ k < 5, InRegions (s₀.rd ++ s₀.wr) (bv + BitVec.ofNat 64 (L.hO + 4 * k)) 4)
    (hH : ∀ k < 5, s₀.mem.readW (bv + BitVec.ofNat 64 (L.hO + 4 * k)) 32 = H[k]!) :
    WP isa (.block ((List.range 5).flatMap fun k => [.load .w (L.var 0 k) B (L.hO + 4 * k)])) s₀
      (LdI L s₀ H 5) := by
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
    · rw [RegUpd.gpr_write_self, h.mem, hb, hH j hk]
  · rw [RegUpd.gpr_write_of_ne _ _ fun e => hr (by rw [e]; exact m)]; exact h.keep r hr

/-- The working variables loaded, `a` and `b` doubled. -/
theorem load_ok (s₀ : State) (H : HashValue) {bv : Addr} (hB : s₀.gpr B = bv) (hal : bv.toNat % 8 = 0)
    (hin : ∀ k < 5, InRegions (s₀.rd ++ s₀.wr) (bv + BitVec.ofNat 64 (L.hO + 4 * k)) 4)
    (hH : ∀ k < 5, s₀.mem.readW (bv + BitVec.ofNat 64 (L.hO + 4 * k)) 32 = H[k]!) :
    WP isa (.block (load L)) s₀ fun s =>
      Vars L 0 s H ∧ (∀ r, r ∉ L.vs → r ≠ T1 → s.gpr r = s₀.gpr r) ∧
      s.mem = s₀.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.sp = s₀.sp := by
  unfold load
  rw [WP.block_append_iff]
  refine WP.mono (loads_ok hL s₀ H hB hal hin hH) fun s₁ h₁ => ?_
  have sp0 := hL.vsp _ (var_mem hL 0 0 (by decide))
  have sp1 := hL.vsp _ (var_mem hL 0 1 (by decide))
  have n01 := var_ne hL (t := 0) (show 0 < 5 by decide) (show 1 < 5 by decide) (by decide)
  have v (k : Nat) (hk : k < 5) : s₁.gpr (L.var 0 k) = H[k].setWidth 64 := by
    rw [h₁.vars k hk, getElem!_pos H k hk]
  have t1 := sp0.2.1; have t1' := sp1.2.1
  simp only [T1] at t1 t1' ⊢
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_logic, exec_shift_d (show 32 < 64 by decide),
    Option.some.injEq, exists_eq_left']
  have hne (k : Nat) (hk : k < 5) (h0 : k ≠ 0) (h1 : k ≠ 1) : L.var 0 k ≠ L.var 0 0 ∧ L.var 0 k ≠ L.var 0 1 ∧
      L.var 0 k ≠ .a6 :=
    ⟨var_ne hL hk (by decide) h0, var_ne hL hk (by decide) h1, (hL.vsp _ (var_mem hL 0 k hk)).2.1⟩
  obtain ⟨a2, b2, c2⟩ := hne 2 (by decide) (by decide) (by decide)
  obtain ⟨a3, b3, c3⟩ := hne 3 (by decide) (by decide) (by decide)
  obtain ⟨a4, b4, c4⟩ := hne 4 (by decide) (by decide) (by decide)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, fun r hr h1 => ?_, h₁.mem, h₁.rd, h₁.wr, h₁.sp⟩
  · simp only [RegUpd.gpr_write, t1, n01, ↓reduceIte]; rw [v 0 (by decide), dbl_ext]
  · simp only [RegUpd.gpr_write, t1', Ne.symm n01, ↓reduceIte]; rw [v 1 (by decide), dbl_ext]
  · simp only [RegUpd.gpr_write, a2, b2, c2, ↓reduceIte]; rw [v 2 (by decide), lo32_ext]
  · simp only [RegUpd.gpr_write, a3, b3, c3, ↓reduceIte]; rw [v 3 (by decide), lo32_ext]
  · simp only [RegUpd.gpr_write, a4, b4, c4, ↓reduceIte]; rw [v 4 (by decide), lo32_ext]
  · have h0 : r ≠ L.var 0 0 := fun e => hr (e ▸ var_mem hL 0 0 (by decide))
    have h1' : r ≠ L.var 0 1 := fun e => hr (e ▸ var_mem hL 0 1 (by decide))
    simp only [RegUpd.gpr_write, h0, h1', h1, ↓reduceIte]
    exact h₁.keep r hr

end

/-! ## The message schedule -/

theorem xor_zero' (a : Word) : a ^^^ 0 = a := BitVec.xor_zero
theorem zero_xor' (a : Word) : 0 ^^^ a = a := BitVec.zero_xor

/-- The exclusive or of a list of words. -/
def xl (l : List Word) : Word := l.foldl (· ^^^ ·) 0

theorem foldl_xor (l : List Word) (a : Word) : l.foldl (· ^^^ ·) a = a ^^^ l.foldl (· ^^^ ·) 0 := by
  induction l generalizing a with
  | nil => rw [List.foldl_nil, List.foldl_nil, xor_zero']
  | cons y l ih => rw [List.foldl_cons, List.foldl_cons, ih (a ^^^ y), ih (0 ^^^ y), zero_xor', BitVec.xor_assoc]

theorem xl_nil : xl [] = 0 := rfl

theorem xl_cons (y : Word) (l : List Word) : xl (y :: l) = y ^^^ xl l := by
  unfold xl; rw [List.foldl_cons, zero_xor', foldl_xor]

/-- The exclusive or splits into the words that pass a test and the others. -/
theorem xl_filter (g : Nat → Word) (p : Nat → Bool) (l : List Nat) :
    xl (l.map g) = xl ((l.filter fun j => !p j).map g) ^^^ xl ((l.filter p).map g) := by
  induction l with
  | nil => rw [List.filter_nil, List.filter_nil, List.map_nil, xl_nil, xor_zero']
  | cons j l ih =>
    cases h : p j
    · simp only [List.map_cons, List.filter_cons, h, Bool.not_false, ↓reduceIte, xl_cons, ih,
        Bool.false_eq_true, BitVec.xor_assoc]
    · simp only [List.map_cons, List.filter_cons, h, Bool.not_true, ↓reduceIte, xl_cons, ih,
        Bool.false_eq_true]
      ac_rfl

theorem rotl1_xor (a b : Word) : (a ^^^ b).rotateLeft 1 = a.rotateLeft 1 ^^^ b.rotateLeft 1 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_rotateLeft, BitVec.getLsbD_xor]
  split <;> simp [hi]

/-- `Wₜ`, the words in registers apart from the padding's (`16 ≤ t`). -/
theorem W_split (x : HashValue) {t : Nat} (ht : 16 ≤ t) :
    W (blk x) t = (xl ((vterms t).map (W (blk x)))).rotateLeft 1 ^^^ cterm t := by
  rw [W_ge _ ht, cterm, ← rotl1_xor]
  congr 1
  have e : ((terms t).filter isC).foldl (fun c j => c ^^^ cval j) 0 =
      xl (((terms t).filter isC).map (W (blk x))) := by
    rw [xl, ← List.foldl_map (f := cval) (g := (· ^^^ ·))]
    exact congrArg (List.foldl (· ^^^ ·) 0)
      (List.map_congr_left fun j hj => (blk_c x (List.mem_filter.mp hj).2).symm)
  rw [e, vterms, ← xl_filter]
  simp only [terms, List.map_cons, List.map_nil, xl_cons, xl_nil, xor_zero']
  ac_rfl

/-- `xor d d r` for each of `rest`, none of them `d`. -/
theorem xorsRest_ok (d : Reg) (rest : List Reg) (s : State) (acc : Word) (hr : ∀ r ∈ rest, r ≠ d)
    (hd : (s.gpr d).setWidth 32 = acc) :
    WP isa (.block (rest.map fun r => .logic .xor d d r)) s fun s' =>
      (s'.gpr d).setWidth 32 = acc ^^^ xl (rest.map fun r => (s.gpr r).setWidth 32) ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  induction rest generalizing s acc with
  | nil => exact WP.block_nil ⟨by simp [hd, xl], fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | cons r rs ih =>
    have rd := hr r List.mem_cons_self
    rw [List.map_cons, show ∀ (i : Instr) (l : List Instr), i :: l = [i] ++ l from fun _ _ => rfl,
      WP.block_append_iff]
    refine WP.mono (Q := fun s₁ => s₁ = s.write d (s.gpr d ^^^ s.gpr r)) ?_ fun s₁ e₁ => ?_
    · apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec_logic, Option.some.injEq, exists_eq_left']
    subst e₁
    refine WP.mono (ih (s.write d (s.gpr d ^^^ s.gpr r)) (acc ^^^ (s.gpr r).setWidth 32)
      (fun r' h => hr r' (List.mem_cons_of_mem _ h)) (by rw [RegUpd.gpr_write_self, lo32_xor, hd]))
      fun s₂ ⟨h₂, k₂, m₂, rd₂, wr₂, sp₂⟩ => ⟨?_, fun r' h => by rw [k₂ r' h, RegUpd.gpr_write_of_ne _ _ h],
        m₂, rd₂, wr₂, sp₂⟩
    rw [h₂, List.map_cons, xl_cons, BitVec.xor_assoc]
    refine congrArg (fun z => acc ^^^ ((s.gpr r).setWidth 32 ^^^ xl z)) (List.map_congr_left fun r' h => ?_)
    rw [RegUpd.gpr_write_of_ne _ _ (hr r' (List.mem_cons_of_mem _ h))]

/-- `xors` leaves the exclusive or of its registers' low words in `d`. -/
theorem xors_ok (d x y : Reg) (rest : List Reg) (s : State) (hr : ∀ r ∈ rest, r ≠ d) :
    WP isa (.block (xors d (x :: y :: rest))) s fun s' =>
      (s'.gpr d).setWidth 32 = xl ((x :: y :: rest).map fun r => (s.gpr r).setWidth 32) ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  rw [xors, show ∀ (i : Instr) (l : List Instr), i :: l = [i] ++ l from fun _ _ => rfl, WP.block_append_iff]
  refine WP.mono (Q := fun s₁ => s₁ = s.write d (s.gpr x ^^^ s.gpr y)) ?_ fun s₁ e₁ => ?_
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_logic, Option.some.injEq, exists_eq_left']
  subst e₁
  refine WP.mono (xorsRest_ok d rest _ ((s.gpr x).setWidth 32 ^^^ (s.gpr y).setWidth 32) hr
    (by rw [RegUpd.gpr_write_self, lo32_xor]))
    fun s₂ ⟨h₂, k₂, m₂, rd₂, wr₂, sp₂⟩ => ⟨?_, fun r' h => by rw [k₂ r' h, RegUpd.gpr_write_of_ne _ _ h],
      m₂, rd₂, wr₂, sp₂⟩
  rw [h₂, List.map_cons, List.map_cons, xl_cons, xl_cons, BitVec.xor_assoc]
  refine congrArg (fun z => (s.gpr x).setWidth 32 ^^^ ((s.gpr y).setWidth 32 ^^^ xl z))
    (List.map_congr_left fun r' h => ?_)
  rw [RegUpd.gpr_write_of_ne _ _ (hr r' h)]

theorem rotl_ok (d x : Reg) (s : State) (d1 : d ≠ T1) (x1 : x ≠ T1) :
    WP isa (.block (rotl d x 1)) s fun s' =>
      (s'.gpr d).setWidth 32 = ((s.gpr x).setWidth 32).rotateLeft 1 ∧
      (∀ r, r ≠ d → r ≠ T1 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  simp only [T1] at d1 x1 ⊢
  apply WP.of_runBlock
  simp only [rotl, T1, runBlock_cons, runStep_some, runBlock_nil, exec_logic, exec_shift_w (show 1 < 32 by decide),
    exec_shift_w (show 32 - 1 < 32 by decide), RegUpd.gpr_write, x1, Ne.symm d1, ↓reduceIte,
    Option.some.injEq, exists_eq_left']
  exact ⟨rotl_lo _ (by decide), fun r h1 h2 => by simp [h1, h2], rfl, rfl, rfl, rfl⟩

/-- The terms of the schedule are within the window, and all but the first
in other registers than `Wₜ`'s. -/
theorem terms_mem {t j : Nat} (ht : 16 ≤ t) (h : j ∈ terms t) : j < t ∧ t ≤ j + 16 := by
  simp only [terms, List.mem_cons, List.not_mem_nil, or_false] at h; omega

theorem vterms_tail {t j : Nat} (ht : 16 ≤ t) (h : j ∈ (vterms t).tail) : j % 16 ≠ t % 16 := by
  have h' : j ∈ (terms t).tail := ((List.filter_sublist).tail).subset h
  simp only [terms, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at h'; omega

theorem vterms_ne (t : Nat) (ht : 16 ≤ t) : vterms t ≠ [] := by
  intro h
  have : t - 3 ∈ vterms t ∨ t - 16 ∈ vterms t := by
    by_cases h19 : 19 ≤ t
    · left; simp [vterms, terms, isC]; omega
    · right; simp [vterms, terms, isC]; omega
  rw [h] at this; simp at this

theorem cterm_lt (t : Nat) : (cterm t).toNat < 2048 := by
  by_cases h : t < 32
  · have := (show ∀ t < 32, (cterm t).toNat < 2048 by decide) t h
    exact this
  · have e : (terms t).filter isC = [] := List.filter_eq_nil_iff.mpr fun j hj => by
      simp only [terms, List.mem_cons, List.not_mem_nil, or_false] at hj
      simp only [isC, Bool.and_eq_true, decide_eq_true_eq]; omega
    simp [cterm, e]

theorem lo32_imm (c : Word) : (BitVec.ofInt 64 (c.toNat : Int)).setWidth 32 = c := by
  apply BitVec.eq_of_toNat_eq
  simp

section
variable {L : Lay} (hL : LayOk L)
include hL

/-- A step of the schedule, with the words `Wₜ₋₁₆ … Wₜ₋₁` but the padding's
in their registers: `Wₜ` in `Wₜ₋₁₆`'s, and the registers but that one and
`T1` kept. -/
theorem sched_ok (x : HashValue) (t : Nat) (ht : 16 ≤ t) (s : State)
    (hw : ∀ j, j < t → t ≤ j + 16 → isC j = false → (s.gpr (L.wr j)).setWidth 32 = W (blk x) j) :
    WP isa (.block (sched L t)) s fun s' =>
      (s'.gpr (L.wr t)).setWidth 32 = W (blk x) t ∧ (∀ r, r ≠ L.wr t → r ≠ T1 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have d1 := (hL.wsp _ (wr_mem hL t)).2.1
  have hv (j : Nat) (hj : j ∈ vterms t) : (s.gpr (L.wr j)).setWidth 32 = W (blk x) j := by
    have := List.mem_filter.mp hj
    exact hw j (terms_mem ht this.1).1 (terms_mem ht this.1).2 (by simpa using this.2)
  -- The words in registers, rotated.
  have hx : WP isa (.block (match (vterms t).map L.wr with
      | [x] => rotl (L.wr t) x 1
      | rs => xors (L.wr t) rs ++ rotl (L.wr t) (L.wr t) 1)) s fun s' =>
      (s'.gpr (L.wr t)).setWidth 32 = (xl ((vterms t).map (W (blk x)))).rotateLeft 1 ∧
      (∀ r, r ≠ L.wr t → r ≠ T1 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
    have hne := vterms_ne t ht
    have hvt := hv
    have htl := fun j => vterms_tail (t := t) (j := j) ht
    generalize vterms t = vt at hne hvt htl
    match vt, hne with
    | [j], _ =>
      simp only [List.map_cons, List.map_nil]
      refine WP.mono (rotl_ok _ _ s d1 (hL.wsp _ (wr_mem hL j)).2.1) fun s' ⟨h, k, m, rd, wr, sp⟩ => ⟨?_, k, m, rd, wr, sp⟩
      rw [h, hvt j List.mem_cons_self]; simp [xl]
    | j₀ :: j₁ :: rest, _ =>
      simp only [List.map_cons]
      rw [WP.block_append_iff]
      refine WP.mono (xors_ok _ _ _ (rest.map L.wr) s fun r hr => ?_) fun s₁ ⟨h₁, k₁, m₁, rd₁, wr₁, sp₁⟩ => ?_
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
        exact wr_ne hL (htl j (List.mem_cons_of_mem _ hj))
      refine WP.mono (rotl_ok _ _ s₁ d1 d1) fun s₂ ⟨h₂, k₂, m₂, rd₂, wr₂, sp₂⟩ =>
        ⟨?_, fun r h h' => by rw [k₂ r h h', k₁ r h], by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁],
          by rw [sp₂, sp₁]⟩
      rw [h₂, h₁]
      show (xl (((j₀ :: j₁ :: rest).map L.wr).map fun r => (s.gpr r).setWidth 32)).rotateLeft 1 = _
      rw [List.map_map]
      exact congrArg (fun z => (xl z).rotateLeft 1) (List.map_congr_left fun j hj => hvt j hj)
  unfold sched
  rw [WP.block_append_iff]
  refine WP.mono hx fun s₁ ⟨h₁, k₁, m₁, rd₁, wr₁, sp₁⟩ => ?_
  by_cases hc : cterm t = 0
  · simp only [hc, ↓reduceIte]
    exact WP.block_nil ⟨by rw [h₁, W_split x ht, hc, xor_zero'], k₁, m₁, rd₁, wr₁, sp₁⟩
  · simp only [hc, ↓reduceIte]
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil,
      exec_logicImm (show imm12 ((cterm t).toNat : Int) by have := cterm_lt t; constructor <;> omega),
      Option.some.injEq, exists_eq_left']
    refine ⟨?_, fun r h h' => by rw [RegUpd.gpr_write_of_ne _ _ h, k₁ r h h'], m₁, rd₁, wr₁, sp₁⟩
    rw [RegUpd.gpr_write_self, lo32_xor, h₁, lo32_imm _, W_split x ht]

/-! ## The rounds -//-! ## The rounds -/

theorem step_ok (H x : HashValue) (s₀ : State) (t : Nat) (s : State) (h : RInv L H (blk x) s₀ t s) :
    WP isa (.block (step L t)) s (RInv L H (blk x) s₀ (t + 1)) := by
  -- The schedule.
  unfold step
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (Q := fun (s₁ : State) => (isC t = false → (s₁.gpr (L.wr t)).setWidth 32 = W (blk x) t) ∧
    (∀ r, r ≠ L.wr t → r ≠ T1 → s₁.gpr r = s.gpr r) ∧
    s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.sp = s.sp) ?_ fun s₁ ⟨w₁, k₁, m₁, rd₁, wr₁, sp₁⟩ => ?_
  · by_cases ht : 16 ≤ t
    · simp only [ht, ite_true]
      exact WP.mono (sched_ok hL x t ht s fun j hj hj' hc => h.win j (by omega) hj' hc)
        fun s' ⟨w, k⟩ => ⟨fun _ => w, k⟩
    · simp only [ht, ite_false]
      exact WP.block_nil ⟨fun hc => h.win t (by omega) (by omega) hc, fun _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
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
  have hv₁ : Vars L t s₂ (Spec.Sha1.rounds H (blk x) t) := by
    have hv := h.vars
    have e : ∀ k, k < 5 → s₂.gpr (L.var t k) = s.gpr (L.var t k) := fun k hk => by
      have sp := hL.vsp _ (var_mem hL t k hk)
      rw [k₂ _ sp.1, k₁ _ (var_wr hL t k t hk) sp.2.1]
    simp only [Vars, e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e 4 (by decide)] at hv ⊢
    exact hv
  have hw₂ : isC t = false → (s₂.gpr (L.wr t)).setWidth 32 = W (blk x) t := fun hc => by
    rw [k₂ _ fun e => (hL.wsp _ (wr_mem hL t)).1 e]; exact w₁ hc
  refine WP.mono (round_ok hL t s₂ _ _ hv₁ hw₂ (fun hc => blk_c x hc) (fun _ => kv₂))
    fun s₃ ⟨hv₃, k₃, m₃, rd₃, wr₃, sp₃⟩ => ?_
  have wkeep (r : Reg) (hw : r ∈ L.w) : s₃.gpr r = s₂.gpr r :=
    k₃ r (fun hv => hL.vw r hv hw) (hL.wsp r hw).2.1
  refine ⟨?_, fun j hj hj' hc => ?_, fun hk => ?_, fun r hr => ?_, by rw [m₃, m₂, m₁, h.mem],
    by rw [rd₃, rd₂, rd₁, h.rd], by rw [wr₃, wr₂, wr₁, h.wr], by rw [sp₃, sp₂, sp₁, h.sp]⟩
  · rw [rounds_succ, round_eq]; exact hv₃
  · rw [wkeep _ (wr_mem hL j), k₂ _ fun e => (hL.wsp _ (wr_mem hL j)).1 e]
    by_cases hjt : j = t
    · subst hjt; exact w₁ hc
    · rw [k₁ _ (wr_ne hL (by omega)) (hL.wsp _ (wr_mem hL j)).2.1]
      exact h.win j (by omega) (by omega) hc
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
  refine WP.mono (load_ok hL s H hB hal hin hH) fun s₂ ⟨hv₂, k₂, m₂, rd₂, wr₂, sp₂⟩ => ?_
  rw [WP.block_append_iff]
  have w₂ : ∀ j < 16, isC j = false → (s₂.gpr (L.wr j)).setWidth 32 = W (blk x) j := fun j hj hc => by
    have h5 : j < 5 := by simp [isC] at hc; omega
    rw [k₂ _ (fun e => hL.vw _ e (wr_mem hL j)) (hL.wsp _ (wr_mem hL j)).2.1, hx j h5, blk_lt x h5,
      getElem!_pos x j h5]
  refine WP.mono (wp_range_flatMap (M := isa) (RInv L H (blk x) s₂) (fun t s' _ h => step_ok hL H x s₂ t s' h)
    80 (Nat.le_refl _) s₂ ⟨by rw [rounds_zero]; exact hv₂, fun j hj _ hc => w₂ j (by omega) hc,
      fun h => absurd rfl h, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩) fun s₃ h₃ => ?_
  have hb₃ : s₃.gpr B = bv := by
    rw [h₃.keep _ (by simp only [Clob, not_or]; exact ⟨fun e => (hL.vsp _ e).2.2.1 rfl,
      fun e => (hL.wsp _ e).2.2.1 rfl, by decide, by decide⟩), k₂ _ (fun e => (hL.vsp _ e).2.2.1 rfl) (by decide),
      hB]
  have rdwr₃ : s₃.rd ++ s₃.wr = s.rd ++ s.wr := by rw [h₃.rd, h₃.wr, rd₂, wr₂]
  have hv₃ : ∀ k < 5, (s₃.gpr (L.var 0 k)).setWidth 32 = (Spec.Sha1.rounds H (blk x) 80)[k]! := by
    obtain ⟨v0, v1, v2, v3, v4⟩ := h₃.vars
    intro k hk
    rw [getElem!_pos _ k hk]
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 by omega) with rfl | rfl | rfl | rfl | rfl
    exacts [(congrArg (BitVec.setWidth 32) v0).trans (dbl_lo _),
      (congrArg (BitVec.setWidth 32) v1).trans (dbl_lo _), v2, v3, v4]
  refine WP.mono (addH_ok hL s₃ _ H hb₃ hal (fun k hk => by rw [rdwr₃]; exact hin k hk)
    (fun k hk => by rw [h₃.mem, m₂]; exact hH k hk) hv₃) fun s₄ h₄ => ?_
  refine ⟨fun k hk => ?_, fun r hr => ?_, by rw [h₄.mem, h₃.mem, m₂], by rw [h₄.rd, h₃.rd, rd₂],
    by rw [h₄.wr, h₃.wr, wr₂], by rw [h₄.sp, h₃.sp, sp₂]⟩
  · rw [h₄.done k hk, getElem!_pos _ k hk, getElem!_pos _ k hk, getElem!_pos _ k hk]
    simp only [compress, Vector.getElem_zipWith]
  · simp only [Clob, not_or] at hr
    obtain ⟨hv, hw, hk, h1⟩ := hr
    rw [h₄.keep r hv h1, h₃.keep r (by simp only [Clob, not_or]; exact ⟨hv, hw, hk, h1⟩), k₂ r hv h1]

end

end VG.Proof.Pbkdf2.Sha1.RISCV64
