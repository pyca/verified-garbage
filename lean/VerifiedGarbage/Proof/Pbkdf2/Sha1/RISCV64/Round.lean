module

public import VerifiedGarbage.Impl.Pbkdf2.Sha1.RISCV64
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Sha1.Spec
public import VerifiedGarbage.TCB.RISCV64.Isa
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import Mathlib.Tactic.SplitIfs

/-!
# PBKDF2-HMAC-SHA-1's iteration on RISC-V: a round and a step of the schedule

Untrusted: everything here is checked by Lean. As for SHA-1's compression
function (`Proof/Sha1/RISCV64/Rounds.lean`), each round is symbolically
executed once, for any registers: `Wₜ` added into `e` (`wadd_ok`), then
`f(b, c, d)` (`fadd_ok`, once per function), then the rest (`tail_ok`).
The registers are those of a layout `Lay` whose facts (`LayOk`, decided
for the inner and the outer compression) keep them apart; the words are
the low 32 bits of the registers (`Vars`). A step of the schedule
(`sched_ok`) updates `Wₜ₋₁₆`'s register to `Wₜ`.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Sha1.RISCV64

open VG VG.RISCV64 VG.Impl.Pbkdf2.Sha1.RISCV64
open VG.Spec.Sha1 (HashValue Word Block K W f)
open VG.Proof.Sha1 (roundKW W_ge ch_eq)

/-! ## Layouts -/

/-- Variable `k`'s register in rounds `t` with `t % 5 = c`. -/
abbrev varAt (L : Lay) (c k : Nat) : Reg := L.vs.getD ((k + 5 - c) % 5) .t0

/-- What the proofs need of a layout's registers: the working variables and
the window apart from each other and from `KR`, `T1` and the loop's
registers, and the hash value within reach. -/
structure LayOk (L : Lay) : Prop where
  vmem : ∀ c < 5, ∀ k < 5, varAt L c k ∈ L.vs
  wmem : ∀ j < 16, L.w.getD j .t0 ∈ L.w
  vne : ∀ c < 5, ∀ k < 5, ∀ k' < 5, k ≠ k' → varAt L c k ≠ varAt L c k'
  wne : ∀ i < 16, ∀ j < 16, i ≠ j → L.w.getD i .t0 ≠ L.w.getD j .t0
  vw : ∀ r ∈ L.vs, r ∉ L.w
  vsp : ∀ r ∈ L.vs, r ≠ KR ∧ r ≠ T1 ∧ r ≠ B ∧ r ≠ N ∧ r ≠ TP
  wsp : ∀ r ∈ L.w, r ≠ KR ∧ r ≠ T1 ∧ r ≠ B ∧ r ≠ N ∧ r ≠ TP
  hO : L.hO + 20 ≤ 2048
  hal : L.hO % 4 = 0

theorem inner_ok : LayOk inner :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem outer_ok : LayOk outer :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

section
variable {L : Lay} (hL : LayOk L)
include hL

theorem var_mem (t k : Nat) (hk : k < 5) : L.var t k ∈ L.vs := hL.vmem _ (Nat.mod_lt _ (by decide)) k hk

theorem wr_mem (j : Nat) : L.wr j ∈ L.w := hL.wmem _ (Nat.mod_lt _ (by decide))

theorem var_ne {t k k' : Nat} (hk : k < 5) (hk' : k' < 5) (h : k ≠ k') : L.var t k ≠ L.var t k' :=
  hL.vne _ (Nat.mod_lt _ (by decide)) k hk k' hk' h

theorem wr_ne {i j : Nat} (h : i % 16 ≠ j % 16) : L.wr i ≠ L.wr j :=
  hL.wne _ (Nat.mod_lt _ (by decide)) _ (Nat.mod_lt _ (by decide)) h

theorem var_wr (t k j : Nat) (hk : k < 5) : L.var t k ≠ L.wr j := fun e =>
  hL.vw _ (var_mem hL t k hk) (e ▸ wr_mem hL j)

end

/-- The working variables move one register along each round. -/
theorem var_succ (L : Lay) (t k : Nat) (hk : k < 4) : L.var (t + 1) (k + 1) = L.var t k := by
  simp only [Lay.var]; congr 1; omega

theorem var_succ_zero (L : Lay) (t : Nat) : L.var (t + 1) 0 = L.var t 4 := by
  simp only [Lay.var]; congr 1; omega

/-- The working variables `v` are in the low 32 bits of the registers of round `t`. -/
def Vars (L : Lay) (t : Nat) (s : State) (v : HashValue) : Prop :=
  (s.gpr (L.var t 0)).setWidth 32 = v[0] ∧ (s.gpr (L.var t 1)).setWidth 32 = v[1] ∧
  (s.gpr (L.var t 2)).setWidth 32 = v[2] ∧ (s.gpr (L.var t 3)).setWidth 32 = v[3] ∧
  (s.gpr (L.var t 4)).setWidth 32 = v[4]

/-! ## Bit vectors -/

/-- A rotation left as its two halves, which have no bit in common. -/
theorem rotl_add (y : Word) {n : Nat} (hn : n < 32) : y <<< n + y >>> (32 - n) = y.rotateLeft n := by
  rw [BitVec.add_eq_or_of_and_eq_zero, rotl_shifts _ hn]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero]
  by_cases h : i < n
  · simp [h]
  · simp [h, BitVec.getLsbD_of_ge y (32 - n + i) (by omega)]

/-- A rotation left, as `rotl` computes it in the low word. -/
theorem rotl_lo (y : Word) {n : Nat} (hn : n < 32) :
    (sext32 (y >>> (32 - n)) ||| sext32 (y <<< n)).setWidth 32 = y.rotateLeft n := by
  rw [lo32_or, lo32_sext, lo32_sext, BitVec.or_comm, rotl_shifts _ hn]

/-- `fₜ` as the code adds it. -/
def fval : Fn → Word → Word → Word → Word
  | .ch, x, y, z => (y ^^^ z) &&& x ^^^ z
  | .parity, x, y, z => x ^^^ y ^^^ z
  | .maj, x, y, z => (x &&& y) + (z &&& (x ^^^ y))

theorem maj_add (x y z : Word) : (x &&& y) + (z &&& (x ^^^ y)) = Spec.Sha1.maj x y z := by
  rw [BitVec.add_eq_or_of_and_eq_zero]
  · ext i hi; simp only [Spec.Sha1.maj, BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_xor]
    cases x[i] <;> cases y[i] <;> cases z[i] <;> rfl
  · ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_xor, BitVec.getElem_zero]
    cases x[i] <;> cases y[i] <;> cases z[i] <;> rfl

theorem f_eq (t : Nat) (x y z : Word) : f t x y z = fval (fn t) x y z := by
  unfold Spec.Sha1.f fn
  split_ifs <;> simp only [fval, ch_eq, maj_add, Spec.Sha1.parity]

/-! ## A round -/

/-- What a piece of a round keeps: the registers but `e`, `b` and `T1`, and the rest. -/
structure Keeps (e b : Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ≠ e → r ≠ b → r ≠ T1 → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem wadd_ok {e w : Reg} (s : State) {z x : Word} (he : (s.gpr e).setWidth 32 = z)
    (hw : (s.gpr w).setWidth 32 = x) :
    WP isa (.block [.add e e w]) s fun s' => (s'.gpr e).setWidth 32 = z + x ∧ Keeps e e s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_add, Option.some.injEq, exists_eq_left']
  refine ⟨by rw [RegUpd.gpr_write_self, lo32_add, he, hw], fun r h _ _ => RegUpd.gpr_write_of_ne _ _ h,
    rfl, rfl, rfl, rfl⟩

theorem fadd_ok (g : Fn) {b c d e : Reg} (s : State) {x y z u : Word}
    (b1 : b ≠ T1) (c1 : c ≠ T1) (d1 : d ≠ T1) (e1 : e ≠ T1) (eb : e ≠ b) (ec : e ≠ c) (ed : e ≠ d)
    (hb : (s.gpr b).setWidth 32 = x) (hc : (s.gpr c).setWidth 32 = y) (hd : (s.gpr d).setWidth 32 = z)
    (he : (s.gpr e).setWidth 32 = u) :
    WP isa (.block (fadd g b c d e)) s fun s' =>
      (s'.gpr e).setWidth 32 = u + fval g x y z ∧ Keeps e e s s' := by
  simp only [T1] at b1 c1 d1 e1 ⊢
  apply WP.of_runBlock
  cases g
  · simp only [fadd, T1, runBlock_cons, runStep_some, runBlock_nil, exec_logic, exec_add, RegUpd.gpr_write,
      b1, d1, e1, ↓reduceIte, Option.some.injEq, exists_eq_left']
    refine ⟨?_, fun r h1 _ h3 => by simp only [T1] at h3; simp [RegUpd.gpr_write, h1, h3], rfl, rfl, rfl, rfl⟩
    simp only [lo32_add, lo32_xor, lo32_and, hb, hc, hd, he, fval]
  · simp only [fadd, T1, runBlock_cons, runStep_some, runBlock_nil, exec_logic, exec_add, RegUpd.gpr_write,
      d1, e1, ↓reduceIte, Option.some.injEq, exists_eq_left']
    refine ⟨?_, fun r h1 _ h3 => by simp only [T1] at h3; simp [RegUpd.gpr_write, h1, h3], rfl, rfl, rfl, rfl⟩
    simp only [lo32_add, lo32_xor, hb, hc, hd, he, fval]
  · simp only [fadd, T1, runBlock_cons, runStep_some, runBlock_nil, exec_logic, exec_add, RegUpd.gpr_write,
      b1, c1, d1, e1, Ne.symm eb, Ne.symm ec, Ne.symm ed, ↓reduceIte, Option.some.injEq, exists_eq_left']
    refine ⟨?_, fun r h1 _ h3 => by simp only [T1] at h3; simp [RegUpd.gpr_write, h1, h3], rfl, rfl, rfl, rfl⟩
    simp only [lo32_add, lo32_xor, lo32_and, hb, hc, hd, he, fval, BitVec.add_assoc]
    rw [BitVec.and_comm (x ^^^ y) z]

/-- The instructions of a round after `f(b, c, d)`. -/
def tailI (a b e : Reg) : List Instr :=
  ([.add e e KR, .shift .sll .w T1 a 5, .add e e T1, .shift .srl .w T1 a 27, .add e e T1] : List Instr) ++
    rotl b b 30

theorem tail_ok {a b e : Reg} (s : State) {x y z k : Word}
    (a1 : a ≠ T1) (b1 : b ≠ T1) (e1 : e ≠ T1) (eb : e ≠ b) (ea : e ≠ a)
    (ha : (s.gpr a).setWidth 32 = x) (hb : (s.gpr b).setWidth 32 = y) (he : (s.gpr e).setWidth 32 = z)
    (hk : (s.gpr KR).setWidth 32 = k) :
    WP isa (.block (tailI a b e)) s fun s' =>
      (s'.gpr e).setWidth 32 = z + k + x.rotateLeft 5 ∧ (s'.gpr b).setWidth 32 = y.rotateLeft 30 ∧
      Keeps e b s s' := by
  simp only [T1, KR] at a1 b1 e1 hk ⊢
  apply WP.of_runBlock
  simp only [tailI, rotl, T1, KR, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec_add, exec_logic, exec_shift_w (show 5 < 32 by decide), exec_shift_w (show 27 < 32 by decide),
    exec_shift_w (show 30 < 32 by decide), exec_shift_w (show 32 - 30 < 32 by decide),
    RegUpd.gpr_write, a1, b1, e1, Ne.symm b1, Ne.symm ea, Ne.symm eb, eb, ↓reduceIte, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, ?_, ⟨fun r h1 h2 h3 => by simp only [T1] at h3; simp [RegUpd.gpr_write, h1, h2, h3], rfl, rfl, rfl, rfl⟩⟩
  · simp only [lo32_add, lo32_sext, ha, he, hk, BitVec.add_assoc, rotl_add x (show 5 < 32 by decide)]
  · rw [rotl_lo _ (by decide), hb]

theorem round_split (L : Lay) (t : Nat) :
    round L t = ([.add (L.var t 4) (L.var t 4) (L.wr t)] : List Instr) ++
      (fadd (fn t) (L.var t 1) (L.var t 2) (L.var t 3) (L.var t 4) ++ tailI (L.var t 0) (L.var t 1) (L.var t 4)) := by
  simp only [Impl.Pbkdf2.Sha1.RISCV64.round, tailI, List.append_assoc]

/-- Round `t`, with `Wₜ` in its register and `Kₜ` in `KR`: the registers
but the working variables' and `T1` are kept. -/
theorem round_ok {L : Lay} (hL : LayOk L) (t : Nat) (s : State) (v : HashValue) (w : Word)
    (hv : Vars L t s v) (hw : (s.gpr (L.wr t)).setWidth 32 = w) (hk : (s.gpr KR).setWidth 32 = K t) :
    WP isa (.block (round L t)) s fun s' =>
      Vars L (t + 1) s' (roundKW v (f t v[1] v[2] v[3]) (K t) w) ∧
      (∀ r, r ∉ L.vs → r ≠ T1 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hv
  have m0 := var_mem hL t 0 (by decide); have m1 := var_mem hL t 1 (by decide)
  have m2 := var_mem hL t 2 (by decide); have m3 := var_mem hL t 3 (by decide)
  have m4 := var_mem hL t 4 (by decide)
  have sp0 := hL.vsp _ m0; have sp1 := hL.vsp _ m1; have sp2 := hL.vsp _ m2
  have sp3 := hL.vsp _ m3; have sp4 := hL.vsp _ m4
  have n40 := var_ne hL (t := t) (show 4 < 5 by decide) (show 0 < 5 by decide) (by decide)
  have n41 := var_ne hL (t := t) (show 4 < 5 by decide) (show 1 < 5 by decide) (by decide)
  have n42 := var_ne hL (t := t) (show 4 < 5 by decide) (show 2 < 5 by decide) (by decide)
  have n43 := var_ne hL (t := t) (show 4 < 5 by decide) (show 3 < 5 by decide) (by decide)
  have n10 := var_ne hL (t := t) (show 1 < 5 by decide) (show 0 < 5 by decide) (by decide)
  have n12 := var_ne hL (t := t) (show 1 < 5 by decide) (show 2 < 5 by decide) (by decide)
  have n13 := var_ne hL (t := t) (show 1 < 5 by decide) (show 3 < 5 by decide) (by decide)
  have kw := (hL.wsp _ (wr_mem hL t)).1
  rw [round_split, WP.block_append_iff]
  refine WP.mono (wadd_ok s h4 hw) fun s₁ ⟨e₁, k₁⟩ => ?_
  have g₁ : ∀ k, k < 4 → s₁.gpr (L.var t k) = s.gpr (L.var t k) := fun k hk =>
    k₁.gpr _ (var_ne hL (by omega) (by decide) (by omega)) (var_ne hL (by omega) (by decide) (by omega))
      (hL.vsp _ (var_mem hL t k (by omega))).2.1
  rw [WP.block_append_iff]
  refine WP.mono (fadd_ok (fn t) s₁ (x := v[1]) (y := v[2]) (z := v[3]) sp1.2.1 sp2.2.1 sp3.2.1 sp4.2.1 n41 n42 n43
    (by rw [g₁ 1 (by decide)]; exact h1) (by rw [g₁ 2 (by decide)]; exact h2) (by rw [g₁ 3 (by decide)]; exact h3)
    e₁) fun s₂ ⟨e₂, k₂⟩ => ?_
  have g₂ : ∀ k, k < 4 → s₂.gpr (L.var t k) = s.gpr (L.var t k) := fun k hk => by
    rw [k₂.gpr _ (var_ne hL (by omega) (by decide) (by omega)) (var_ne hL (by omega) (by decide) (by omega))
      (hL.vsp _ (var_mem hL t k (by omega))).2.1, g₁ k hk]
  have hk₂ : (s₂.gpr KR).setWidth 32 = K t := by
    rw [k₂.gpr _ (Ne.symm sp4.1) (Ne.symm sp4.1) (by decide), k₁.gpr _ (Ne.symm sp4.1) (Ne.symm sp4.1) (by decide), hk]
  refine WP.mono (tail_ok s₂ (x := v[0]) (y := v[1]) sp0.2.1 sp1.2.1 sp4.2.1 n41 n40
    (by rw [g₂ 0 (by decide)]; exact h0) (by rw [g₂ 1 (by decide)]; exact h1) e₂ hk₂)
    fun s₃ ⟨e₃, b₃, k₃⟩ => ?_
  refine ⟨?_, fun r hr h1' => ?_, by rw [k₃.mem, k₂.mem, k₁.mem], by rw [k₃.rd, k₂.rd, k₁.rd],
    by rw [k₃.wr, k₂.wr, k₁.wr], by rw [k₃.sp, k₂.sp, k₁.sp]⟩
  · have hne (k : Nat) (hk : k < 5) (h4' : k ≠ 4) (h1'' : k ≠ 1) : s₃.gpr (L.var t k) = s.gpr (L.var t k) := by
      rw [k₃.gpr _ (var_ne hL hk (by decide) h4') (var_ne hL hk (by decide) h1'') (hL.vsp _ (var_mem hL t k hk)).2.1]
      exact g₂ k (by omega)
    simp only [Vars, var_succ_zero, var_succ L t _ (show 0 < 4 by omega), var_succ L t _ (show 1 < 4 by omega),
      var_succ L t _ (show 2 < 4 by omega), var_succ L t _ (show 3 < 4 by omega)]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [e₃, ← f_eq]; simp only [roundKW, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero]
      ac_rfl
    · rw [hne 0 (by decide) (by decide) (by decide), h0]; rfl
    · rw [b₃]; rfl
    · rw [hne 2 (by decide) (by decide) (by decide), h2]; rfl
    · rw [hne 3 (by decide) (by decide) (by decide), h3]; rfl
  · have hn : ∀ k, k < 5 → r ≠ L.var t k := fun k hk e => hr (e ▸ var_mem hL t k hk)
    rw [k₃.gpr r (hn 4 (by decide)) (hn 1 (by decide)) h1', k₂.gpr r (hn 4 (by decide)) (hn 4 (by decide)) h1',
      k₁.gpr r (hn 4 (by decide)) (hn 4 (by decide)) h1']

/-! ## The message schedule -/

/-- A step of the schedule, with `Wₜ₋₁₆ … Wₜ₋₁` in their registers: `Wₜ` in
`Wₜ₋₁₆`'s, and the registers but that one and `T1` kept. -/
theorem sched_ok {L : Lay} (hL : LayOk L) (M : Block) (t : Nat) (ht : 16 ≤ t) (s : State)
    (hw : ∀ j, j < t → t ≤ j + 16 → (s.gpr (L.wr j)).setWidth 32 = W M j) :
    WP isa (.block (sched L t)) s fun s' =>
      (s'.gpr (L.wr t)).setWidth 32 = W M t ∧ (∀ r, r ≠ L.wr t → r ≠ T1 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have e16 := hw (t - 16) (by omega) (by omega)
  have e14 := hw (t - 14) (by omega) (by omega)
  have e8 := hw (t - 8) (by omega) (by omega)
  have e3 := hw (t - 3) (by omega) (by omega)
  have w16 : L.wr (t - 16) = L.wr t := by simp only [Lay.wr]; congr 1; omega
  have w14 : L.wr (t - 14) = L.wr (t + 2) := by simp only [Lay.wr]; congr 1; omega
  have w8 : L.wr (t - 8) = L.wr (t + 8) := by simp only [Lay.wr]; congr 1; omega
  have w3 : L.wr (t - 3) = L.wr (t + 13) := by simp only [Lay.wr]; congr 1; omega
  rw [w16] at e16; rw [w14] at e14; rw [w8] at e8; rw [w3] at e3
  have d8 := wr_ne hL (i := t) (j := t + 8) (by omega)
  have d13 := wr_ne hL (i := t) (j := t + 13) (by omega)
  have t0 := (hL.wsp _ (wr_mem hL t)).2.1
  have t2 := (hL.wsp _ (wr_mem hL (t + 2))).2.1
  have t8 := (hL.wsp _ (wr_mem hL (t + 8))).2.1
  have t13 := (hL.wsp _ (wr_mem hL (t + 13))).2.1
  simp only [T1] at t0 t2 t8 t13 ⊢
  apply WP.of_runBlock
  simp only [sched, rotl, T1, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec_logic, exec_shift_w (show 1 < 32 by decide), exec_shift_w (show 32 - 1 < 32 by decide),
    RegUpd.gpr_write, t0, Ne.symm t0, Ne.symm d8, Ne.symm d13, ↓reduceIte, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, fun r h1 h2 => by simp [h1, h2], rfl, rfl, rfl, rfl⟩
  rw [rotl_lo _ (by decide), lo32_xor, lo32_xor, lo32_xor, e16, e14, e8, e3, W_ge M ht]
  congr 1
  ac_rfl

end VG.Proof.Pbkdf2.Sha1.RISCV64
