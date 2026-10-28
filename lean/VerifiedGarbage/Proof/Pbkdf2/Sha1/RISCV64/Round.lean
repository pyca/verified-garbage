module

public import VerifiedGarbage.Impl.Pbkdf2.Sha1.RISCV64
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Sha1.Spec
public import VerifiedGarbage.TCB.RISCV64.Isa
public import VerifiedGarbage.Proof.Framework.RISCV64.Double
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import Mathlib.Tactic.SplitIfs

/-!
# PBKDF2-HMAC-SHA-1's iteration on RISC-V: a round and a step of the schedule

Untrusted: everything here is checked by Lean. As for SHA-1's compression
function (`Proof/Sha1/RISCV64/Rounds.lean`), each round is symbolically
executed once, for any registers: `Wₜ + Kₜ` added into `e` (`wk_ok`, by
the four forms of `wk`), then `f(b, c, d)` (`fadd_ok`, once per function),
then the rest (`tail_ok`). The registers are those of a layout `Lay` whose
facts (`LayOk`, decided for the inner and the outer compression) keep them
apart; the words are the low 32 bits of the registers, and `a` and `b` are
doubled, a word in both halves of its register (`Vars`, `dbl`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Sha1.RISCV64

open VG VG.RISCV64 VG.Impl.Pbkdf2.Sha1.RISCV64
open VG.Spec.Sha1 (HashValue Word Block K W f)
open VG.Proof.Sha1 (roundKW ch_eq)
open VG.RISCV64.ByteLoad (li32_ok)

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

/-- The working variables `v` in the registers of round `t`: `a` and `b`
doubled, and `c`, `d` and `e` in the low 32 bits. -/
def Vars (L : Lay) (t : Nat) (s : State) (v : HashValue) : Prop :=
  s.gpr (L.var t 0) = dbl v[0] ∧ s.gpr (L.var t 1) = dbl v[1] ∧
  (s.gpr (L.var t 2)).setWidth 32 = v[2] ∧ (s.gpr (L.var t 3)).setWidth 32 = v[3] ∧
  (s.gpr (L.var t 4)).setWidth 32 = v[4]

/-! ## Bit vectors -/

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

/-- `Wₜ + Kₜ` added into `e`, `Wₜ` in its register unless it is a padding
word, and `Kₜ` in `KR` unless `t = 5`. -/
theorem wk_ok (L : Lay) (t : Nat) {e : Reg} (s : State) {z w : Word} (e1 : e ≠ T1) (ek : e ≠ KR)
    (he : (s.gpr e).setWidth 32 = z) (hw : isC t = false → (s.gpr (L.wr t)).setWidth 32 = w)
    (hc : isC t = true → w = cval t) (hk : t ≠ 5 → (s.gpr KR).setWidth 32 = K t) :
    WP isa (.block (wk L t e)) s fun s' => (s'.gpr e).setWidth 32 = z + w + K t ∧ Keeps e e s s' := by
  simp only [T1, KR] at e1 ek hk ⊢
  unfold wk
  by_cases h5 : t = 5
  · subst h5
    simp only [↓reduceIte]
    rw [WP.block_append_iff]
    refine WP.mono (li32_ok (d := T1) _) fun s₁ e₁ => ?_
    subst e₁
    apply WP.of_runBlock
    simp only [T1, runBlock_cons, runStep_some, runBlock_nil, exec_add, RegUpd.gpr_write, e1, ↓reduceIte,
      Option.some.injEq, exists_eq_left']
    refine ⟨?_, fun r h _ h1 => ?_, rfl, rfl, rfl, rfl⟩
    · rw [lo32_add, he, lo32_sext, hc rfl, cval]
      simp only [↓reduceIte, BitVec.add_assoc, BitVec.add_comm (K 5)]
    · simp only [T1] at h1; simp [RegUpd.gpr_write, h, h1]
  have hk' := hk h5
  by_cases h15 : t = 15
  · subst h15
    simp only [show (15 : Nat) ≠ 5 by decide, ↓reduceIte]
    apply WP.of_runBlock
    simp only [KR, runBlock_cons, runStep_some, runBlock_nil, exec_add, exec_addi (show imm12 672 by decide),
      RegUpd.gpr_write, Ne.symm ek, ↓reduceIte, Option.some.injEq, exists_eq_left']
    refine ⟨?_, fun r h _ _ => by simp [RegUpd.gpr_write, h], rfl, rfl, rfl, rfl⟩
    rw [lo32_add, lo32_add, he, hk', hc rfl]
    rfl
  simp only [h5, h15, ↓reduceIte]
  cases hC : isC t
  · simp only [Bool.false_eq_true, ↓reduceIte]
    apply WP.of_runBlock
    simp only [KR, runBlock_cons, runStep_some, runBlock_nil, exec_add, RegUpd.gpr_write, Ne.symm ek, ↓reduceIte,
      Option.some.injEq, exists_eq_left']
    refine ⟨?_, fun r h _ _ => by simp [RegUpd.gpr_write, h], rfl, rfl, rfl, rfl⟩
    rw [lo32_add, lo32_add, he, hw hC, hk']
  · simp only [↓reduceIte]
    apply WP.of_runBlock
    simp only [KR, runBlock_cons, runStep_some, runBlock_nil, exec_add, Option.some.injEq, exists_eq_left']
    refine ⟨?_, fun r h _ _ => RegUpd.gpr_write_of_ne _ _ h, rfl, rfl, rfl, rfl⟩
    rw [RegUpd.gpr_write_self, lo32_add, he, hk', hc hC, cval]
    simp only [h5, h15, ↓reduceIte]; exact congrArg (· + K t) (BitVec.add_zero z).symm

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

/-- The rest of a round, with `a` and `b` doubled: `e` gets `ROTL⁵(a)` and
is doubled, and `b` is rotated. -/
theorem tail_ok {a b e : Reg} (s : State) {x y z : Word} (b1 : b ≠ T1) (e1 : e ≠ T1) (eb : e ≠ b)
    (ha : s.gpr a = dbl x) (hb : s.gpr b = dbl y) (he : (s.gpr e).setWidth 32 = z) :
    WP isa (.block (tail a b e)) s fun s' =>
      s'.gpr e = dbl (z + x.rotateLeft 5) ∧ (s'.gpr b).setWidth 32 = y.rotateLeft 30 ∧ Keeps e b s s' := by
  simp only [T1] at b1 e1 ⊢
  apply WP.of_runBlock
  simp only [tail, T1, runBlock_cons, runStep_some, runBlock_nil, exec_add, exec_logic,
    exec_shift_d (show 27 < 64 by decide), exec_shift_d (show 2 < 64 by decide),
    exec_shift_d (show 32 < 64 by decide), RegUpd.gpr_write, b1, e1, Ne.symm eb, eb, ↓reduceIte,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ⟨fun r h1 h2 h3 => by simp only [T1] at h3; simp [RegUpd.gpr_write, h1, h2, h3], rfl, rfl, rfl,
    rfl⟩⟩
  · rw [dbl_mk, lo32_add, he, ha, dbl_rot x 5 27 (by decide) (by decide)]
  · rw [hb, dbl_rot y 30 2 (by decide) (by decide)]

theorem round_split (L : Lay) (t : Nat) :
    round L t = wk L t (L.var t 4) ++
      (fadd (fn t) (L.var t 1) (L.var t 2) (L.var t 3) (L.var t 4) ++ tail (L.var t 0) (L.var t 1) (L.var t 4)) := by
  simp only [Impl.Pbkdf2.Sha1.RISCV64.round, List.append_assoc]

/-- Round `t`, with `Wₜ` in its register unless it is a padding word, and
`Kₜ` in `KR` unless `t = 5`: the registers but the working variables' and
`T1` are kept. -/
theorem round_ok {L : Lay} (hL : LayOk L) (t : Nat) (s : State) (v : HashValue) (w : Word)
    (hv : Vars L t s v) (hw : isC t = false → (s.gpr (L.wr t)).setWidth 32 = w)
    (hc : isC t = true → w = cval t) (hk : t ≠ 5 → (s.gpr KR).setWidth 32 = K t) :
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
  rw [round_split, WP.block_append_iff]
  refine WP.mono (wk_ok L t s sp4.2.1 sp4.1 h4 hw hc hk) fun s₁ ⟨e₁, k₁⟩ => ?_
  have g₁ : ∀ k, k < 4 → s₁.gpr (L.var t k) = s.gpr (L.var t k) := fun k hk =>
    k₁.gpr _ (var_ne hL (by omega) (by decide) (by omega)) (var_ne hL (by omega) (by decide) (by omega))
      (hL.vsp _ (var_mem hL t k (by omega))).2.1
  rw [WP.block_append_iff]
  refine WP.mono (fadd_ok (fn t) s₁ (x := v[1]) (y := v[2]) (z := v[3]) sp1.2.1 sp2.2.1 sp3.2.1 sp4.2.1 n41 n42 n43
    (by rw [g₁ 1 (by decide), h1, dbl_lo]) (by rw [g₁ 2 (by decide)]; exact h2)
    (by rw [g₁ 3 (by decide)]; exact h3) e₁) fun s₂ ⟨e₂, k₂⟩ => ?_
  have g₂ : ∀ k, k < 4 → s₂.gpr (L.var t k) = s.gpr (L.var t k) := fun k hk => by
    rw [k₂.gpr _ (var_ne hL (by omega) (by decide) (by omega)) (var_ne hL (by omega) (by decide) (by omega))
      (hL.vsp _ (var_mem hL t k (by omega))).2.1, g₁ k hk]
  refine WP.mono (tail_ok s₂ (x := v[0]) (y := v[1]) sp1.2.1 sp4.2.1 n41
    (by rw [g₂ 0 (by decide)]; exact h0) (by rw [g₂ 1 (by decide)]; exact h1) e₂)
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
      congr 1; ac_rfl
    · rw [hne 0 (by decide) (by decide) (by decide), h0]; rfl
    · rw [b₃]; rfl
    · rw [hne 2 (by decide) (by decide) (by decide), h2]; rfl
    · rw [hne 3 (by decide) (by decide) (by decide), h3]; rfl
  · have hn : ∀ k, k < 5 → r ≠ L.var t k := fun k hk e => hr (e ▸ var_mem hL t k hk)
    rw [k₃.gpr r (hn 4 (by decide)) (hn 1 (by decide)) h1', k₂.gpr r (hn 4 (by decide)) (hn 4 (by decide)) h1',
      k₁.gpr r (hn 4 (by decide)) (hn 4 (by decide)) h1']

end VG.Proof.Pbkdf2.Sha1.RISCV64
