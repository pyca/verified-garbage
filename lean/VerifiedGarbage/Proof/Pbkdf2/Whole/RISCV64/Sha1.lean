module

import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
import VerifiedGarbage.Proof.Sha1.RISCV64.Compress
meta import VerifiedGarbage.Proof.Sha1.RISCV64.Compress
public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Shared
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha1
public import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Shared
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha1
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Correct
public import VerifiedGarbage.Proof.Sha1.Md
public import VerifiedGarbage.Impl.Sha1.RISCV64
public import VerifiedGarbage.Impl.Sha1.RISCV64.Stream
import VerifiedGarbage.Proof.Sha1.RISCV64.Stream
import VerifiedGarbage.Proof.Hmac.Generic.Common
public import VerifiedGarbage.Spec.Pbkdf2.Generic
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Align
public import VerifiedGarbage.Impl.Pbkdf2.Sha1.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Sha1.StateMem
public import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Calls
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Hmac.Common
public import VerifiedGarbage.Proof.Pbkdf2.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Impl.Pbkdf2.Sha1.RISCV64
public import VerifiedGarbage.Proof.Pbkdf2.MdStep
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Sha1.Spec
public import VerifiedGarbage.TCB.RISCV64.Isa
public import VerifiedGarbage.Proof.Framework.RISCV64.Double

/-! ### `Pbkdf2.Sha1.RISCV64.Verified`, which only this module used -/

section

/-! ### `Pbkdf2.Sha1.RISCV64.Cmp`, which only this module used -/

section

/-! ### `Pbkdf2.Sha1.RISCV64.Round`, which this module and modules that import it used -/

section

/-!
# PBKDF2-HMAC-SHA-1's iteration on RISC-V: a round and a step of the schedule

Untrusted: everything here is checked by Lean. As for SHA-1's compression
function (`Proof/Sha1/RISCV64/Compress.lean`), each round is symbolically
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
  simp only [Lay.var]; congr 1; omega_using []

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
  (repeat' split) <;> simp only [fval, ch_eq, maj_add, Spec.Sha1.parity]

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
    k₁.gpr _ (var_ne hL (by omega_using [hk]) (by decide) (by omega_using [hk])) (var_ne hL (by omega_using [hk]) (by decide) (by omega_using [hk]))
      (hL.vsp _ (var_mem hL t k (by omega_using [hk]))).2.1
  rw [WP.block_append_iff]
  refine WP.mono (fadd_ok (fn t) s₁ (x := v[1]) (y := v[2]) (z := v[3]) sp1.2.1 sp2.2.1 sp3.2.1 sp4.2.1 n41 n42 n43
    (by rw [g₁ 1 (by decide), h1, dbl_lo]) (by rw [g₁ 2 (by decide)]; exact h2)
    (by rw [g₁ 3 (by decide)]; exact h3) e₁) fun s₂ ⟨e₂, k₂⟩ => ?_
  have g₂ : ∀ k, k < 4 → s₂.gpr (L.var t k) = s.gpr (L.var t k) := fun k hk => by
    rw [k₂.gpr _ (var_ne hL (by omega_using [hk]) (by decide) (by omega_using [hk])) (var_ne hL (by omega_using [hk]) (by decide) (by omega_using [hk]))
      (hL.vsp _ (var_mem hL t k (by omega_using [hk]))).2.1, g₁ k hk]
  refine WP.mono (tail_ok s₂ (x := v[0]) (y := v[1]) sp1.2.1 sp4.2.1 n41
    (by rw [g₂ 0 (by decide)]; exact h0) (by rw [g₂ 1 (by decide)]; exact h1) e₂)
    fun s₃ ⟨e₃, b₃, k₃⟩ => ?_
  refine ⟨?_, fun r hr h1' => ?_, by rw [k₃.mem, k₂.mem, k₁.mem], by rw [k₃.rd, k₂.rd, k₁.rd],
    by rw [k₃.wr, k₂.wr, k₁.wr], by rw [k₃.sp, k₂.sp, k₁.sp]⟩
  · have hne (k : Nat) (hk : k < 5) (h4' : k ≠ 4) (h1'' : k ≠ 1) : s₃.gpr (L.var t k) = s.gpr (L.var t k) := by
      rw [k₃.gpr _ (var_ne hL hk (by decide) h4') (var_ne hL hk (by decide) h1'') (hL.vsp _ (var_mem hL t k hk)).2.1]
      exact g₂ k (by omega_using [hk, h4'])
    simp only [Vars, var_succ_zero, var_succ L t _ (show 0 < 4 by omega_using []), var_succ L t _ (show 1 < 4 by omega_using []),
      var_succ L t _ (show 2 < 4 by omega_using []), var_succ L t _ (show 3 < 4 by omega_using [])]
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

end

end

/-! ### `Pbkdf2.Sha1Words`, which this module and modules that import it used -/

section

/-!
# PBKDF2-HMAC-SHA-1's iteration on words

Untrusted: everything here is checked by Lean. SHA-1's digest is its hash
value's words, big-endian, so the block a step compresses after a hash
value `x` (the `D = 20` bytes of a digest, then the padding of an 84-byte
message) is `x`'s words, `0x80000000`, nine zero words and the bit count
`672` (`blk`, `tailBlock_digest`). So one step of the iteration
(`Md.step`, `Proof/Pbkdf2/MdStep.lean`) on a digest is the digest of two
compressions of such blocks (`step_digest`), and the iteration on digests
is the digest of an iteration on hash values (`iterate_digest`), with `T`
updated by the words' XOR (`xorBytes_digest`). The digests of the arguments
are the big-endian words of their bytes (`digest_beWords`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Sha1Words

open VG.Spec.Sha1 (HashValue Word Block compress wordBytes parseBlock)
open VG.Proof.Sha1 (md)

/-- The block after the digest of `x`: its words, then SHA-1's padding of an
84-byte message. -/
def blk (x : HashValue) : Block := fun j =>
  if h : j.val < 5 then x[j.val] else if j.val = 5 then 0x80000000 else if j.val = 15 then 672 else 0

/-! ## Bytes and words -/

/-- The four bytes of a word, big-endian, make the word. -/
theorem be4 (x : Word) :
    (x.extractLsb' 24 8 ++ x.extractLsb' 16 8 ++ x.extractLsb' 8 8 ++ x.extractLsb' 0 8 : Word) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  rcases (show i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ (24 ≤ i ∧ i < 32) by omega_using [hi]) with h | h | h | h
  · simp [h]
  · simp only [show ¬ i < 8 by omega_using [h], show i - 8 < 8 by omega_using [h], ite_true, ite_false, decide_true, Bool.true_and]
    congr 1; omega_using [h]
  · simp only [show ¬ i < 8 by omega_using [h], show ¬ i - 8 < 8 by omega_using [h], show i - 8 - 8 < 8 by omega_using [h], ite_true,
      ite_false, decide_true, Bool.true_and]
    congr 1; omega_using [h]
  · simp only [show ¬ i < 8 by omega_using [h], show ¬ i - 8 < 8 by omega_using [h], show ¬ i - 8 - 8 < 8 by omega_using [h],
      show i - 8 - 8 - 8 < 8 by omega_using [hi], ite_false, decide_true, Bool.true_and]
    congr 1; omega_using [h]

/-- The bytes of a word made of four bytes. -/
theorem ex24 (a b c d : BitVec 8) : (a ++ b ++ c ++ d : Word).extractLsb' 24 8 = a := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
  simp only [show ¬ 24 + i < 8 by omega_using [], show ¬ 24 + i - 8 < 8 by omega_using [], show ¬ 24 + i - 8 - 8 < 8 by omega_using [],
    ite_false]
  congr 1; omega_using []

theorem ex16 (a b c d : BitVec 8) : (a ++ b ++ c ++ d : Word).extractLsb' 16 8 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
  simp only [show ¬ 16 + i < 8 by omega_using [], show ¬ 16 + i - 8 < 8 by omega_using [], show 16 + i - 8 - 8 < 8 by omega_using [hi],
    ite_false, ite_true]
  congr 1; omega_using []

theorem ex8 (a b c d : BitVec 8) : (a ++ b ++ c ++ d : Word).extractLsb' 8 8 = c := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
  simp only [show ¬ 8 + i < 8 by omega_using [], show 8 + i - 8 < 8 by omega_using [hi], ite_false, ite_true]
  congr 1; omega_using []

theorem ex0 (a b c d : BitVec 8) : (a ++ b ++ c ++ d : Word).extractLsb' 0 8 = d := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
  rw [Nat.zero_add]; simp [hi]

/-- The digest, word by word. -/
theorem digest_eq (x : HashValue) :
    md.digest x = wordBytes x[0] ++ wordBytes x[1] ++ wordBytes x[2] ++ wordBytes x[3] ++ wordBytes x[4] := by
  obtain ⟨⟨l⟩, hl⟩ := x
  match l, hl with
  | [a, b, c, d, e], _ => simp [md, wordBytes]

theorem take_digest (x : md.HV) : (md.digest x).take 20 = md.digest x :=
  List.take_of_length_le (Nat.le_of_eq (md.digest_length _))

/-- The five big-endian words of the 20 bytes at `p`. -/
def beWords (m : Mem) (p : Addr) : HashValue := Vector.ofFn fun k =>
  (m (p + BitVec.ofNat 64 (4 * k)) ++ m (p + BitVec.ofNat 64 (4 * k + 1)) ++ m (p + BitVec.ofNat 64 (4 * k + 2)) ++
    m (p + BitVec.ofNat 64 (4 * k + 3)) : Word)

theorem digest_beWords (m : Mem) (p : Addr) : md.digest (beWords m p) = Spec.Sha256.bytesAt m p 20 := by
  simp only [digest_eq, beWords, Vector.getElem_ofFn, wordBytes, ex24, ex16, ex8, ex0]
  simp [Spec.Sha256.bytesAt, List.range_succ]

/-! ## One step -/

theorem tailPad_eq : md.tailPad 20 = [0x80] ++ List.replicate 35 0 ++ [0, 0, 0, 0, 0, 0, 2, 0xa0] := by
  decide +kernel

/-- The block after the digest of `x`. -/
theorem tailBlock_digest (x : md.HV) : md.tailBlock 20 (md.digest x) = blk x := by
  unfold MdStream.Md.tailBlock
  rw [tailPad_eq, digest_eq x, show md.parse = parseBlock from rfl]
  simp only [wordBytes, List.cons_append, List.nil_append, List.replicate_succ, List.replicate_zero]
  funext j
  obtain ⟨j, hj⟩ := j
  simp only [parseBlock, blk]
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨
    j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 by omega_using [hj]) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [List.getD_cons_succ, List.getD_cons_zero, be4, Nat.reduceMul, Nat.reduceAdd, Nat.reduceLT,
    ↓reduceDIte, ↓reduceIte, Nat.reduceEqDiff] <;> decide

/-- One step on hash values: the inner compression, with `hi`, of the block
after `x`, then the outer one, with `ho`, of the block after that. -/
def wstep (hi ho x : HashValue) : HashValue := compress ho (blk (compress hi (blk x)))

theorem step_digest (hi ho x : HashValue) : md.step 20 hi ho (md.digest x) = md.digest (wstep hi ho x) := by
  unfold MdStream.Md.step
  rw [tailBlock_digest x, take_digest (md.compress hi (blk x)), tailBlock_digest, take_digest]
  rfl

/-! ## The iteration -/

/-- `n` steps on hash values from `U = x` and `T = y`: the final `T`. -/
def wIter (hi ho : HashValue) : Nat → HashValue → HashValue → HashValue
  | 0, _, y => y
  | n + 1, x, y => wIter hi ho n (wstep hi ho x) (Vector.zipWith (· ^^^ ·) y (wstep hi ho x))

theorem wordBytes_xor (a b : Word) :
    wordBytes (a ^^^ b) = List.zipWith (· ^^^ ·) (wordBytes a) (wordBytes b) := by
  simp [wordBytes, BitVec.extractLsb'_xor]

theorem xorBytes_digest (y x : HashValue) :
    Spec.Pbkdf2.xorBytes (md.digest y) (md.digest x) = md.digest (Vector.zipWith (· ^^^ ·) y x) := by
  simp only [digest_eq, Spec.Pbkdf2.xorBytes, Vector.getElem_zipWith, wordBytes_xor]
  simp [wordBytes]

theorem iterate_digest (hi ho : HashValue) (n : Nat) (x y : HashValue) :
    Spec.Pbkdf2.iterate (md.step 20 hi ho) n (md.digest x) (md.digest y) = md.digest (wIter hi ho n x y) := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih => simp only [Spec.Pbkdf2.iterate, wIter, step_digest, xorBytes_digest, ih]

end VG.Proof.Pbkdf2.Sha1Words

end

end

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
  (repeat' split) <;> first | rfl | omega_arith

/-- The block's words. -/
theorem blk_lt (x : HashValue) {j : Nat} (hj : j < 5) : W (blk x) j = x[j] := by
  rw [W_lt _ (by omega_using [hj])]; simp [blk, hj]

theorem blk_5 (x : HashValue) : W (blk x) 5 = 0x80000000 := by rw [W_lt _ (by decide)]; rfl
theorem blk_15 (x : HashValue) : W (blk x) 15 = 672 := by rw [W_lt _ (by decide)]; rfl
theorem blk_mid (x : HashValue) {j : Nat} (h₁ : 6 ≤ j) (h₂ : j < 15) : W (blk x) j = 0 := by
  rw [W_lt _ (by omega_using [h₂])]; simp [blk, show ¬ j < 5 by omega_using [h₁], show j ≠ 5 by omega_using [h₁], show j ≠ 15 by omega_using [h₂]]

/-- The padding's words are `cval`'s. -/
theorem blk_c (x : HashValue) {j : Nat} (h : isC j = true) : W (blk x) j = cval j := by
  simp only [isC, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases (show j = 5 ∨ (6 ≤ j ∧ j < 15) ∨ j = 15 by omega_using [h]) with rfl | h' | rfl
  · rw [blk_5]; rfl
  · rw [blk_mid x h'.1 h'.2]; simp [cval, show j ≠ 5 by omega_using [h'], show j ≠ 15 by omega_using [h']]
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
    ⟨fun _ h => absurd h (by omega_using []), fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  have m := var_mem hL 0 k hk
  have hb : s.gpr B = bv := by rw [h.keep _ fun e => (hL.vsp _ e).2.2.1 rfl, hB]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_w (s := s) (t := L.var 0 k) (show L.hO + 4 * k < 2048 by have := hL.hO; omega_using [hk, this])
      (by rw [hb]; exact al_add hal (by decide) (by have := hL.hal; omega_using [this]))
      (by rw [hb, h.rd, h.wr]; exact hin k hk),
    Option.some.injEq, exists_eq_left']
  refine ⟨fun j hj => ?_, fun r hr => ?_, h.mem, h.rd, h.wr, h.sp⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [RegUpd.gpr_write_of_ne _ _ (var_ne hL (by omega_arith) hk (by omega_using [hj]))]; exact h.vars j hj
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
  simp only [terms, List.mem_cons, List.not_mem_nil, or_false] at h; omega_using [ht, h]

theorem vterms_tail {t j : Nat} (ht : 16 ≤ t) (h : j ∈ (vterms t).tail) : j % 16 ≠ t % 16 := by
  have h' : j ∈ (terms t).tail := ((List.filter_sublist).tail).subset h
  simp only [terms, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at h'; omega_using [ht, h']

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
      simp only [isC, Bool.and_eq_true, decide_eq_true_eq]; omega_using [h, hj]
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
      exec_logicImm (show imm12 ((cterm t).toNat : Int) by have := cterm_lt t; constructor <;> omega_arith),
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
      exact WP.mono (sched_ok hL x t ht s fun j hj hj' hc => h.win j (by omega_using [hj]) hj' hc)
        fun s' ⟨w, k⟩ => ⟨fun _ => w, k⟩
    · simp only [ht, ite_false]
      exact WP.block_nil ⟨fun hc => h.win t (by omega_using [ht]) (by omega_using []) hc, fun _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
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
    · rw [k₁ _ (wr_ne hL (by omega_using [hj, hj', hjt])) (hL.wsp _ (wr_mem hL j)).2.1]
      exact h.win j (by omega_using [hj, hjt]) (by omega_using [hj']) hc
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
    ⟨fun _ h => absurd h (by omega_using []), fun _ _ _ => rfl, fun _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
  have m := var_mem hL 0 k hk
  have sp := hL.vsp _ m
  have hb : s.gpr B = bv := by
    rw [h.keep _ (fun e => (hL.vsp _ e).2.2.1 rfl) (by decide), hB]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_w (s := s) (t := T1) (show L.hO + 4 * k < 2048 by have := hL.hO; omega_using [hk, this])
      (by rw [hb]; exact al_add hal (by decide) (by have := hL.hal; omega_using [this]))
      (by rw [hb, h.rd, h.wr]; exact hin k hk),
    exec_add, Option.some.injEq, exists_eq_left']
  refine ⟨fun j hj => ?_, fun j hj hj' => ?_, fun r hr h1 => ?_, h.mem, h.rd, h.wr, h.sp⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [RegUpd.gpr_write_of_ne _ _ (var_ne hL (by omega_arith) hk (by omega_using [hj])),
        RegUpd.gpr_write_of_ne _ _ (hL.vsp _ (var_mem hL 0 j (by omega_arith))).2.1]
      exact h.done j hj
    · rw [RegUpd.gpr_write_self, lo32_add, RegUpd.gpr_write_of_ne _ _ sp.2.1, RegUpd.gpr_write_self, lo32_ext,
        h.todo j (Nat.le_refl _) hk, hV j hk, h.mem, hb, hH j hk]
  · rw [RegUpd.gpr_write_of_ne _ _ (var_ne hL hj' hk (by omega_using [hj])),
      RegUpd.gpr_write_of_ne _ _ (hL.vsp _ (var_mem hL 0 j hj')).2.1]
    exact h.todo j (by omega_using [hj]) hj'
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
    have h5 : j < 5 := by simp [isC] at hc; omega_using [hj, hc]
    rw [k₂ _ (fun e => hL.vw _ e (wr_mem hL j)) (hL.wsp _ (wr_mem hL j)).2.1, hx j h5, blk_lt x h5,
      getElem!_pos x j h5]
  refine WP.mono (wp_range_flatMap (M := isa) (RInv L H (blk x) s₂) (fun t s' _ h => step_ok hL H x s₂ t s' h)
    80 (Nat.le_refl _) s₂ ⟨by rw [rounds_zero]; exact hv₂, fun j hj _ hc => w₂ j (by omega_using [hj]) hc,
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
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 by omega_using [hk]) with rfl | rfl | rfl | rfl | rfl
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

end

end

/-! ### `Pbkdf2.Sha1.RISCV64.Fin`, which only this module used -/

section

/-! ### `Pbkdf2.Sha1.RISCV64.Pro`, which only this module used -/

section

/-! ### `Pbkdf2.Sha1.RISCV64.Loop`, which only this module used -/

section

/-! ### `Pbkdf2.Sha1.RISCV64.Frame`, which only this module used -/

section

/-! ### `Pbkdf2.RISCV64.Sha1`, which only this module used -/

section

/-!
# PBKDF2-HMAC-SHA-1 on RISC-V: `iterate`

The iteration over a Merkle–Damgård hash function (`Impl/Pbkdf2/RISCV64.lean`)
for SHA-1's sizes, compression function and digest code (`it`), and what its
proof needs of SHA-1 (`hashOkW`): the sizes and the precondition that
SHA-1's own iteration (`Proof/Pbkdf2/Sha1/RISCV64/`) shares with it.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.RISCV64.Sha1

open VG.RISCV64
open VG.Impl.Pbkdf2.RISCV64 (It padBE)

/-- SHA-1's parameters of the iteration. -/
def it : It where
  N := 20
  B := 64
  D := 20
  CW := 80
  cmpN := "vg_sha1_compress"
  cmpC := Impl.Sha1.RISCV64.compress
  out := Impl.Sha1.RISCV64.Stream.params.out
  pad := padBE 64 20 8

/-- What the proof needs of SHA-1, with `Wi` bytes of working space. -/
theorem hashOkW (Wi : Nat) (h₁ : 227 ≤ Wi) (h₂ : Wi ≤ 8192) :
    HashOk it Wi Spec.Hmac.sha1S Proof.Sha1.md Spec.Sha1.H0 where
  sizes := ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by simp only [it]; omega_using [h₁], h₂⟩
  pad := by decide
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha1.md, Spec.Sha1.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 20) h (by omega_using [hj])
  out := fun s h₁ h₂ h₃ => (Proof.Sha1.RISCV64.Stream.shape.out s h₁ h₂ h₃).mono fun _ ⟨g, a, b, c, d⟩ =>
    ⟨fun r x y _ => g r x y, a, b, c, d⟩
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun m => by
    show Spec.Sha1.hash m = _
    rw [Proof.Sha1.hash_eq]
    exact (List.take_of_length_le (Nat.le_of_eq (Proof.Sha1.md.digest_length _))).symm,
    by decide, by decide⟩

end VG.Proof.Pbkdf2.RISCV64.Sha1

end

end


/-!
# PBKDF2-HMAC-SHA-1's iteration on RISC-V: the frame

Untrusted: everything here is checked by Lean. The precondition is the one
of every Merkle–Damgård hash function's iteration (`Pre`,
`Proof/Pbkdf2/RISCV64/Iterate.lean`), for SHA-1's sizes (`Sha1.it`), and so
are the parts of the scratch space (`sc`, `sc_contains`, …): the frame is
`scratch` rounded up to a multiple of 8, of which the code uses 164 bytes.
`Hs` says the frame holds the key's two hash values; `LI` is the loop's
invariant, with `m` steps left, `U`'s words in `A` and `T`'s in the frame.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Sha1.RISCV64

open VG VG.RISCV64 VG.Impl.Pbkdf2.Sha1.RISCV64
open VG.Proof.Pbkdf2.RISCV64 (Pre Sizes key up tp scr nn sc scR keyR uR tR sc_contains sc_al sc_add pad_le)
open VG.Proof.Pbkdf2.RISCV64.Sha1 (it)
open VG.Spec.Sha1 (HashValue Word)
open VG.Proof.Pbkdf2.Sha1Words (wstep wIter)

section
variable (s₀ : State)

/-- The key's inner and outer hash values. -/
abbrev Hi : HashValue := Spec.Sha1.stateAt s₀.mem (key s₀)
abbrev Ho : HashValue := Spec.Sha1.stateAt s₀.mem (key s₀ + BitVec.ofNat 64 84)

/-- The word at offset `d` of the frame. -/
abbrev fw (m : Mem) (d : Nat) : Word := m.readW (sc s₀ + BitVec.ofNat 64 d) 32

end

/-- The frame holds the key's two hash values. -/
structure Hs (s₀ : State) (m : Mem) : Prop where
  hi : ∀ k < 5, fw s₀ m (hiO + 4 * k) = (Hi s₀)[k]!
  ho : ∀ k < 5, fw s₀ m (hoO + 4 * k) = (Ho s₀)[k]!

/-- The loop's invariant, with `m` steps left before the final `T`, `R`. -/
structure LI (Wi : Nat) (s₀ : State) (R : HashValue) (m : Nat) (s : State) : Prop where
  b : s.gpr B = sc s₀
  n : s.gpr N = BitVec.ofNat 64 m
  tp : s.gpr TP = tp s₀
  xy : ∃ x y : HashValue, (∀ k < 5, (s.gpr (A.getD k .t0)).setWidth 32 = x[k]!) ∧
    (∀ k < 5, fw s₀ s.mem (tO + 4 * k) = y[k]!) ∧ wIter (Hi s₀) (Ho s₀) m x y = R
  hs : Hs s₀ s.mem
  saved : Spill.Saved (sc s₀) s₀.gpr saved s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [scR Wi s₀] s₀.mem s.mem

section
variable {Wi : Nat} {s₀ : State} (hp : Pre it Wi s₀) (hz : Sizes it Wi)
include hp hz

omit hp in
theorem fc {d n : Nat} (h : d + n ≤ 164) : (scR Wi s₀).Contains (sc s₀ + BitVec.ofNat 64 d) n :=
  sc_contains hz (by have := hz.fits; simp only [it] at this; omega_using [h, this])

theorem fin {s : State} (hwr : s.wr = s₀.wr) {d n : Nat} (h : d + n ≤ 164) :
    InRegions s.wr (sc s₀ + BitVec.ofNat 64 d) n :=
  ⟨scR Wi s₀, by rw [hwr, hp.wr]; simp, fc hz h⟩

theorem frd {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {d n : Nat} (h : d + n ≤ 164) :
    InRegions (s.rd ++ s.wr) (sc s₀ + BitVec.ofNat 64 d) n :=
  ⟨scR Wi s₀, by rw [hrd, hwr, hp.rd, hp.wr]; simp, fc hz h⟩

end

theorem fal (s₀ : State) {d : Nat} (h : d % 4 = 0) : (sc s₀ + BitVec.ofNat 64 d).toNat % 4 = 0 :=
  Align.al_add sc_al (by decide) h

theorem fsep (s₀ : State) {a b : Nat} (h : a + 4 ≤ b ∨ b + 4 ≤ a) (ha : a + 4 ≤ 164) (hb : b + 4 ≤ 164) :
    Mem.Sep (sc s₀ + BitVec.ofNat 64 a) 4 (sc s₀ + BitVec.ofNat 64 b) 4 :=
  Offset.sep _ h (by omega_using [ha]) (by omega_using [hb])

/-- A word of the frame after a word written elsewhere in it. -/
theorem fw_write (s₀ : State) (m : Mem) {a b : Nat} (v : Word) (h : a + 4 ≤ b ∨ b + 4 ≤ a) (ha : a + 4 ≤ 164)
    (hb : b + 4 ≤ 164) : fw s₀ (m.writeW (sc s₀ + BitVec.ofNat 64 b) v) a = fw s₀ m a :=
  Mem.readW_writeW_sep (fsep s₀ h ha hb) (by decide)

/-- The saved registers' slots, apart from the words. -/
theorem slot_word (s₀ : State) {d a : Nat} (hd : d + 8 ≤ 104) (ha : 104 ≤ a) (ha' : a + 4 ≤ 164) :
    Region.Disjoint ⟨sc s₀ + BitVec.ofNat 64 d, 8⟩ ⟨sc s₀ + BitVec.ofNat 64 a, 4⟩ :=
  Offset.disjoint _ (by omega_using [hd, ha]) (by omega_using [hd]) (by omega_using [ha'])

theorem saved_bound : ∀ p ∈ saved, p.2 % 8 = 0 ∧ p.2 + 8 ≤ 104 := by decide

/-- A word written in the frame keeps the saved registers. -/
theorem saved_write {s₀ : State} {m : Mem} (h : Spill.Saved (sc s₀) s₀.gpr saved m) {a : Nat} (v : Word)
    (ha : 104 ≤ a) (ha' : a + 4 ≤ 164) :
    Spill.Saved (sc s₀) s₀.gpr saved (m.writeW (sc s₀ + BitVec.ofNat 64 a) v) :=
  h.frame (rs := [⟨sc s₀ + BitVec.ofNat 64 a, 4⟩])
    ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
    fun p hp r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact slot_word s₀ (saved_bound p hp).2 ha ha'

end VG.Proof.Pbkdf2.Sha1.RISCV64

end

end


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
    ⟨fun _ h => absurd h (by omega_using []), fun j _ hj => hy j hj, fun _ _ => rfl, fun _ _ => rfl, id, Frame.refl _ _,
      rfl, rfl, rfl⟩
  obtain an := A_ne k hk
  obtain hb' : s.gpr B = sc s₀ := by rw [h.gpr _ (by decide), hb]
  obtain rd' : s.rd = s₀.rd := h.rd.trans hrd
  obtain wr' : s.wr = s₀.wr := h.wr.trans hwr
  refine wp_lw (a := sc s₀ + BitVec.ofNat 64 (tO + 4 * k)) (by simp only [tO]; omega_using [hk]) (by rw [hb'])
    (fal s₀ (by simp only [tO]; omega_using [])) (frd hp hz rd' wr' (by simp only [tO]; omega_using [hk])) fun s₂ u₂ => ?_
  refine wp_xor fun s₃ u₃ => ?_
  refine wp_sw (a := sc s₀ + BitVec.ofNat 64 (tO + 4 * k)) (by simp only [tO]; omega_using [hk])
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), hb']) (fal s₀ (by simp only [tO]; omega_using []))
    (by rw [u₃.wr, u₂.wr]; exact fin hp hz wr' (by simp only [tO]; omega_using [hk])) fun s₄ u₄ => WP.block_nil ?_
  obtain hv : (s₃.gpr T1).setWidth 32 = y[k]! ^^^ x[k]! := by
    rw [u₃.gpr, u₂.gpr, lo32_xor, lo32_ext, u₂.other _ an.1, h.gpr _ an.1, hx k hk]
    have := h.todo k (Nat.le_refl _) hk
    simp only [fw] at this
    rw [this]
  obtain m₄ : s₄.mem = s.mem.writeW (sc s₀ + BitVec.ofNat 64 (tO + 4 * k)) (y[k]! ^^^ x[k]!) := by
    rw [u₄.mem, hv, u₃.mem, u₂.mem]
  refine ⟨fun j hj => ?_, fun j hj hj' => ?_, fun r hr => ?_, fun d hd => ?_, fun hsv => ?_, ?_,
    by rw [u₄.rd, u₃.rd, u₂.rd, h.rd], by rw [u₄.wr, u₃.wr, u₂.wr, h.wr], by rw [u₄.sp, u₃.sp, u₂.sp, h.sp]⟩
  · rw [m₄]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [fw_write s₀ _ _ (by omega_using [hj]) (by simp only [tO]; omega_arith) (by simp only [tO]; omega_using [hk])]; exact h.done j hj
    · exact Mem.readW_writeW_self32 _ _ _
  · rw [m₄, fw_write s₀ _ _ (by omega_using [hj]) (by simp only [tO]; omega_using [hj']) (by simp only [tO]; omega_using [hk])]
    exact h.todo j (by omega_using [hj]) hj'
  · rw [u₄.gpr, u₃.other _ hr, u₂.other _ hr, h.gpr _ hr]
  · rw [m₄, fw_write s₀ _ _ (by omega_using [hd]) (by simp only [tO] at hd ⊢; omega_using [hd]) (by simp only [tO]; omega_using [hk])]
    exact h.other d hd
  · rw [m₄]; exact saved_write (h.saved hsv) _ (by simp only [tO]; omega_using []) (by simp only [tO]; omega_using [hk])
  · rw [m₄]
    exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by simp only [tO]; omega_using [])
      (by simp only [tO]; omega_using [hk]) (by simp only [tO]; omega_using []))

/-! ## One step -/

theorem body_ok {R : HashValue} {m : Nat} {s : State} (h : LI Wi s₀ R (m + 1) s) (hm : m + 1 < 2 ^ 64) :
    WP isa (.block body) s (LI Wi s₀ R m) := by
  obtain ⟨x, y, hx, hy, hR⟩ := h.xy
  obtain rdwr : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  unfold body
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  -- The inner compression.
  refine WP.mono (cmp_ok inner_ok s x (Hi s₀) h.b sc_al
    (fun k hk => frd hp hz h.rd h.wr (by simp only [inner, hiO]; omega)) (fun k hk => h.hs.hi k hk)
    (fun k hk => by rw [inner_wr k hk]; exact hx k hk)) fun s₁ ⟨v₁, k₁, m₁, rd₁, wr₁, sp₁⟩ => ?_
  rw [WP.block_append_iff]
  obtain b₁ : s₁.gpr B = sc s₀ := by rw [k₁ _ inner_keep.1, h.b]
  -- The outer compression.
  refine WP.mono (cmp_ok outer_ok s₁ (compress (Hi s₀) (blk x)) (Ho s₀) b₁ sc_al
    (fun k hk => frd hp hz (rd₁.trans h.rd) (wr₁.trans h.wr) (by simp only [outer, hoO]; omega))
    (fun k hk => by rw [m₁]; exact h.hs.ho k hk)
    (fun k hk => by rw [outer_wr k hk, ← inner_var k hk]; exact v₁ k hk)) fun s₂ ⟨v₂, k₂, m₂, rd₂, wr₂, sp₂⟩ => ?_
  rw [WP.block_append_iff]
  obtain b₂ : s₂.gpr B = sc s₀ := by rw [k₂ _ outer_keep.1, b₁]
  obtain hx₂ : ∀ k < 5, (s₂.gpr (A.getD k .t0)).setWidth 32 = (wstep (Hi s₀) (Ho s₀) x)[k]! := fun k hk => by
    rw [← outer_var k hk]; exact v₂ k hk
  -- `T ← T ⊕ U`.
  refine WP.mono (xorT_ok hp hz s₂ _ y b₂ hx₂ (fun k hk => by rw [m₂, m₁]; exact hy k hk)
    (rd₂.trans (rd₁.trans h.rd)) (wr₂.trans (wr₁.trans h.wr))) fun s₃ h₃ => ?_
  refine wp_subi (imm := 1) (by decide) fun s₄ u₄ => WP.block_nil ?_
  obtain g₃ : ∀ r, r ≠ T1 → ¬ Clob outer r → ¬ Clob inner r → s₃.gpr r = s.gpr r := fun r h1 ho hi => by
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
  obtain hlt : n < 2 ^ 64 := by omega_using [hn]
  refine WP.ite (decide (n = 0)) (by rw [eval_zero, h.n, ofNat_beq_zero hlt]) (fun hb => ?_) (fun hb => ?_)
  · obtain rfl : n = 0 := by simpa using hb
    exact WP.block_nil h
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hb; omega_using [hb]⟩
    refine WP.loop (M := isa) (fun m s => m + 1 < 2 ^ 32 ∧ LI Wi s₀ R (m + 1) s)
      (fun m s ⟨hm, hs'⟩ => WP.mono (body_ok hp hz hs' (by omega_using [hm])) fun s' hi => ?_) m s ⟨hn, h⟩
    obtain hz' : isa.eval (.nonzero N) s' = some (decide (m ≠ 0)) := by
      rw [eval_nonzero, hi.n, bne, ofNat_beq_zero (by omega_using [hm])]; simp
    cases m with
    | zero => exact .inl ⟨by rw [hz']; rfl, hi⟩
    | succ m => exact .inr ⟨by rw [hz']; simp, m, by omega_using [], by omega_using [hm], hi⟩

end

end VG.Proof.Pbkdf2.Sha1.RISCV64

end

end


/-!
# PBKDF2-HMAC-SHA-1's iteration on RISC-V: the prologue

Untrusted: everything here is checked by Lean. After the entry block, which
zero-extends `n` (`Proof/Pbkdf2/RISCV64/Correct.lean`): the frame
aligned and our caller's registers saved there; the key's inner and outer
hash values copied to the frame as words (`cpLE_ok`); `T`'s words to the
frame (`cpT_ok`) and `U`'s to `A` (`ldU_ok`), big-endian. That is the loop's
invariant with `n` steps left (`pro_ok`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Sha1.RISCV64

open VG VG.RISCV64 VG.Impl.Pbkdf2.Sha1.RISCV64
open VG.RISCV64.ByteLoad (beWord loadBE32_ok loadLE32_ok contains_byte)
open VG.Proof.Pbkdf2.RISCV64 (Pre Sizes Entry key up tp scr nn sc scR keyR uR tR sc_al sc_sub)
open VG.Proof.Pbkdf2.RISCV64.Sha1 (it)
open VG.Spec.Sha1 (HashValue Word)
open VG.Proof.Pbkdf2.Sha1Words (beWords wIter)

/-- A big-endian word in a region a frame keeps. -/
theorem beWord_frame {rs : List Region} {m m' : Mem} {R : Region} {p : Addr} {off : Nat}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, R.Disjoint r) (hc : R.Contains (p + BitVec.ofNat 64 off) 4) :
    beWord m' p off = beWord m p off := by
  have e (k : Nat) (hk : k < 4) : m' (p + BitVec.ofNat 64 (off + k)) = m (p + BitVec.ofNat 64 (off + k)) :=
    hf _ fun r hr hx => hd r hr _ (contains_byte hc (k := k) hk) hx
  obtain e0 := e 0 (by decide)
  rw [Nat.add_zero] at e0
  simp only [beWord, e0, e 1 (by decide), e 2 (by decide), e 3 (by decide)]

/-- What the prologue keeps. -/
structure PS (Wi : Nat) (s₀ s : State) : Prop where
  a0 : s.gpr .a0 = key s₀
  a1 : s.gpr .a1 = up s₀
  b : s.gpr B = sc s₀
  tp : s.gpr TP = tp s₀
  frame : Frame [scR Wi s₀] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem PS.keep {Wi : Nat} {s₀ s s' : State} (h : PS Wi s₀ s) (hg : ∀ r, r ≠ T1 → r ≠ KR → s'.gpr r = s.gpr r)
    (hf : Frame [scR Wi s₀] s.mem s'.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    PS Wi s₀ s' :=
  ⟨by rw [hg _ (by decide) (by decide), h.a0], by rw [hg _ (by decide) (by decide), h.a1],
    by rw [hg _ (by decide) (by decide), h.b], by rw [hg _ (by decide) (by decide), h.tp], h.frame.trans hf,
    hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp⟩

section
variable {Wi : Nat} {s₀ : State} (hp : Pre it Wi s₀) (hz : Sizes it Wi)
include hp hz

omit hp in
/-- A word stored in the frame, within `scR`. -/
theorem frame_word {m : Mem} {d : Nat} (hd : d + 4 ≤ 164) (v : Word) :
    Frame [scR Wi s₀] m (m.writeW (sc s₀ + BitVec.ofNat 64 d) v) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (fc hz hd)

/-- The first `k` words of the hash value at `so(key)` copied to `fo` in the frame. -/
structure CI (so fo : Nat) (s₁ : State) (k : Nat) (s : State) : Prop where
  ps : PS Wi s₀ s
  done : ∀ j < k, fw s₀ s.mem (fo + 4 * j) = s₀.mem.readW (key s₀ + BitVec.ofNat 64 (so + 4 * j)) 32
  other : ∀ d, d + 4 ≤ fo ∨ fo + 20 ≤ d → d + 4 ≤ 164 → fw s₀ s.mem d = fw s₀ s₁.mem d
  saved : Spill.Saved (sc s₀) s₀.gpr saved s₁.mem → Spill.Saved (sc s₀) s₀.gpr saved s.mem
  gpr : ∀ r, r ≠ T1 → r ≠ KR → s.gpr r = s₁.gpr r

theorem cpLE_ok (so fo : Nat) (hso : so + 20 ≤ 168) (hso4 : so % 4 = 0) (hfo : 104 ≤ fo) (hfo' : fo + 20 ≤ 164)
    (hfa : fo % 4 = 0) (s₁ : State) (h₁ : PS Wi s₀ s₁) :
    WP isa (.block (cpLE so fo)) s₁ (CI (Wi := Wi) (s₀ := s₀) so fo s₁ 5) := by
  refine wp_range_flatMap (M := isa) (CI (Wi := Wi) (s₀ := s₀) so fo s₁) (fun k s hk h => ?_) 5 (Nat.le_refl _) s₁
    ⟨h₁, fun _ h => absurd h (by omega), fun _ _ _ => rfl, id, fun _ _ _ => rfl⟩
  rw [WP.block_append_iff]
  obtain hin : InRegions (s.rd ++ s.wr) (s.gpr .a0 + BitVec.ofNat 64 (so + 4 * k)) 4 :=
    ⟨keyR it s₀, by rw [h.ps.rd, h.ps.wr, hp.rd, hp.wr]; simp,
      by rw [h.ps.a0]; exact Offset.contains_base _ (by simp only [it, Impl.Pbkdf2.RISCV64.It.S]; omega) (by omega)⟩
  refine WP.mono (loadLE32_ok (s := s) (d := T1) (tmp := KR) (n := .a0) (by decide) (by decide) (by decide)
    (by omega) hin) fun s₂ e₂ => ?_
  subst e₂
  refine wp_sw (a := sc s₀ + BitVec.ofNat 64 (fo + 4 * k)) (by omega)
    (by rw [RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_of_ne _ _ (by decide), h.ps.b])
    (fal s₀ (by omega)) (by exact fin hp hz h.ps.wr (by omega)) fun s₃ u₃ => WP.block_nil ?_
  obtain val : s.mem.readW (key s₀ + BitVec.ofNat 64 (so + 4 * k)) 32 =
      s₀.mem.readW (key s₀ + BitVec.ofNat 64 (so + 4 * k)) 32 :=
    h.ps.frame.readW (r := keyR it s₀) (Offset.contains_base _ (by simp only [it, Impl.Pbkdf2.RISCV64.It.S]; omega) (by omega))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.k_s) (by decide)
  obtain m₃ : s₃.mem = s.mem.writeW (sc s₀ + BitVec.ofNat 64 (fo + 4 * k))
      (s₀.mem.readW (key s₀ + BitVec.ofNat 64 (so + 4 * k)) 32) := by
    rw [u₃.mem, RegUpd.gpr_write_self, lo32_ext, RegUpd.mem_write, RegUpd.mem_write, h.ps.a0, val]
  obtain g₃ : ∀ r, r ≠ T1 → r ≠ KR → s₃.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₃.gpr, RegUpd.gpr_write_of_ne _ _ h1, RegUpd.gpr_write_of_ne _ _ h2]
  refine ⟨h.ps.keep g₃ (by rw [m₃]; exact frame_word hz (by omega) _) u₃.rd u₃.wr u₃.sp, fun j hj => ?_,
    fun d hd hd' => ?_, fun hsv => ?_, fun r h1 h2 => by rw [g₃ r h1 h2, h.gpr r h1 h2]⟩
  · rw [m₃]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [fw_write s₀ _ _ (by omega) (by omega) (by omega)]; exact h.done j hj
    · exact Mem.readW_writeW_self32 _ _ _
  · rw [m₃, fw_write s₀ _ _ (by omega) hd' (by omega)]; exact h.other d hd hd'
  · rw [m₃]; exact saved_write (h.saved hsv) _ (by omega) (by omega)

/-- The first `k` words of `T` copied to the frame. -/
structure TI (s₁ : State) (k : Nat) (s : State) : Prop where
  ps : PS Wi s₀ s
  done : ∀ j < k, fw s₀ s.mem (tO + 4 * j) = (beWords s₀.mem (tp s₀))[j]!
  other : ∀ d, d + 4 ≤ tO → fw s₀ s.mem d = fw s₀ s₁.mem d
  saved : Spill.Saved (sc s₀) s₀.gpr saved s₁.mem → Spill.Saved (sc s₀) s₀.gpr saved s.mem
  gpr : ∀ r, r ≠ T1 → r ≠ KR → s.gpr r = s₁.gpr r

omit hp hz in
theorem beWords_get (m : Mem) (p : Addr) {k : Nat} (hk : k < 5) : (beWords m p)[k]! = beWord m p (4 * k) := by
  rw [getElem!_pos _ k hk]; simp only [beWords, Vector.getElem_ofFn]; rfl

theorem cpT_ok (s₁ : State) (h₁ : PS Wi s₀ s₁) : WP isa (.block cpT) s₁ (TI (Wi := Wi) (s₀ := s₀) s₁ 5) := by
  refine wp_range_flatMap (M := isa) (TI (Wi := Wi) (s₀ := s₀) s₁) (fun k s hk h => ?_) 5 (Nat.le_refl _) s₁
    ⟨h₁, fun _ h => absurd h (by omega_using []), fun _ _ => rfl, id, fun _ _ _ => rfl⟩
  rw [WP.block_append_iff]
  obtain hc : (tR it s₀).Contains (tp s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
    Offset.contains_base _ (by simp only [it]; omega_using [hk]) (by omega_using [hk])
  obtain hin : InRegions (s.rd ++ s.wr) (s.gpr TP + BitVec.ofNat 64 (4 * k)) 4 :=
    ⟨tR it s₀, by rw [h.ps.rd, h.ps.wr, hp.rd, hp.wr]; simp, by rw [h.ps.tp]; exact hc⟩
  refine WP.mono (loadBE32_ok (s := s) (d := T1) (tmp := KR) (n := TP) (by decide) (by decide) (by decide)
    (by omega_using [hk]) hin) fun s₂ e₂ => ?_
  subst e₂
  refine wp_sw (a := sc s₀ + BitVec.ofNat 64 (tO + 4 * k)) (by simp only [tO]; omega_using [hk])
    (by rw [RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_of_ne _ _ (by decide), h.ps.b])
    (fal s₀ (by simp only [tO]; omega_using [])) (by exact fin hp hz h.ps.wr (by simp only [tO]; omega_using [hk]))
    fun s₃ u₃ => WP.block_nil ?_
  obtain val : beWord s.mem (s.gpr TP) (4 * k) = (beWords s₀.mem (tp s₀))[k]! := by
    rw [h.ps.tp, beWord_frame h.ps.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.t_s) hc, beWords_get _ _ hk]
  obtain m₃ : s₃.mem = s.mem.writeW (sc s₀ + BitVec.ofNat 64 (tO + 4 * k)) (beWords s₀.mem (tp s₀))[k]! := by
    rw [u₃.mem, RegUpd.gpr_write_self, lo32_ext, RegUpd.mem_write, RegUpd.mem_write, val]
  obtain g₃ : ∀ r, r ≠ T1 → r ≠ KR → s₃.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₃.gpr, RegUpd.gpr_write_of_ne _ _ h1, RegUpd.gpr_write_of_ne _ _ h2]
  refine ⟨h.ps.keep g₃ (by rw [m₃]; exact frame_word hz (by simp only [tO]; omega_using [hk]) _) u₃.rd u₃.wr u₃.sp,
    fun j hj => ?_, fun d hd => ?_, fun hsv => ?_, fun r h1 h2 => by rw [g₃ r h1 h2, h.gpr r h1 h2]⟩
  · rw [m₃]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [fw_write s₀ _ _ (by omega_using [hj]) (by simp only [tO]; omega_arith) (by simp only [tO]; omega_using [hk])]; exact h.done j hj
    · exact Mem.readW_writeW_self32 _ _ _
  · rw [m₃, fw_write s₀ _ _ (by omega_using [hd]) (by simp only [tO] at hd ⊢; omega_using [hd]) (by simp only [tO]; omega_using [hk])]
    exact h.other d hd
  · rw [m₃]; exact saved_write (h.saved hsv) _ (by simp only [tO]; omega_using []) (by simp only [tO]; omega_using [hk])

omit hp hz in
theorem A_nodup : ∀ i < 5, ∀ j < 5, i ≠ j → A.getD i .t0 ≠ A.getD j .t0 := by decide
omit hp hz in
theorem A_sp : ∀ k < 5, A.getD k .t0 ≠ .a0 ∧ A.getD k .t0 ≠ .a1 ∧ A.getD k .t0 ≠ B ∧ A.getD k .t0 ≠ TP ∧
    A.getD k .t0 ≠ KR ∧ A.getD k .t0 ≠ N := by decide

/-- The first `k` words of `U` loaded into `A`. -/
structure UI (s₁ : State) (k : Nat) (s : State) : Prop where
  done : ∀ j < k, (s.gpr (A.getD j .t0)).setWidth 32 = (beWords s₀.mem (up s₀))[j]!
  gpr : ∀ r, (∀ j < 5, r ≠ A.getD j .t0) → r ≠ KR → s.gpr r = s₁.gpr r
  mem : s.mem = s₁.mem
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  sp : s.sp = s₁.sp

omit hz in
theorem ldU_ok (s₁ : State) (h₁ : PS Wi s₀ s₁) : WP isa (.block ldU) s₁ (UI (s₀ := s₀) s₁ 5) := by
  refine wp_range_flatMap (M := isa) (UI (s₀ := s₀) s₁) (fun k s hk h => ?_) 5 (Nat.le_refl _) s₁
    ⟨fun _ h => absurd h (by omega_using []), fun _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
  obtain an := A_sp k hk
  obtain a1 : s.gpr .a1 = up s₀ := by
    rw [h.gpr _ (fun j hj => (A_sp j hj).2.1.symm) (by decide), h₁.a1]
  obtain hc : (uR it s₀).Contains (up s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
    Offset.contains_base _ (by simp only [it]; omega_using [hk]) (by omega_using [hk])
  obtain hin : InRegions (s.rd ++ s.wr) (s.gpr .a1 + BitVec.ofNat 64 (4 * k)) 4 :=
    ⟨uR it s₀, by rw [h.rd, h.wr, h₁.rd, h₁.wr, hp.rd, hp.wr]; simp, by rw [a1]; exact hc⟩
  refine WP.mono (loadBE32_ok (s := s) (d := A.getD k .t0) (tmp := KR) (n := .a1) an.2.1 (by decide) an.2.2.2.2.1
    (by omega_using [hk]) hin) fun s₂ e₂ => ?_
  subst e₂
  obtain val : beWord s.mem (s.gpr .a1) (4 * k) = (beWords s₀.mem (up s₀))[k]! := by
    rw [a1, h.mem, beWord_frame h₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.u_s) hc, beWords_get _ _ hk]
  refine ⟨fun j hj => ?_, fun r hr h2 => ?_, by rw [RegUpd.mem_write, RegUpd.mem_write, h.mem],
    by rw [RegUpd.rd_write, RegUpd.rd_write, h.rd], by rw [RegUpd.wr_write, RegUpd.wr_write, h.wr],
    by rw [RegUpd.sp_write, RegUpd.sp_write, h.sp]⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [RegUpd.gpr_write_of_ne _ _ (A_nodup j (by omega_arith) k hk (by omega_using [hj])),
        RegUpd.gpr_write_of_ne _ _ (A_sp j (by omega_arith)).2.2.2.2.1]
      exact h.done j hj
    · rw [RegUpd.gpr_write_self, lo32_ext, val]
  · rw [RegUpd.gpr_write_of_ne _ _ (hr k hk), RegUpd.gpr_write_of_ne _ _ h2]; exact h.gpr r hr h2

end

/-! ## The whole prologue -/

/-- The final `T`, from the arguments. -/
abbrev Rf (s₀ : State) : HashValue :=
  wIter (Hi s₀) (Ho s₀) (nn s₀) (beWords s₀.mem (up s₀)) (beWords s₀.mem (tp s₀))

theorem save_eq : save = ([.addi B B 7, .logicImm .and B B (-8)] : List Instr) ++ Spill.saveCode B saved := rfl

theorem saved_fits : Spill.Fits saved := by decide

section
variable {Wi : Nat} {s₀ : State} (hp : Pre it Wi s₀) (hz : Sizes it Wi)
include hp hz

theorem pro_ok {e : State} (he : Entry s₀ e) : WP isa (.block (save ++ setup)) e (LI Wi s₀ (Rf s₀) (nn s₀)) := by
  rw [save_eq, List.append_assoc, WP.block_append_iff]
  refine WP.mono (Q := fun (e₁ : State) => e₁ = e.write B (sc s₀)) ?_ fun e₁ he₁ => ?_
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addi (show imm12 7 by decide),
      exec_logicImm (show imm12 (-8) by decide), RegUpd.gpr_write_self, RegUpd.write_write, Align.align_eq,
      Option.some.injEq, exists_eq_left']
    rw [he.other _ (by decide)]; rfl
  subst he₁
  obtain b₁ : (e.write B (sc s₀)).gpr B = sc s₀ := RegUpd.gpr_write_self _ _ _
  have g₁ (r : Reg) (hr : r ≠ B) : (e.write B (sc s₀)).gpr r = e.gpr r := RegUpd.gpr_write_of_ne _ _ hr
  refine Spill.save_ok (b := B) (l := saved) (by rw [b₁]; exact sc_al) (by decide) (fun q hq => ?_) ?_
  · rw [b₁]; exact fin hp hz (by rw [RegUpd.wr_write, he.wr]) (by have := saved_bound q hq; omega_using [this])
  generalize hs₂ : ({ (e.write B (sc s₀)) with
    mem := Spill.saveMem (e.write B (sc s₀)).mem ((e.write B (sc s₀)).gpr B) (e.write B (sc s₀)).gpr saved } :
      State) = s₂
  have gpr₂ (r : Reg) (hr : r ≠ B) : s₂.gpr r = e.gpr r := by rw [← hs₂]; exact g₁ r hr
  obtain b₂ : s₂.gpr B = sc s₀ := by rw [← hs₂]; exact b₁
  obtain mem₂ : s₂.mem = Spill.saveMem s₀.mem (sc s₀) (e.write B (sc s₀)).gpr saved := by
    rw [← hs₂]; show Spill.saveMem _ _ _ _ = _; rw [b₁, RegUpd.mem_write, he.mem]
  obtain ps₂ : PS Wi s₀ s₂ := by
    refine ⟨by rw [gpr₂ _ (by decide), he.other _ (by decide)], by rw [gpr₂ _ (by decide), he.other _ (by decide)],
      b₂, by rw [gpr₂ _ (by decide), he.other _ (by decide)]; rfl, ?_, by rw [← hs₂]; exact he.rd,
      by rw [← hs₂]; exact he.wr, by rw [← hs₂]; exact he.sp⟩
    rw [mem₂]
    refine (Spill.saveMem_frame_base (n := 104) (fun q hq => (saved_bound q hq).2) (by decide) _ _ _).sub
      fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    refine ⟨scR Wi s₀, by simp, ?_⟩
    have := sc_sub (Wi := Wi) (s₀ := s₀) (a := 0) (n := 104) (by have := hz.fits; simp only [it] at this; omega_using [this])
    rwa [Proof.Pbkdf2.RISCV64.sc0] at this
  obtain sv₂ : Spill.Saved (sc s₀) s₀.gpr saved s₂.mem := by
    rw [mem₂]
    intro q hq
    rw [Spill.saveMem_saved saved_fits _ _ _ q hq]
    have : q.1 ≠ B ∧ q.1 ≠ .a2 := by revert q; decide
    rw [g₁ _ this.1, he.other _ this.2]
  -- The four parts of the setup.
  unfold setup
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (cpLE_ok hp hz 0 hiO (by decide) (by decide) (by decide) (by decide) (by decide) s₂ ps₂)
    fun s₃ h₃ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cpLE_ok hp hz 84 hoO (by decide) (by decide) (by decide) (by decide) (by decide) s₃ h₃.ps)
    fun s₄ h₄ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cpT_ok hp hz s₄ h₄.ps) fun s₅ h₅ => ?_
  refine WP.mono (ldU_ok hp s₅ h₅.ps) fun s₆ h₆ => ?_
  have m₆ : s₆.mem = s₅.mem := h₆.mem
  have keepA (r : Reg) (hA : ∀ j < 5, r ≠ A.getD j .t0) (h1 : r ≠ T1) (h2 : r ≠ KR) : s₆.gpr r = s₂.gpr r := by
    rw [h₆.gpr r hA h2, h₅.gpr r h1 h2, h₄.gpr r h1 h2, h₃.gpr r h1 h2]
  have notA (r : Reg) (h : r = B ∨ r = N ∨ r = TP) : ∀ j < 5, r ≠ A.getD j .t0 := fun j hj e => by
    rcases h with rfl | rfl | rfl
    · exact (A_sp j hj).2.2.1 e.symm
    · exact (A_sp j hj).2.2.2.2.2 e.symm
    · exact (A_sp j hj).2.2.2.1 e.symm
  refine ⟨?_, ?_, ?_, ⟨beWords s₀.mem (up s₀), beWords s₀.mem (tp s₀), h₆.done, fun k hk => by
      rw [m₆]; exact h₅.done k hk, rfl⟩, ⟨fun k hk => ?_, fun k hk => ?_⟩, ?_, by rw [h₆.rd]; exact h₅.ps.rd,
    by rw [h₆.wr]; exact h₅.ps.wr, by rw [h₆.sp]; exact h₅.ps.sp, by rw [m₆]; exact h₅.ps.frame⟩
  · rw [keepA _ (notA _ (.inl rfl)) (by decide) (by decide), b₂]
  · rw [keepA _ (notA _ (.inr (.inl rfl))) (by decide) (by decide), gpr₂ _ (by decide)]; exact he.a2
  · rw [keepA _ (notA _ (.inr (.inr rfl))) (by decide) (by decide), gpr₂ _ (by decide), he.other _ (by decide)]; rfl
  · rw [m₆, h₅.other _ (by simp only [hiO, tO]; omega_using [hk]), h₄.other _ (.inl (by simp only [hiO, hoO]; omega_using [hk]))
      (by simp only [hiO]; omega_using [hk]), h₃.done k hk, Nat.zero_add, getElem!_pos _ k hk, Proof.Sha1.StateMem.stateAt_get _ _ hk]
  · rw [m₆, h₅.other _ (by simp only [hoO, tO]; omega_using [hk]), h₄.done k hk, getElem!_pos _ k hk,
      Proof.Sha1.StateMem.stateAt_get _ _ hk, Offset.add_add]
  · rw [m₆]; exact h₅.saved (h₄.saved (h₃.saved sv₂))

end

end VG.Proof.Pbkdf2.Sha1.RISCV64

end

end


/-!
# PBKDF2-HMAC-SHA-1's iteration on RISC-V: the epilogue, and correctness

Untrusted: everything here is checked by Lean. The epilogue writes `T`'s
words to `t`, big-endian, which is the digest of the final `T`
(`out_ok`), and restores our caller's registers (`fin_ok`). `correct`: the
entry block, the prologue, the loop and the epilogue meet the iteration's
contract (`iterK`), since the digest of the final `T` on words is PBKDF2's
(`Sha1Words.iterate_digest`, `Md.iterate_hmac`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Sha1.RISCV64

open VG VG.RISCV64 VG.Impl.Pbkdf2.Sha1.RISCV64
open VG.RISCV64.ByteLoad (beBytes storeBE_ok)
open VG.WriteBytes (writeBytes)
open VG.Impl.Words.RISCV64 (storeBE)
open VG.Proof.Hmac.Common (writeBytes_at writeBytes_other)
open VG.Proof.Pbkdf2.RISCV64 (Pre Sizes Entry key up tp scr nn sc scR keyR uR tR sc_al sc_sub iterK)
open VG.Proof.Pbkdf2.RISCV64.Sha1 (it)
open VG.Spec.Sha1 (HashValue Word wordBytes)
open VG.Proof.Sha1 (md)
open VG.Proof.Pbkdf2.Sha1Words (beWords wIter digest_eq digest_beWords iterate_digest)

theorem shr_byte (x : BitVec 64) (s : Nat) : (x >>> s).setWidth 8 = x.extractLsb' s 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_ushiftRight, hi]

theorem setWidth_byte (w : Word) {s : Nat} (h : s + 8 ≤ 32) :
    (w.setWidth 64).extractLsb' s 8 = w.extractLsb' s 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi, show s + i < 32 by omega_using [h, hi], show s + i < 64 by omega_using [h, hi]]

/-- A word, as `storeBE 4` stores it. -/
theorem beBytes_word (w : Word) : beBytes 4 (w.setWidth 64) = wordBytes w := by
  simp only [beBytes, shr_byte]
  rw [show List.range 4 = [0, 1, 2, 3] from rfl]
  simp (disch := decide) only [List.map_cons, List.map_nil, Nat.reduceMul, Nat.reduceSub, setWidth_byte,
    wordBytes]

/-- Byte `4k + i` of a digest. -/
theorem digest_getD (x : HashValue) {k i : Nat} (hk : k < 5) (hi : i < 4) :
    (md.digest x).getD (4 * k + i) 0 = (wordBytes x[k]!).getD i 0 := by
  rw [digest_eq, getElem!_pos x k hk]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 by omega_using [hk]) with rfl | rfl | rfl | rfl | rfl <;>
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega_using [hi]) with rfl | rfl | rfl | rfl <;>
  simp [wordBytes]

theorem digest_length (x : HashValue) : (md.digest x).length = 20 := md.digest_length x

/-! ## `T` to `t` -/

/-- The first `k` words of `T` written to `t`, from the state `s₁` before. -/
structure OI (s₀ s₁ : State) (y : HashValue) (k : Nat) (s : State) : Prop where
  bytes : ∀ j < 20, s.mem (tp s₀ + BitVec.ofNat 64 j) =
    if j < 4 * k then (md.digest y).getD j 0 else s₁.mem (tp s₀ + BitVec.ofNat 64 j)
  frame : Frame [tR it s₀] s₁.mem s.mem
  gpr : ∀ r, r ≠ T1 → r ≠ KR → s.gpr r = s₁.gpr r
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  sp : s.sp = s₁.sp

section
variable {Wi : Nat} {s₀ : State} (hp : Pre it Wi s₀) (hz : Sizes it Wi)
include hp hz

/-- The frame's words, which the writes to `t` keep. -/
theorem fw_tR {m m' : Mem} (hf : Frame [tR it s₀] m m') {d : Nat} (hd : d + 4 ≤ 164) : fw s₀ m' d = fw s₀ m d :=
  hf.readW (r := scR Wi s₀) (fc hz hd) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.t_s.symm) (by decide)

theorem out_ok (s₁ : State) (y : HashValue) (hb : s₁.gpr B = sc s₀) (htp : s₁.gpr TP = tp s₀)
    (hy : ∀ k < 5, fw s₀ s₁.mem (tO + 4 * k) = y[k]!) (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) :
    WP isa (.block ((List.range 5).flatMap fun k => ([.load .w T1 B (tO + 4 * k)] : List Instr) ++ storeBE 4 T1 KR TP (4 * k)))
      s₁ (OI s₀ s₁ y 5) := by
  refine wp_range_flatMap (M := isa) (OI s₀ s₁ y) (fun k s hk h => ?_) 5 (Nat.le_refl _) s₁
    ⟨fun j _ => by simp, Frame.refl _ _, fun _ _ _ => rfl, rfl, rfl, rfl⟩
  obtain hb' : s.gpr B = sc s₀ := by rw [h.gpr _ (by decide) (by decide), hb]
  obtain htp' : s.gpr TP = tp s₀ := by rw [h.gpr _ (by decide) (by decide), htp]
  obtain rd' : s.rd = s₀.rd := h.rd.trans hrd
  obtain wr' : s.wr = s₀.wr := h.wr.trans hwr
  rw [List.singleton_append]
  refine wp_lw (a := sc s₀ + BitVec.ofNat 64 (tO + 4 * k)) (by simp only [tO]; omega_using [hk]) (by rw [hb'])
    (fal s₀ (by simp only [tO]; omega_using [])) (frd hp hz rd' wr' (by simp only [tO]; omega_using [hk])) fun s₂ u₂ => ?_
  obtain hv : s₂.gpr T1 = (y[k]!).setWidth 64 := by
    obtain e := fw_tR hp hz h.frame (d := tO + 4 * k) (by simp only [tO]; omega_using [hk])
    obtain e' := hy k hk
    simp only [fw] at e e'
    rw [u₂.gpr, e, e']
  obtain tp₂ : s₂.gpr TP = tp s₀ := by rw [u₂.other _ (by decide), htp']
  refine WP.mono (storeBE_ok (s := s₂) (v := T1) (tmp := KR) (n := TP) (off := 4 * k) (w := 4) (by decide)
    (by decide) (by decide) (by decide) (by omega_using [hk]) fun j hj => ?_) fun s₃ e₃ => ?_
  · rw [u₂.wr, wr', hp.wr, tp₂]
    exact ⟨tR it s₀, by simp, Offset.contains_base _ (by simp only [it]; omega_using [hk, hj]) (by omega_using [hk, hj])⟩
  subst e₃
  obtain m₃ : (({ s₂ with mem := writeBytes s₂.mem (s₂.gpr TP + BitVec.ofNat 64 (4 * k)) (beBytes 4 (s₂.gpr T1)) } :
      State).write KR (s₂.gpr T1)).mem = writeBytes s.mem (tp s₀ + BitVec.ofNat 64 (4 * k)) (wordBytes y[k]!) := by
    rw [RegUpd.mem_write]; show writeBytes _ _ _ = _; rw [u₂.mem, tp₂, hv, beBytes_word]
  have wl : (wordBytes y[k]!).length = 4 := rfl
  refine ⟨fun j hj => ?_, ?_, fun r h1 h2 => ?_, ?_, ?_, ?_⟩
  · rw [m₃]
    by_cases hin : 4 * k ≤ j ∧ j < 4 * k + 4
    · obtain ⟨i, rfl⟩ : ∃ i, j = 4 * k + i := ⟨j - 4 * k, by omega_using [hin]⟩
      rw [← Offset.add_add, writeBytes_at _ _ _ (by rw [wl]; omega_using [hin]) (by rw [wl]; decide),
        digest_getD y hk (by omega_using [hin])]
      simp only [show 4 * k + i < 4 * (k + 1) by omega_using [hin], ↓reduceIte]
    · rw [writeBytes_other _ _ _ (by
        rw [wl, Offset.lt_iff _ _ (by omega_using [hk]), Mem.sub_ofNat_toNat _ (by omega_using [hj])]; exact hin), h.bytes j hj]
      by_cases hjk : j < 4 * k
      · simp only [hjk, show j < 4 * (k + 1) by omega_using [hjk], ↓reduceIte]
      · simp only [hjk, show ¬ j < 4 * (k + 1) by omega_using [hin, hjk], ↓reduceIte]
  · rw [m₃]
    exact h.frame.trans (VG.WriteBytes.writeBytes_frame _ _ _ (by
      rw [wl]; exact Offset.contains_base _ (by simp only [it]; omega_using [hk]) (by omega_using [hk])))
  · rw [RegUpd.gpr_write_of_ne _ _ h2]
    show s₂.gpr r = _
    rw [u₂.other _ h1, h.gpr r h1 h2]
  · rw [RegUpd.rd_write]; show s₂.rd = _; rw [u₂.rd, h.rd]
  · rw [RegUpd.wr_write]; show s₂.wr = _; rw [u₂.wr, h.wr]
  · rw [RegUpd.sp_write]; show s₂.sp = _; rw [u₂.sp, h.sp]

omit hp hz in
theorem finish_eq : finish = ((List.range 5).flatMap fun k => ([.load .w T1 B (tO + 4 * k)] : List Instr) ++
    storeBE 4 T1 KR TP (4 * k)) ++ Spill.restoreCode B saved := rfl

theorem fin_ok {R : HashValue} {s : State} (h : LI Wi s₀ R 0 s) :
    WP isa (.block finish) s fun s' => abiPreserved s₀ s' ∧ Spec.Sha256.bytesAt s'.mem (tp s₀) 20 = md.digest R := by
  obtain ⟨x, y, hx, hy, hR⟩ := h.xy
  have hyR : y = R := hR
  subst hyR
  rw [finish_eq, WP.block_append_iff]
  refine WP.mono (out_ok hp hz s y h.b h.tp hy h.rd h.wr) fun s₁ h₁ => ?_
  obtain b₁ : s₁.gpr B = sc s₀ := by rw [h₁.gpr _ (by decide) (by decide), h.b]
  obtain sv₁ : Spill.Saved (sc s₀) s₀.gpr saved s₁.mem :=
    h.saved.frame h₁.frame fun q hq r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.t_s.symm.sub_left (sc_sub (by have := hz.fits; have := saved_bound q hq; simp only [it] at *; omega_arith))
  refine WP.mono (Spill.restore_wp (b := B) (l := saved) (B := sc s₀) sc_al b₁ (by decide) (by decide)
    (fun q hq => frd hp hz (h₁.rd.trans h.rd) (h₁.wr.trans h.wr) (by have := saved_bound q hq; omega_using [this])) sv₁)
    fun s₂ r₂ => ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · exact r₂.gpr_of (.inl (by revert r; decide))
  · rw [r₂.sp, h₁.sp, h.sp]
  · exact r₂.gpr_of (.inl (by decide))
  · rw [r₂.mem]
    apply List.ext_getElem (by simp [Spec.Sha256.bytesAt, digest_length])
    intro j h₁' h₂'
    simp only [Spec.Sha256.bytesAt, List.length_map, List.length_range] at h₁'
    simp only [Spec.Sha256.bytesAt, List.getElem_map, List.getElem_range]
    rw [h₁.bytes j h₁']
    simp only [show j < 4 * 5 by omega_using [h₁'], ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂',
      Option.getD_some]

end

theorem entry_eq : entry = Impl.Pbkdf2.RISCV64.It.entry := rfl

/-- `iterate` meets the iteration's contract, for SHA-1's link to the specification. -/
theorem correct {Wi : Nat} {s₀ : State} (hp : Pre it Wi s₀) (hz : Sizes it Wi)
    (hl : md.Link Spec.Hmac.sha1S Spec.Sha1.H0 20) :
    WP isa iterate s₀ fun s' => abiPreserved s₀ s' ∧ (iterK Spec.Hmac.sha1S Wi).post s₀ s' := by
  unfold iterate main
  refine WP.seq (WP.mono (by rw [entry_eq]; exact Proof.Pbkdf2.RISCV64.entry_ok s₀) fun e he => ?_)
  refine WP.seq (WP.mono (pro_ok hp hz he) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (loop_ok hp hz (Proof.Pbkdf2.RISCV64.nn_lt s₀) h₁) fun s₂ h₂ => ?_)
  refine WP.mono (fin_ok hp hz h₂) fun s' ⟨ha, hb⟩ => ⟨ha, ?_⟩
  intro k0 hk hi ho
  have hD : Spec.Hmac.sha1S.digestBytes = 20 := rfl
  rw [hD]
  rw [MdStream.Md.iterate_hmac hl hk hi ho _ (by simp [Spec.Sha256.bytesAt]),
    ← digest_beWords s₀.mem (s₀.gpr .a1), ← digest_beWords s₀.mem (s₀.gpr .a3),
    iterate_digest (md.stateAt s₀.mem (s₀.gpr .a0))
      (md.stateAt s₀.mem (s₀.gpr .a0 + BitVec.ofNat 64 Spec.Hmac.sha1S.stateBytes))]
  exact hb

end VG.Proof.Pbkdf2.Sha1.RISCV64

end

end


/-!
# PBKDF2-HMAC-SHA-1's iteration on RISC-V: `Verified`

Untrusted: everything here is checked by Lean. Constant time (`ct`), as for
every Merkle–Damgård hash function's iteration
(`Proof/Pbkdf2/RISCV64/Correct.lean`): the taint analysis of `main` after the
entry block, which zero-extends `n`, the one input public only in its low
32 bits (`RelCT.wpDep`). `verifiedW`: `correct` meets the iteration's
contract with `Wi` bytes of scratch space (`iterK`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Sha1.RISCV64

open VG VG.RISCV64 VG.Impl.Pbkdf2.Sha1.RISCV64
open VG.Proof.Pbkdf2.RISCV64 (Entry entry_ok nn iterK pre_of iterImp iterSat)
open VG.Proof.Pbkdf2.RISCV64.Sha1 (it hashOkW)

/-- The taint analysis of `main`, which the kernel checks. -/
theorem main_ck : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) main hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- `iterate` is constant time, for any precondition whose public data are `iterK`'s. -/
theorem ct {pre : State → Prop} {pub : State → State → Prop}
    (hpub : ∀ s₁ s₂, pub s₁ s₂ → s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
      (s₁.gpr .a2).setWidth 32 = (s₂.gpr .a2).setWidth 32 ∧ s₁.gpr .a3 = s₂.gpr .a3 ∧
      s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.sp = s₂.sp) :
    ConstantTime isa pre pub iterate := by
  obtain ⟨_, hb⟩ := main_ck
  refine RelCT.constantTime (Q := fun _ _ => True) (RelCT.seq ?_ (RelCT.taint (A := taint)
    (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) (fun _ _ h => h) hb))
  obtain ag4 : ∀ s₁ s₂ : State, pre s₁ ∧ pre s₂ ∧ pub s₁ s₂ →
      taint.Agree (Taint.ofRegs [.a0, .a1, .a3, .a4]) s₁ s₂ := by
    rintro s₁ s₂ ⟨_, _, hq⟩
    obtain ⟨h0, h1, _, h3, h4, hsp⟩ := hpub s₁ s₂ hq
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [h0, h1, h3, h4]
  refine RelCT.mono (RelCT.wpDep (F := Entry) (RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1, .a3, .a4])
    ag4 (by rw [entry_eq]; taint_decide)) fun s₁ s₂ _ => ⟨by rw [entry_eq]; exact entry_ok s₁,
      by rw [entry_eq]; exact entry_ok s₂⟩) (fun _ _ h => h) ?_
  rintro s₁' s₂' ⟨-, σ₁, σ₂, ⟨_, _, hq⟩, a, b⟩
  obtain ⟨h0, h1, h2, h3, h4, hsp⟩ := hpub σ₁ σ₂ hq
  refine ⟨by rw [a.sp, b.sp, hsp], fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [a.other _ (by decide), b.other _ (by decide), h0]
  · rw [a.other _ (by decide), b.other _ (by decide), h1]
  · rw [a.a2, b.a2, nn, nn, h2]
  · rw [a.other _ (by decide), b.other _ (by decide), h3]
  · rw [a.other _ (by decide), b.other _ (by decide), h4]

theorem noFrames : iterate.noFrames = true := by decide

/-- `iterate` meets the iteration's contract, with `Wi` bytes of working space. -/
theorem verifiedW (Wi : Nat) (h₁ : 227 ≤ Wi) (h₂ : Wi ≤ 8192) :
    ∀ s, (iterK Spec.Hmac.sha1S Wi).pre s →
      ∃ t s', Exec isa iterate s t s' ∧ abiPreserved s s' ∧ (iterK Spec.Hmac.sha1S Wi).post s s' := by
  intro s hs
  obtain ho := hashOkW Wi h₁ h₂
  obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of (P := it) rfl rfl hs) ho.sizes ho.link
  exact ⟨t, s', he, h₁, h₂⟩

end VG.Proof.Pbkdf2.Sha1.RISCV64

end

end

/-!
# PBKDF2-HMAC-SHA-1 on RISC-V: the whole derivation

`pbkdf2` over SHA-1's streaming functions, HMAC's `init` and `finalize` and
SHA-1's own PBKDF2 `iterate` (`F`, with 240 bytes of working space for
`iterate`, `Proof/Pbkdf2/Sha1/RISCV64/`);
the taint checks of its pieces, which the kernel evaluates; and `pbkdf2`
against the shared contract of `Spec.Hmac.sha1I`.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.RISCV64.Sha1

open VG.RISCV64

/-- The functions `pbkdf2` calls. -/
def F : Impl.Pbkdf2.Whole.RISCV64.Fns where
  H := Proof.Hmac.Stream.RISCV64.Sha1.hash
  hiN := Spec.Hmac.sha1I.initAnyKeyApi.name ++ "_core"
  hfN := Spec.Hmac.sha1I.finalizeApi.name ++ "_core"
  itN := "vg_pbkdf2_hmac_sha1_iterate"
  itC := Impl.Pbkdf2.Sha1.RISCV64.iterate
  itW := 240

/-- What the proofs need of them. -/
def okF : FnsOK F where
  hH := Proof.Hmac.Stream.RISCV64.Sha1.ok
  hiCt := Proof.Hmac.Stream.RISCV64.Sha1.init_ct
  hfCt := Proof.Hmac.Stream.RISCV64.Sha1.fin_ct
  itOk := Pbkdf2.Sha1.RISCV64.verifiedW 240 (by decide) (by decide)
  itCt := Pbkdf2.Sha1.RISCV64.ct fun _ _ h => h
  itNf := Pbkdf2.Sha1.RISCV64.noFrames
  itW0 := by decide
  itB := by decide
  frB := by decide

theorem checks : Checks F := by
  constructor
  case upd => unfold Ck; taint_decide_sum [VG.Proof.Sha1.RISCV64.compressSum]
  all_goals refine ⟨?_, ?_⟩
  taint_decide_all

theorem pbkdf2 : Verified RISCV64.target F.pbkdf2 (Spec.Hmac.sha1I.pbkdf2Contract RISCV64.abi (F.itB + F.frB + F.X)) :=
  shared okF checks rfl (by
    inst_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
      Spec.Pbkdf2.pbkdf2Pre, Spec.Hmac.sha1I, Spec.Hmac.sha1S, Spec.Hmac.sha1, Impl.Pbkdf2.Whole.RISCV64.Fns.itB,
      Impl.Pbkdf2.Whole.RISCV64.Fns.frB, Impl.Pbkdf2.Whole.RISCV64.Fns.X, Impl.Pbkdf2.Whole.RISCV64.Fns.bytes,
      Impl.Pbkdf2.Whole.RISCV64.Fns.intO, Impl.Pbkdf2.Whole.RISCV64.Fns.tO, Impl.Pbkdf2.Whole.RISCV64.Fns.uO,
      Impl.Pbkdf2.Whole.RISCV64.Fns.stWO, Impl.Pbkdf2.Whole.RISCV64.Fns.st1O, Impl.Pbkdf2.Whole.RISCV64.Fns.st0O,
      F, Proof.Hmac.Stream.RISCV64.Sha1.hash, Impl.Hmac.Stream.RISCV64.Hash.ibytes, Impl.Hmac.Stream.RISCV64.Hash.fbytes,
      Impl.Hmac.Stream.RISCV64.Hash.iso, Impl.Hmac.Stream.RISCV64.Hash.fso, RISCV64.abi, RISCV64.argRegs]
      using pbkSat)

end VG.Proof.Pbkdf2.Whole.RISCV64.Sha1
