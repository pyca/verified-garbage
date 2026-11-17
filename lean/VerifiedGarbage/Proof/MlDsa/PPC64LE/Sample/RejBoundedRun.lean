module

import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.Pro
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Sample.RejBounded
public import VerifiedGarbage.Proof.MlDsa.Sample.RejBounded
public import VerifiedGarbage.Proof.MlDsa.Sample.HalfByte
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `MlDsa.PPC64LE.Sample.RejBoundedBody`, which this module and modules that import it used -/

section

/-!
# ML-DSA on PPC64LE: an iteration of `vg_mldsa_rej_bounded_poly`

As on 32-bit ARM (`Proof/MlDsa/Arm/Sample/RejBoundedBody.lean`), but each
half-byte is tried the same way: its coefficient computed without a branch
(`rbF`, the coefficient of `CoeffFromHalfByte` modulo `q` on the accepted
half-bytes, `rbF_eq`, by evaluation) and `r12` the test of whether it is
accepted and `j < 256` (`accH`), both from `half_ok`; then `accept` stores the
coefficient if so (`try_ok`), which is what `tryJ` does to the coefficients.
An iteration tries the low and then the high half-byte of its byte, which is
what `rbStep` does (`rbStep_tryJ`, `body_ok`). Between the pieces, `Base`
holds: the environment, the XOF output, the pointer `r3` to the byte of
iteration `t`, the count `r6`, `q` in `r7`, and the coefficients `L` stored
(`At`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Sample.RejBounded

open VG VG.PPC64LE
open VG.Proof.MlDsa.PPC64LE.Sample
open VG.Impl.MlDsa.PPC64LE.Sample
open VG.Proof.MlDsa.Sample (hbTry rbStep rbFold Stored zw ifT ifF hbTry_length halfByteOk_le rbFold_snoc rbFold_append rbFold_full
  rbFold_length_le rbB rbC hbTry_eq halfByteOk_eq)
open VG.Proof.MlKem.PPC64LE (ptr_add count_sub count_nz)
open VG.Proof.MlKem.PPC64LE.Sample (read_one toNat_setWidth8)
open VG.Spec.MlDsa (Zq q ofInt halfByteOk)
open VG.Spec.Sha3 (bytesAt)

/-! ## A half-byte -/

/-- Nonzero exactly when the half-byte `x` is less than `B` and `j < 256`, as
`testJ` computes it. -/
def accH (x : BitVec 64) (B : Nat) (j : BitVec 64) : BitVec 64 :=
  (x - BitVec.ofNat 64 B) >>> 63 &&& (j - BitVec.ofNat 64 256) >>> 63

theorem accH_val {b B j : Nat} (hb : b < 16) (hB : B ≤ 15) (hj : j ≤ 256) :
    accH (BitVec.ofNat 64 b) B (BitVec.ofNat 64 j) = if b < B ∧ j < 256 then 1 else 0 := by
  unfold accH
  by_cases h1 : b < B <;> by_cases h2 : j < 256
  · have e1 : (BitVec.ofNat 64 b - BitVec.ofNat 64 B) >>> 63 = 1 := by bv_omega
    have e2 : (BitVec.ofNat 64 j - BitVec.ofNat 64 256) >>> 63 = 1 := by bv_omega
    rw [e1, e2]; simp [h1, h2]
  · have e2 : (BitVec.ofNat 64 j - BitVec.ofNat 64 256) >>> 63 = 0 := by bv_omega
    rw [e2]; simp [h1, h2]
  · have e1 : (BitVec.ofNat 64 b - BitVec.ofNat 64 B) >>> 63 = 0 := by bv_omega
    rw [e1]; simp [h1, h2]
  · have e1 : (BitVec.ofNat 64 b - BitVec.ofNat 64 B) >>> 63 = 0 := by bv_omega
    rw [e1]; simp [h1, h2]

/-- `x - 10` if `10 ≤ x`, as `csub 10` computes it. -/
def cs10 (x : BitVec 64) : BitVec 64 :=
  x - BitVec.ofNat 64 10 + (x - BitVec.ofNat 64 10) >>> 63 <<< 3 + (x - BitVec.ofNat 64 10) >>> 63 <<< 1

/-- `x - 5` if `5 ≤ x`, as `csub 5` computes it. -/
def cs5 (x : BitVec 64) : BitVec 64 :=
  x - BitVec.ofNat 64 5 + (x - BitVec.ofNat 64 5) >>> 63 <<< 2 + (x - BitVec.ofNat 64 5) >>> 63

/-- `v + q` if `v` is negative, as `addQNeg` computes it. -/
def aq (v : BitVec 64) : BitVec 64 := v + v >>> 63 * BitVec.ofNat 64 8380417

/-- What `rbVal η` computes of the half-byte `x`. -/
def rbF : Nat → BitVec 64 → BitVec 64
  | 2, x => aq (BitVec.ofNat 64 2 - cs5 (cs10 x))
  | _, x => aq (BitVec.ofNat 64 4 - x)

theorem rbF_eq2 : ∀ b < 15, (rbF 2 (BitVec.ofNat 64 b)).setWidth 32 = zw (ofInt (rbC 2 b)) := by decide

theorem rbF_eq4 : ∀ b < 9, (rbF 4 (BitVec.ofNat 64 b)).setWidth 32 = zw (ofInt (rbC 4 b)) := by decide

theorem rbF_eq {η : Nat} (hη : η = 2 ∨ η = 4) {b : Nat} (hb : b < rbB η) :
    (rbF η (BitVec.ofNat 64 b)).setWidth 32 = zw (ofInt (rbC η b)) := by
  rcases hη with rfl | rfl
  · exact rbF_eq2 b hb
  · exact rbF_eq4 b hb

theorem rbB_two : rbB 2 = 15 := rfl

theorem csub_ten : csub 10 = [.subi .r9 .r9 10, .lsr .d .r11 .r9 63, .lsl .r10 .r11 3, .add .r9 .r9 .r10,
    .lsl .r10 .r11 1, .add .r9 .r9 .r10] := rfl

theorem csub_five : csub 5 = [.subi .r9 .r9 5, .lsr .d .r11 .r9 63, .lsl .r10 .r11 2, .add .r9 .r9 .r10,
    .add .r9 .r9 .r11] := rfl

theorem rbB_four : rbB 4 = 9 := rfl

theorem rbB_le {η : Nat} : rbB η ≤ 15 := by unfold rbB; split <;> omega_using []

/-- The block of a half-byte: `r10` its coefficient, `r12` the test. -/
theorem half_run {η : Nat} (hη : η = 2 ∨ η = 4) (s : State) (h7 : s.gpr .r7 = BitVec.ofNat 64 8380417) :
    WP isa (.block (rbHalf η)) s fun t =>
      t.gpr .r10 = rbF η (s.gpr .r9) ∧ t.gpr .r12 = accH (s.gpr .r9) (rbB η) (s.gpr .r5) ∧
      (∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  rcases hη with rfl | rfl
  · prun [rbHalf, testJ, rbVal, csub_ten, csub_five, addQNeg, rbBound, rbB_two, rbF, cs10, cs5, aq, accH, List.cons_append,
      List.nil_append, List.append_assoc, exec_mul, ↓reduceIte, h7]
    simp only [true_and, and_true]
    intro r a b c d
    simp only [RegUpd.gpr_write, a, b, c, d, ite_false]
  · prun [rbHalf, testJ, rbVal, addQNeg, rbBound, rbB_four, rbF, aq, accH, List.cons_append, List.nil_append,
      List.append_assoc, exec_mul, ↓reduceIte, h7]
    simp only [true_and, and_true]
    intro r _ b c d
    simp only [RegUpd.gpr_write, b, c, d, ite_false]

/-! ## The invariant between the pieces -/

/-- The call, from its entry state: `seed = r3`, `eta = r4`, `a = r5`,
`scratch = r6`. -/
abbrev spOf (σ : State) : Sp := ⟨σ.gpr .r3, 66, σ.gpr .r6, σ.gpr .r5⟩

/-- `η`, the low 32 bits of `r4`. -/
abbrev etaOf (σ : State) : Nat := ((σ.gpr .r4).setWidth 32).toNat

/-- The XOF output a loop uses: `n` bytes of `H(ρ)`. -/
abbrev X (n : Nat) (σ : State) : List Byte := Spec.MlDsa.H ((spOf σ).msg σ) n

theorem X_length (n : Nat) (σ : State) : (X n σ).length = n := Proof.MlDsa.Sample.H_length _ _

/-- The byte of iteration `t`. -/
abbrev zAt (X : List Byte) (t : Nat) : Byte := X.getD t 0

/-- Iteration `t`, with the coefficients `L` stored, for the XOF output `X`. -/
structure Base (σ : State) (X : List Byte) (t : Nat) (L : List Zq) (s : State) : Prop where
  env : Env (spOf σ) σ s
  xlen : X.length ≤ 544
  out : bytesAt s.mem ((spOf σ).at' 840) X.length = X
  r3 : s.gpr .r3 = σ.gpr .r6 + BitVec.ofNat 64 (840 + t)
  r6 : s.gpr .r6 = BitVec.ofNat 64 (X.length - t)
  r7 : s.gpr .r7 = BitVec.ofNat 64 8380417
  r27 : s.gpr .r27 = zx (σ.gpr .r4)
  r28 : s.gpr .r28 = BitVec.ofNat 64 66
  r29 : s.gpr .r29 = σ.gpr .r3
  at' : At (spOf σ) L s

section
variable {σ : State} (hp : SpOk (spOf σ) σ)
include hp

/-- `Base` through a block that writes no memory and only `r8`–`r12`. -/
theorem Base.keep {X : List Byte} {t : Nat} {L : List Zq} {s s' : State} (h : Base σ X t L s)
    (hm : s'.mem = s.mem)
    (g : ∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → s'.gpr r = s.gpr r) (rd : s'.rd = s.rd)
    (wr : s'.wr = s.wr) (sp : s'.sp = s.sp) : Base σ X t L s' := by
  have gp : ∀ r ∈ preserved, s'.gpr r = s.gpr r := fun r hr =>
    g r (by rintro rfl; exact absurd hr (by decide)) (by rintro rfl; exact absurd hr (by decide))
      (by rintro rfl; exact absurd hr (by decide)) (by rintro rfl; exact absurd hr (by decide))
      (by rintro rfl; exact absurd hr (by decide))
  exact ⟨h.env.regs hp hm gp rd wr sp, h.xlen, by rw [hm]; exact h.out, (g _ (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans h.r3, (g _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.r6,
    (g _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.r7,
    (gp _ (by decide)).trans h.r27, (gp _ (by decide)).trans h.r28, (gp _ (by decide)).trans h.r29,
    ⟨(g _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.at'.r4,
      (g _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.at'.r5, h.at'.len,
      by rw [hm]; exact h.at'.st⟩⟩

end

/-! ## A try -/

/-- The half-byte `b` tried while `j < 256`: what a half-byte of the loop does. -/
def tryJ (η : Nat) (L : List Zq) (b : Nat) : List Zq := if L.length < 256 then hbTry η L b else L

theorem tryJ_length (η : Nat) (L : List Zq) (b : Nat) :
    (tryJ η L b).length = if L.length < 256 then L.length + halfByteOk η b else L.length := by
  unfold tryJ; split <;> simp only [hbTry_length]

/-- An iteration, as two tries. -/
theorem rbStep_tryJ (η : Nat) (L : List Zq) (z : Byte) :
    rbStep η L z = tryJ η (tryJ η L (z.toNat % 16)) (z.toNat / 16) := by
  unfold rbStep tryJ
  by_cases h : L.length < 256
  · rw [ifT (show L.length < Spec.MlDsa.n from h), ifT h]
  · rw [ifF (show ¬ L.length < Spec.MlDsa.n from h), ifF h, ifF h]

/-- After the block of the half-byte `b`: its coefficient in `r10`, the test
in `r12`, `r8` = `v`. -/
structure H1 (η : Nat) (σ : State) (X : List Byte) (t : Nat) (L : List Zq) (b : Nat) (v : BitVec 64)
    (s : State) : Prop where
  base : Base σ X t L s
  r8 : s.gpr .r8 = v
  r10 : s.gpr .r10 = rbF η (BitVec.ofNat 64 b)
  r12 : s.gpr .r12 = accH (BitVec.ofNat 64 b) (rbB η) (BitVec.ofNat 64 L.length)

section
variable {σ : State} (hp : SpOk (spOf σ) σ)
include hp

theorem half_ok {η : Nat} (hη : η = 2 ∨ η = 4) {X : List Byte} {t : Nat} {L : List Zq} {b : Nat} {s : State}
    (h : Base σ X t L s) (h9 : s.gpr .r9 = BitVec.ofNat 64 b) :
    WP isa (.block (rbHalf η)) s (H1 η σ X t L b (s.gpr .r8)) :=
  WP.mono (half_run hη s h.r7) fun s' ⟨g10, g12, g, m, rd, wr, sp⟩ =>
    ⟨h.keep hp m (fun r _ a b c d => g r a b c d) rd wr sp, g .r8 (by decide) (by decide) (by decide) (by decide),
      by rw [g10, h9], by rw [g12, h9, h.at'.r5]⟩

/-- `accept` after the block of a half-byte: what `tryJ` does. -/
theorem try_ok {η : Nat} (hη : η = 2 ∨ η = 4) {X : List Byte} {t : Nat} {L : List Zq} {b : Nat} (hb : b < 16)
    {v : BitVec 64} {s : State} (h : H1 η σ X t L b v s) :
    WP isa (accept .r10) s fun s' => Base σ X t (tryJ η L b) s' ∧ s'.gpr .r8 = v := by
  have l := h.base
  have hlen := l.at'.len
  have ea := accH_val hb (rbB_le (η := η)) hlen
  rw [← h.r12] at ea
  unfold tryJ
  rw [hbTry_eq hη]
  by_cases hz : s.gpr .r12 = 0
  · have hn : ¬ (b < rbB η ∧ L.length < 256) := fun hc => by rw [hz, ifT hc] at ea; exact absurd ea (by decide)
    have e : (if L.length < 256 then (if b < rbB η then L ++ [ofInt (rbC η b)] else L) else L) = L := by
      by_cases hl : L.length < 256
      · rw [ifT hl, ifF (fun hc => hn ⟨hc, hl⟩)]
      · rw [ifF hl]
    rw [e]
    exact WP.mono (accept_skip hz) fun s' e' => by subst e'; exact ⟨l, h.r8⟩
  · have hy : b < rbB η ∧ L.length < 256 := by
      by_contra hc; rw [ifF hc] at ea; exact hz ea
    rw [ifT hy.2, ifT hy.1]
    refine WP.mono (accept_store hp l.env l.at' hy.2 (x := ofInt (rbC η b)) (by rw [h.r10]; exact rbF_eq hη hy.1) hz)
      fun s' ⟨at', env', rr, hf⟩ => ⟨⟨env', l.xlen, ?_, (rr _ (by decide) (by decide)).trans l.r3,
        (rr _ (by decide) (by decide)).trans l.r6, (rr _ (by decide) (by decide)).trans l.r7,
        (rr _ (by decide) (by decide)).trans l.r27, (rr _ (by decide) (by decide)).trans l.r28,
        (rr _ (by decide) (by decide)).trans l.r29, at'⟩,
        (rr _ (by decide) (by decide)).trans h.r8⟩
    rw [MlKem.bytesAt_frame hf (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact (hp.a_scr.sub_right (sub_scr (a := 840) (n := X.length) (by have := l.xlen; omega_using [this]))).symm) (by have := l.xlen; omega_using [this])]
    exact l.out

/-! ## An iteration -/

/-- The byte of iteration `t`. -/
theorem byte_ok {X : List Byte} {t : Nat} (ht : t < X.length) {L : List Zq} {s : State} (h : Base σ X t L s) :
    InRegions (s.rd ++ s.wr) (s.gpr .r3) 1 ∧ s.mem (s.gpr .r3) = zAt X t := by
  rw [h.r3]
  have := h.xlen
  refine ⟨by rw [← BitVec.add_zero (σ.gpr .r6 + _), ptr_add]; exact inScrRd hp h.env.wr (by omega_using [ht, this]), ?_⟩
  have := congrArg (fun L => L.getD t 0) h.out
  rw [MlKem.bytesAt_getD _ _ (by omega_using [ht]), ptr_add] at this
  exact this

omit hp in
/-- The low half-byte of a byte, as the code computes it. -/
theorem lo_eq (z : Byte) : z.setWidth 64 <<< 60 >>> 60 = BitVec.ofNat 64 (z.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  have := z.isLt
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, toNat_setWidth8, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega_using []

omit hp in
/-- The high half-byte of a byte, as the code computes it. -/
theorem hi_eq (z : Byte) : z.setWidth 64 >>> 4 = BitVec.ofNat 64 (z.toNat / 16) := by
  apply BitVec.eq_of_toNat_eq
  have := z.isLt
  rw [BitVec.toNat_ushiftRight, toNat_setWidth8, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega_using []

/-- The load of the byte and its low half-byte. -/
theorem lo_ok {X : List Byte} {t : Nat} (ht : t < X.length) {L : List Zq} {s : State} (h : Base σ X t L s) :
    WP isa (.block [.lbz .r8 .r3 0, .lsl .r9 .r8 60, .lsr .d .r9 .r9 60]) s fun s' =>
      Base σ X t L s' ∧ s'.gpr .r8 = (zAt X t).setWidth 64 ∧
        s'.gpr .r9 = BitVec.ofNat 64 ((zAt X t).toNat % 16) := by
  obtain ⟨i0, v0⟩ := byte_ok hp ht h
  have hk : WP isa (.block [.lbz .r8 .r3 0, .lsl .r9 .r8 60, .lsr .d .r9 .r9 60]) s fun s' =>
      s'.gpr .r8 = (zAt X t).setWidth 64 ∧ s'.gpr .r9 = (zAt X t).setWidth 64 <<< 60 >>> 60 ∧
      (∀ r, r ≠ .r8 → r ≠ .r9 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
    prun [exec_lbz, read_one, i0, v0]
    simp only [true_and, and_true]
    intro r a b
    simp only [RegUpd.gpr_write, a, b, ite_false]
  refine WP.mono hk fun s' ⟨g8, g9, g, m, rd, wr, sp⟩ =>
    ⟨h.keep hp m (fun r a b _ _ _ => g r a b) rd wr sp, g8, by rw [g9, lo_eq]⟩

/-- The load of the byte and the block of its low half-byte. -/
theorem loHalf_ok {η : Nat} (hη : η = 2 ∨ η = 4) {X : List Byte} {t : Nat} (ht : t < X.length) {L : List Zq}
    {s : State} (h : Base σ X t L s) :
    WP isa (.block (([.lbz .r8 .r3 0, .lsl .r9 .r8 60, .lsr .d .r9 .r9 60] : List Instr) ++ rbHalf η)) s
      (H1 η σ X t L ((zAt X t).toNat % 16) ((zAt X t).setWidth 64)) := by
  rw [WP.block_append_iff]
  exact WP.mono (lo_ok hp ht h) fun s1 ⟨b1, e8, e9⟩ => e8 ▸ half_ok hp hη b1 e9

/-- The block of the high half-byte, from the byte in `r8`. -/
theorem hiHalf_ok {η : Nat} (hη : η = 2 ∨ η = 4) {X : List Byte} {t : Nat} {L : List Zq} {s : State}
    (h : Base σ X t L s) (h8 : s.gpr .r8 = (zAt X t).setWidth 64) :
    WP isa (.block (.lsr .d .r9 .r8 4 :: rbHalf η)) s
      (H1 η σ X t L ((zAt X t).toNat / 16) ((zAt X t).setWidth 64)) := by
  rw [← List.singleton_append, WP.block_append_iff]
  have hk : WP isa (.block [.lsr .d .r9 .r8 4]) s fun s4 => s4 = s.write .r9 (s.gpr .r8 >>> 4) := by prun []
  refine WP.mono hk fun s4 e4 => ?_
  subst e4
  have b4 : Base σ X t L (s.write .r9 (s.gpr .r8 >>> 4)) :=
    h.keep hp rfl (fun r _ a _ _ _ => RegUpd.gpr_write_of_ne _ _ a) rfl rfl rfl
  have h9 : (s.write .r9 (s.gpr .r8 >>> 4)).gpr .r9 = BitVec.ofNat 64 ((zAt X t).toNat / 16) := by
    rw [RegUpd.gpr_write_self, h8, hi_eq]
  have e : (s.write .r9 (s.gpr .r8 >>> 4)).gpr .r8 = (zAt X t).setWidth 64 := by
    rw [RegUpd.gpr_write_of_ne _ _ (by decide), h8]
  exact e ▸ half_ok hp hη b4 h9

/-- The tries of an iteration, from its start, then `rest`. -/
theorem tries_ok {η : Nat} (hη : η = 2 ∨ η = 4) {X : List Byte} {t : Nat} (ht : t < X.length) {L : List Zq}
    {s : State} (h : Base σ X t L s) {rest : Prog isa} {Q : State → Prop}
    (hr : ∀ s', Base σ X t (rbStep η L (zAt X t)) s' → WP isa rest s' Q) :
    WP isa (.seq (.block (([.lbz .r8 .r3 0, .lsl .r9 .r8 60, .lsr .d .r9 .r9 60] : List Instr) ++ rbHalf η))
      (.seq (accept .r10) (.seq (.block (.lsr .d .r9 .r8 4 :: rbHalf η)) (.seq (accept .r10) rest)))) s Q := by
  rw [rbStep_tryJ] at hr
  refine WP.seq (WP.mono (loHalf_ok hp hη ht h) fun s2 h2 => ?_)
  refine WP.seq (WP.mono (try_ok hp hη (Nat.mod_lt _ (by decide)) h2) fun s3 ⟨b3, f8⟩ => ?_)
  refine WP.seq (WP.mono (hiHalf_ok hp hη b3 f8) fun s5 h5 => ?_)
  exact WP.seq (WP.mono (try_ok hp hη (by have := (zAt X t).isLt; omega_using []) h5) fun s6 h6 => hr s6 h6.1)

omit hp in
/-- The test of the step: `r12` nonzero iff bytes are left and `j < 256`. -/
theorem exit_val {N t j : Nat} (ht : t < N) (hN : N < 2 ^ 63) (hj : j ≤ 256) :
    (BitVec.ofNat 64 (N - (t + 1)) * ((BitVec.ofNat 64 j - BitVec.ofNat 64 256) >>> 63) != 0) =
      decide (t + 1 ≠ N ∧ j < 256) := by
  by_cases hj' : j < 256
  · have e : (BitVec.ofNat 64 j - BitVec.ofNat 64 256) >>> 63 = 1 := by bv_omega
    rw [e, show ∀ x : BitVec 64, x * 1 = x from fun x => by bv_omega, count_nz ht (by omega_using [hN])]
    simp [hj']
  · have e : (BitVec.ofNat 64 j - BitVec.ofNat 64 256) >>> 63 = 0 := by bv_omega
    rw [e, show ∀ x : BitVec 64, x * 0 = 0 from fun x => by bv_omega]
    simp [hj']

/-- The step, to iteration `t + 1`: `r12` zero iff it was the last or `j = 256`. -/
theorem step_ok {X : List Byte} {t : Nat} (ht : t < X.length) {L : List Zq} {s : State} (h : Base σ X t L s) :
    WP isa (.block stepBlk) s fun s' =>
      Base σ X (t + 1) L s' ∧ (s'.gpr .r12 != 0) = decide (t + 1 ≠ X.length ∧ L.length < 256) := by
  have hk : WP isa (.block stepBlk) s fun s' =>
      s'.gpr .r3 = s.gpr .r3 + BitVec.ofNat 64 1 ∧ s'.gpr .r6 = s.gpr .r6 - BitVec.ofNat 64 1 ∧
      s'.gpr .r12 = (s.gpr .r6 - BitVec.ofNat 64 1) * ((s.gpr .r5 - BitVec.ofNat 64 256) >>> 63) ∧
      (∀ r, r ≠ .r3 → r ≠ .r6 → r ≠ .r11 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
    prun [stepBlk, exec_mul]
    simp only [true_and, and_true]
    intro r a b c d
    simp only [RegUpd.gpr_write, a, b, c, d, ite_false]
  have hx := h.xlen
  refine WP.mono hk fun s' ⟨r3, r6, r12, g, m, rd, wr, sp⟩ => ⟨⟨?_, h.xlen, by rw [m]; exact h.out, ?_, ?_,
    (g _ (by decide) (by decide) (by decide) (by decide)).trans h.r7,
    (g _ (by decide) (by decide) (by decide) (by decide)).trans h.r27,
    (g _ (by decide) (by decide) (by decide) (by decide)).trans h.r28,
    (g _ (by decide) (by decide) (by decide) (by decide)).trans h.r29,
    ⟨(g _ (by decide) (by decide) (by decide) (by decide)).trans h.at'.r4,
      (g _ (by decide) (by decide) (by decide) (by decide)).trans h.at'.r5, h.at'.len, by rw [m]; exact h.at'.st⟩⟩, ?_⟩
  · exact h.env.regs hp m (fun r hr => g r (by rintro rfl; exact absurd hr (by decide))
      (by rintro rfl; exact absurd hr (by decide)) (by rintro rfl; exact absurd hr (by decide))
      (by rintro rfl; exact absurd hr (by decide))) rd wr sp
  · rw [r3, h.r3, ptr_add, Nat.add_assoc]
  · rw [r6, h.r6]; exact count_sub ht
  · rw [r12, h.r6, h.at'.r5, count_sub ht]; exact exit_val ht (by omega_using [hx]) h.at'.len

end

/-- The coefficients after `t` iterations. -/
abbrev Lf (η : Nat) (X : List Byte) (t : Nat) : List Zq := rbFold η [] (X.take t)

theorem take_succ' (L : List Byte) {i : Nat} (h : i < L.length) : L.take (i + 1) = L.take i ++ [L.getD i 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem Lf_succ (η : Nat) {X : List Byte} {t : Nat} (ht : t < X.length) :
    Lf η X (t + 1) = rbStep η (Lf η X t) (zAt X t) := by
  simp only [Lf]
  rw [take_succ' _ (by omega_using [ht]), rbFold_snoc]

/-- After the last byte, or once there are 256 coefficients, the bytes left
change nothing. -/
theorem Lf_stop {η : Nat} {X : List Byte} {t N : Nat} (htN : t ≤ N) (h : t = N ∨ (Lf η X t).length = 256) :
    Lf η X N = Lf η X t := by
  rcases h with rfl | h
  · rfl
  simp only [Lf] at h ⊢
  have e : X.take N = X.take t ++ (X.take N).drop t := by
    have := List.take_append_drop t (X.take N)
    rw [List.take_take, Nat.min_eq_left htN] at this
    exact this.symm
  rw [e, rbFold_append, rbFold_full h]

/-- An iteration: what `rbStep` does to the coefficients. -/
theorem body_ok {σ : State} (hp : SpOk (spOf σ) σ) {η : Nat} (hη : η = 2 ∨ η = 4) {X : List Byte}
    {t : Nat} (ht : t < X.length) {s : State} (h : Base σ X t (Lf η X t) s) :
    WP isa (rbBody η) s fun s' => Base σ X (t + 1) (Lf η X (t + 1)) s' ∧
      (s'.gpr .r12 != 0) = decide (t + 1 ≠ X.length ∧ (Lf η X (t + 1)).length < 256) := by
  rw [Lf_succ η ht]
  exact tries_ok hp hη ht h fun _ h' => step_ok hp ht h'

end VG.Proof.MlDsa.PPC64LE.Sample.RejBounded

end

end

/-!
# ML-DSA on PPC64LE: `vg_mldsa_rej_bounded_poly`, correctness

As on 32-bit ARM (`Proof/MlDsa/Arm/Sample/RejBoundedRun.lean`). The function
runs in pieces: the prologue (`J0`, with `η` zero-extended in `r27`), the
sponge, whose output is `H(ρ, n)` (`J6`), the branch on `η` (`sel_ok`), and
the loop for `η`, iteration `t` of which starts from `Base` with the
coefficients `rbFold` samples from the first `t` bytes of output stored
(`loop_ok`): a try (`rbTry_ok`), with 272 bytes, then, if it did not sample 256
coefficients (`jtest_ok`), with 544; then the end returns whether there are
256 (`correct`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Sample.RejBounded

open VG VG.PPC64LE
open VG.Proof.MlDsa.PPC64LE.Sample
open VG.Impl.MlDsa.PPC64LE.Sample
open VG.Impl.Sha3.PPC64LE.Stream (mov)
open VG.Proof.MlDsa.Sample (Stored stored_nil H_eq rbFold ifT ifF rbFold_length_le)
open VG.Proof.MlKem.PPC64LE (wp_loop_nz)
open VG.Spec.MlDsa (Zq H)
open VG.Spec.Sha3 (bytesAt)

/-- `J6` for `n` bytes, and `η` zero-extended in `r27`. -/
structure SJ (n : Nat) (σ s : State) : Prop where
  j6 : ∃ s₀, J6 136 n (spOf σ) σ s₀ s
  r27 : s.gpr .r27 = zx (σ.gpr .r4)

section
variable {σ : State} (hp : SpOk (spOf σ) σ)
include hp

/-- The loop's setup, after the sponge. -/
theorem init_ok {n : Nat} (hn : n ≤ 544) {s : State} (h : SJ n σ s) :
    WP isa (.block (([.addi .r3 .r31 840, mov .r4 .r30, .li .r5 0, .li .r6 n] : List Instr) ++ loadQ)) s
      (Base σ (X n σ) 0 []) := by
  obtain ⟨⟨s₀, h⟩, e27⟩ := h
  have g30 := h.j0.env.r30
  have g31 := h.j0.env.r31
  have hn' : n < 32768 := by omega_using [hn]
  have hk : WP isa (.block (([.addi .r3 .r31 840, mov .r4 .r30, .li .r5 0, .li .r6 n] : List Instr) ++ loadQ)) s
      fun s' => s'.gpr .r3 = σ.gpr .r6 + BitVec.ofNat 64 (840 + 0) ∧ s'.gpr .r4 = σ.gpr .r5 ∧
        s'.gpr .r5 = BitVec.ofNat 64 0 ∧ s'.gpr .r6 = BitVec.ofNat 64 n ∧
        s'.gpr .r7 = BitVec.ofNat 64 8380417 ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
    prun [loadQ, List.cons_append, List.nil_append, exec_lis, exec_ori, loadQ_val, g30, g31, hn']
    simp only [true_and, and_true]
    pres_tac
  refine WP.mono hk fun s' ⟨g3, g4, g5, g6, g7, gp, m, rd, wr, sp⟩ => ⟨h.j0.env.regs hp m gp rd wr sp,
    by rw [X_length]; exact hn, by rw [m, X_length, h.out]; exact (H_eq _ _).symm, g3, by rw [X_length, Nat.sub_zero]; exact g6, g7,
    (gp _ (by decide)).trans e27, (gp _ (by decide)).trans h.j0.r28, (gp _ (by decide)).trans h.j0.r29, ?_⟩
  exact ⟨by rw [g4]; exact (BitVec.add_zero _).symm, g5, by simp, stored_nil _ _⟩

/-- The loop for `η`, over `n` bytes: it stops after the last byte or once
there are 256 coefficients, which are then those of all `n` bytes. -/
theorem loop_ok {η : Nat} (hη : η = 2 ∨ η = 4) {n : Nat} (hn0 : 0 < n) (hn : n ≤ 544) {s : State}
    (h : SJ n σ s) : WP isa (rbLoop η n) s fun s' => ∃ t, Base σ (X n σ) t (Lf η (X n σ) n) s' := by
  refine WP.seq (WP.mono (init_ok hp hn h) fun s0 h0 => ?_)
  refine WP.loop (M := isa) (c := .nonzero .d .r12) (fun m s => ∃ i, i < n ∧ m = n - i ∧
    Base σ (X n σ) i (Lf η (X n σ) i) s ∧ (Lf η (X n σ) i).length < 256) ?_ n s0
    ⟨0, hn0, rfl, by simpa [Lf, rbFold] using h0, by simp [Lf, rbFold]⟩
  rintro m s ⟨i, hi, rfl, hs, -⟩
  refine WP.mono (body_ok hp hη (X := X n σ) (by rw [X_length]; exact hi) hs) fun s' ⟨hs', hz⟩ => ?_
  rw [X_length] at hz
  have ev : isa.eval (.nonzero .d .r12) s' =
      some (decide (i + 1 ≠ n ∧ (Lf η (X n σ) (i + 1)).length < 256)) := by rw [eval_nonzero, hz]
  by_cases hc : i + 1 ≠ n ∧ (Lf η (X n σ) (i + 1)).length < 256
  · exact .inr ⟨by rw [ev, decide_eq_true hc], n - (i + 1), by omega_using [hi], i + 1, by omega_using [hi, hc], rfl, hs', hc.2⟩
  · refine .inl ⟨by rw [ev, decide_eq_false hc], i + 1, ?_⟩
    have hle := rbFold_length_le (η := η) (a := []) (by simp) ((X n σ).take (i + 1))
    rw [Lf_stop (show i + 1 ≤ n by omega_using [hi]) (by
      by_cases e : i + 1 = n
      · exact .inl e
      · have h1 := not_and.mp hc e
        have hle' : (Lf η (X n σ) (i + 1)).length ≤ 256 := hle
        exact .inr (by omega_using [h1, hle']))]
    exact hs'

omit hp in
/-- The test of `η = 2`. -/
theorem eta_test (x : BitVec 64) : (zx x - BitVec.ofNat 64 2 == 0) = decide ((x.setWidth 32).toNat = 2) := by
  have e := zx_toNat x
  by_cases h : (x.setWidth 32).toNat = 2
  · have : zx x - BitVec.ofNat 64 2 = 0 := by bv_omega
    rw [this, decide_eq_true h]; rfl
  · have : zx x - BitVec.ofNat 64 2 ≠ 0 := by bv_omega
    rw [decide_eq_false h]; exact beq_eq_false_iff_ne.mpr this

/-- The test of `η = 2`, which keeps `J6`. -/
theorem cmp_ok {n : Nat} {s : State} (h : SJ n σ s) :
    WP isa (.block [.subi .r12 .r27 2]) s fun s' => SJ n σ s' ∧ s'.gpr .r12 = zx (σ.gpr .r4) - BitVec.ofNat 64 2 := by
  obtain ⟨⟨s₀, j6⟩, e27⟩ := h
  have hk : WP isa (.block [.subi .r12 .r27 2]) s fun s' => s' = s.write .r12 (s.gpr .r27 - BitVec.ofNat 64 2) := by
    prun []
  refine WP.mono hk fun s' e' => ?_
  subst e'
  have gp : ∀ r ∈ preserved, (s.write .r12 (s.gpr .r27 - BitVec.ofNat 64 2)).gpr r = s.gpr r := by pres_tac
  exact ⟨⟨⟨s₀, j6.j0.regs hp rfl gp rfl rfl rfl, fun r hr => (gp r hr).trans (j6.gp r hr), j6.out⟩,
    (gp .r27 (by decide)).trans e27⟩, by rw [RegUpd.gpr_write_self, e27]⟩

/-- The branch on `η`, and the loop for it. -/
theorem sel_ok (hη : etaOf σ = 2 ∨ etaOf σ = 4) {n : Nat} (hn0 : 0 < n) (hn : n ≤ 544) {s : State}
    (h : SJ n σ s) :
    WP isa (.seq (.block [.subi .r12 .r27 2]) (.ite (.zero .d .r12) (rbLoop 2 n) (rbLoop 4 n))) s
      fun s' => ∃ t, Base σ (X n σ) t (Lf (etaOf σ) (X n σ) n) s' := by
  refine WP.seq (WP.mono (cmp_ok hp h) fun s1 ⟨h1, e12⟩ => ?_)
  refine WP.ite _ (by rw [eval_zero, e12, eta_test]) (fun he => ?_) (fun he => ?_)
  · simp only [decide_eq_true_eq] at he
    rw [show etaOf σ = 2 from he]
    exact loop_ok hp (.inl rfl) hn0 hn h1
  · simp only [decide_eq_false_iff_not] at he
    rw [show etaOf σ = 4 from hη.resolve_left he]
    exact loop_ok hp (.inr rfl) hn0 hn h1

/-- A try with `n` bytes, from the registers of the sponge's arguments and
`η` in `r27`. -/
theorem rbTry_ok (hη : etaOf σ = 2 ∨ etaOf σ = 4) {n : Nat} (hn0 : 0 < n) (hn : n ≤ 544) {s : State}
    (j0 : J0 (spOf σ) σ s) (e27 : s.gpr .r27 = zx (σ.gpr .r4)) :
    WP isa (rbTry n) s fun s' => ∃ t, Base σ (X n σ) t (Lf (etaOf σ) (X n σ) n) s' :=
  WP.seq (WP.mono (sponge_ok hp (rate := 136) (outlen := n) (by decide) (by omega_using [hn]) j0) fun _ h =>
    sel_ok hp hη hn0 hn ⟨⟨s, h⟩, (h.gp .r27 (by decide)).trans e27⟩)

/-- The test of `j = 256`. -/
theorem jtest_ok {X : List Byte} {t : Nat} {L : List Zq} {s : State} (h : Base σ X t L s) :
    WP isa (.block [.subi .r12 .r5 256]) s fun s' => Base σ X t L s' ∧
      isa.eval (.zero .d .r12) s' = some (decide (L.length = 256)) := by
  have hk : WP isa (.block [.subi .r12 .r5 256]) s fun s' => s' = s.write .r12 (s.gpr .r5 - BitVec.ofNat 64 256) := by
    prun []
  refine WP.mono hk fun s' e' => ?_
  subst e'
  refine ⟨h.keep hp rfl (fun r _ _ _ _ a => RegUpd.gpr_write_of_ne _ _ a) rfl rfl rfl, ?_⟩
  rw [eval_zero, RegUpd.gpr_write_self, h.at'.r5]
  have hl := h.at'.len
  by_cases e : L.length = 256
  · rw [e]; rfl
  · rw [decide_eq_false e]
    exact congrArg some (beq_eq_false_iff_ne.mpr (by bv_omega))

/-- The coefficients the function samples: those of the first 272 bytes if
there are 256 of them, and those of 544 bytes otherwise. -/
abbrev Lr (η : Nat) (σ : State) : List Zq :=
  if (Lf η (X 272 σ) 272).length = 256 then Lf η (X 272 σ) 272 else Lf η (X 544 σ) 544

/-- The whole function: `r3` whether 256 coefficients were sampled, those
stored, and the calling convention. -/
theorem correct (hη : etaOf σ = 2 ∨ etaOf σ = 4) :
    WP isa rejBounded σ fun s' =>
      s'.gpr .r3 = (if (Lr (etaOf σ) σ).length = 256 then 1 else 0) ∧
      Stored s'.mem (σ.gpr .r5) (Lr (etaOf σ) σ) ∧ abiPreserved σ s' := by
  unfold rejBounded
  refine WP.seq (WP.mono (pro_rb hp rfl rfl rfl rfl) fun s₀ ⟨j0, e27⟩ => ?_)
  refine WP.seq (WP.mono (rbTry_ok hp hη (n := 272) (by decide) (by decide) j0 e27) fun s1 ⟨t1, h1⟩ => ?_)
  have fin : ∀ {X t s}, Base σ X t (Lr (etaOf σ) σ) s →
      WP isa (.block (retJ ++ epi)) s fun s' =>
        s'.gpr .r3 = (if (Lr (etaOf σ) σ).length = 256 then 1 else 0) ∧
        Stored s'.mem (σ.gpr .r5) (Lr (etaOf σ) σ) ∧ abiPreserved σ s' := fun h3 =>
    WP.mono (retEpi_ok hp h3.env h3.at'.r5 h3.at'.len) fun s' ⟨r3, hm, ha⟩ =>
      ⟨r3, by rw [hm]; exact h3.at'.st, ha⟩
  refine WP.seq (WP.seq (WP.mono (jtest_ok hp h1) fun s2 ⟨h2, ev⟩ =>
    WP.ite _ ev (fun he => ?_) (fun he => ?_)))
  · simp only [decide_eq_true_eq] at he
    refine WP.block_nil (fin (X := X 272 σ) (t := t1) ?_)
    rw [Lr, ifT he]; exact h2
  · simp only [decide_eq_false_iff_not] at he
    exact WP.mono (rbTry_ok hp hη (n := 544) (by decide) (by decide) ⟨h2.env, h2.r29, h2.r28⟩ h2.r27)
      fun s3 ⟨_, h3⟩ => fin (by rw [Lr, ifF he]; exact h3)

end

end VG.Proof.MlDsa.PPC64LE.Sample.RejBounded
