module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.Pro
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Sample.RejBounded
public import VerifiedGarbage.Proof.MlDsa.Sample.RejBounded
public import VerifiedGarbage.Proof.MlDsa.Sample.HalfByte
import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

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
open VG.Proof.MlDsa.Sample (hbTry rbStep rbFold Stored zw ifT ifF hbTry_length halfByteOk_le rbFold_snoc
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

theorem rbB_le {η : Nat} : rbB η ≤ 15 := by unfold rbB; split <;> omega

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

/-- The XOF output the function uses: 544 bytes of `H(ρ)`. -/
abbrev X (σ : State) : List Byte := Spec.MlDsa.H ((spOf σ).msg σ) 544

theorem X_length (σ : State) : (X σ).length = 544 := Proof.MlDsa.Sample.H_length _ _

/-- The byte of iteration `t`. -/
abbrev zAt (X : List Byte) (t : Nat) : Byte := X.getD t 0

/-- Iteration `t`, with the coefficients `L` stored, for the XOF output `X`. -/
structure Base (σ : State) (X : List Byte) (t : Nat) (L : List Zq) (s : State) : Prop where
  env : Env (spOf σ) σ s
  out : bytesAt s.mem ((spOf σ).at' 840) 544 = X
  r3 : s.gpr .r3 = σ.gpr .r6 + BitVec.ofNat 64 (840 + t)
  r6 : s.gpr .r6 = BitVec.ofNat 64 (544 - t)
  r7 : s.gpr .r7 = BitVec.ofNat 64 8380417
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
  exact ⟨h.env.regs hp hm gp rd wr sp, by rw [hm]; exact h.out, (g _ (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans h.r3, (g _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.r6,
    (g _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.r7,
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

theorem tryJ_length_le {η : Nat} {L : List Zq} (hL : L.length ≤ 256) (b : Nat) : (tryJ η L b).length ≤ 256 := by
  rw [tryJ_length]; have := halfByteOk_le η b; split <;> omega

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
      fun s' ⟨at', env', rr, hf⟩ => ⟨⟨env', ?_, (rr _ (by decide) (by decide)).trans l.r3,
        (rr _ (by decide) (by decide)).trans l.r6, (rr _ (by decide) (by decide)).trans l.r7, at'⟩,
        (rr _ (by decide) (by decide)).trans h.r8⟩
    rw [MlKem.bytesAt_frame hf (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact (hp.a_scr.sub_right (sub_scr (a := 840) (n := 544) (by decide))).symm) (by decide)]
    exact l.out

/-! ## An iteration -/

/-- The byte of iteration `t`. -/
theorem byte_ok {X : List Byte} {t : Nat} (ht : t < 544) {L : List Zq} {s : State} (h : Base σ X t L s) :
    InRegions (s.rd ++ s.wr) (s.gpr .r3) 1 ∧ s.mem (s.gpr .r3) = zAt X t := by
  rw [h.r3]
  refine ⟨by rw [← BitVec.add_zero (σ.gpr .r6 + _), ptr_add]; exact inScrRd hp h.env.wr (by omega), ?_⟩
  have := congrArg (fun L => L.getD t 0) h.out
  rw [MlKem.bytesAt_getD _ _ (by omega), ptr_add] at this
  exact this

omit hp in
/-- The low half-byte of a byte, as the code computes it. -/
theorem lo_eq (z : Byte) : z.setWidth 64 <<< 60 >>> 60 = BitVec.ofNat 64 (z.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  have := z.isLt
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, toNat_setWidth8, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega

omit hp in
/-- The high half-byte of a byte, as the code computes it. -/
theorem hi_eq (z : Byte) : z.setWidth 64 >>> 4 = BitVec.ofNat 64 (z.toNat / 16) := by
  apply BitVec.eq_of_toNat_eq
  have := z.isLt
  rw [BitVec.toNat_ushiftRight, toNat_setWidth8, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

/-- The load of the byte and its low half-byte. -/
theorem lo_ok {X : List Byte} {t : Nat} (ht : t < 544) {L : List Zq} {s : State} (h : Base σ X t L s) :
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
theorem loHalf_ok {η : Nat} (hη : η = 2 ∨ η = 4) {X : List Byte} {t : Nat} (ht : t < 544) {L : List Zq}
    {s : State} (h : Base σ X t L s) :
    WP isa (.block ([.lbz .r8 .r3 0, .lsl .r9 .r8 60, .lsr .d .r9 .r9 60] ++ rbHalf η)) s
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
theorem tries_ok {η : Nat} (hη : η = 2 ∨ η = 4) {X : List Byte} {t : Nat} (ht : t < 544) {L : List Zq}
    {s : State} (h : Base σ X t L s) {rest : Prog isa} {Q : State → Prop}
    (hr : ∀ s', Base σ X t (rbStep η L (zAt X t)) s' → WP isa rest s' Q) :
    WP isa (.seq (.block ([.lbz .r8 .r3 0, .lsl .r9 .r8 60, .lsr .d .r9 .r9 60] ++ rbHalf η))
      (.seq (accept .r10) (.seq (.block (.lsr .d .r9 .r8 4 :: rbHalf η)) (.seq (accept .r10) rest)))) s Q := by
  rw [rbStep_tryJ] at hr
  refine WP.seq (WP.mono (loHalf_ok hp hη ht h) fun s2 h2 => ?_)
  refine WP.seq (WP.mono (try_ok hp hη (Nat.mod_lt _ (by decide)) h2) fun s3 ⟨b3, f8⟩ => ?_)
  refine WP.seq (WP.mono (hiHalf_ok hp hη b3 f8) fun s5 h5 => ?_)
  exact WP.seq (WP.mono (try_ok hp hη (by have := (zAt X t).isLt; omega) h5) fun s6 h6 => hr s6 h6.1)

/-- The step, to iteration `t + 1`: `r6` zero iff it is the last. -/
theorem step_ok {X : List Byte} {t : Nat} (ht : t < 544) {L : List Zq} {s : State} (h : Base σ X t L s) :
    WP isa (.block [.addi .r3 .r3 1, .subi .r6 .r6 1]) s fun s' =>
      Base σ X (t + 1) L s' ∧ (s'.gpr .r6 != 0) = decide (t + 1 ≠ 544) := by
  have hk : WP isa (.block [.addi .r3 .r3 1, .subi .r6 .r6 1]) s fun s' =>
      s'.gpr .r3 = s.gpr .r3 + BitVec.ofNat 64 1 ∧ s'.gpr .r6 = s.gpr .r6 - BitVec.ofNat 64 1 ∧
      (∀ r, r ≠ .r3 → r ≠ .r6 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
    prun []
    simp only [true_and, and_true]
    intro r a b
    simp only [RegUpd.gpr_write, a, b, ite_false]
  refine WP.mono hk fun s' ⟨r3, r6, g, m, rd, wr, sp⟩ => ⟨⟨?_, by rw [m]; exact h.out, ?_, ?_,
    (g _ (by decide) (by decide)).trans h.r7, ⟨(g _ (by decide) (by decide)).trans h.at'.r4,
      (g _ (by decide) (by decide)).trans h.at'.r5, h.at'.len, by rw [m]; exact h.at'.st⟩⟩, ?_⟩
  · exact h.env.regs hp m (fun r hr => g r (by rintro rfl; exact absurd hr (by decide))
      (by rintro rfl; exact absurd hr (by decide))) rd wr sp
  · rw [r3, h.r3, ptr_add, Nat.add_assoc]
  · rw [r6, h.r6]; exact count_sub ht
  · rw [r6, h.r6, count_sub ht]; exact count_nz ht (by decide)

end

/-- The coefficients after `t` iterations. -/
abbrev Lf (η : Nat) (X : List Byte) (t : Nat) : List Zq := rbFold η [] (X.take t)

theorem take_succ' (L : List Byte) {i : Nat} (h : i < L.length) : L.take (i + 1) = L.take i ++ [L.getD i 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem Lf_succ (η : Nat) {X : List Byte} (hX : X.length = 544) {t : Nat} (ht : t < 544) :
    Lf η X (t + 1) = rbStep η (Lf η X t) (zAt X t) := by
  simp only [Lf]
  rw [take_succ' _ (by omega), rbFold_snoc]

theorem Lf_length_le (η : Nat) (X : List Byte) (t : Nat) : (Lf η X t).length ≤ 256 := rbFold_length_le (by simp) _

/-- An iteration: what `rbStep` does to the coefficients. -/
theorem body_ok {σ : State} (hp : SpOk (spOf σ) σ) {η : Nat} (hη : η = 2 ∨ η = 4) {X : List Byte}
    (hX : X.length = 544) {t : Nat} (ht : t < 544) {s : State} (h : Base σ X t (Lf η X t) s) :
    WP isa (rbBody η) s fun s' => Base σ X (t + 1) (Lf η X (t + 1)) s' ∧ (s'.gpr .r6 != 0) = decide (t + 1 ≠ 544) := by
  rw [Lf_succ η hX ht]
  exact tries_ok hp hη ht h fun _ h' => step_ok hp ht h'

end VG.Proof.MlDsa.PPC64LE.Sample.RejBounded
