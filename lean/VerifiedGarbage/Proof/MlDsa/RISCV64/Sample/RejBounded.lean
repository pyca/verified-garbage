module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.Sample.Pro
public import VerifiedGarbage.Proof.MlDsa.Sample.RejBounded
public import VerifiedGarbage.Proof.MlDsa.Sample.HalfByte
public import VerifiedGarbage.Proof.MlDsa.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.Contracts
import VerifiedGarbage.Proof.MlKem.RISCV64.Sample
import VerifiedGarbage.Proof.MlKem.RISCV64.SampleCT
import VerifiedGarbage.Proof.MlKem.RISCV64.Common
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Common
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.SigEval
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Sample.Pro
meta import VerifiedGarbage.Proof.MlDsa.Sample.RejBounded
meta import VerifiedGarbage.Proof.MlDsa.Sample.HalfByte
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Sample
meta import VerifiedGarbage.Proof.MlKem.RISCV64.SampleCT
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Common
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.MRun
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.Contracts
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Common
meta import VerifiedGarbage.Proof.MlDsa.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Framework.RISCV64.Keep
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.SigEval
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# ML-DSA on RISC-V: `vg_mldsa_rej_bounded_poly`

As on PPC64LE (`Proof/MlDsa/PPC64LE/Sample/RejBoundedBody.lean`,
`RejBoundedCT.lean`, `RejBoundedRun.lean` and `RejBounded.lean`).

An iteration. Each half-byte is tried the same way: its coefficient computed
without a branch (`rbF`, the coefficient of `CoeffFromHalfByte` modulo `q`
on the accepted half-bytes, `rbF_eq`, by evaluation) and `t2` the test of
whether it is accepted and `j < 256` (`accH`), both from `half_ok`; then
`accept` stores the coefficient if so (`try_ok`), which is what `tryJ` does
to the coefficients. An iteration tries the low and then the high half-byte
of its byte, which is what `rbStep` does (`rbStep_tryJ`, `body_ok`). Between
the pieces, `Base` holds: the environment, the XOF output, the pointer `a0`
to the byte of iteration `t`, the count `a3`, `q` in `a4`, and the
coefficients `L` stored (`At`).

The function runs in pieces: the prologue (`J0`, with `eta` in `s7`), then
a try with `N = 272` (`rbTry_ok`): the sponge, whose output is `H(ρ, N)`
(`J6`), the branch on `η` (`Impl.MlDsa.RISCV64.Pack.sel`, which compares the
low 32 bits of `s7`: `sel_ok`), and the loop for `η` over the `N` bytes,
iteration `t` of which starts from `Base` with the coefficients `rbFold`
samples from the first `t` bytes of output stored (`loop_ok`). If those are
256, they are all of `H(ρ, 544)`'s (`Lf_full`); if not, a try with
`N = 544` runs from the prologue's state again (`Base` keeps `s7`–`s9`).
Then the end returns whether there are 256 (`correct`).

Two runs from entry states that agree on the public data (the pointers, the
low 32 bits of `η`, the stack pointer, and which half-bytes of the XOF
output are accepted, `rejBoundedLeak`) leak the same trace (`all_ct`): the
prologue and the blocks around the loop by the taint analysis, the sponge by
`sponge_ct`, the branch on `η` because the low 32 bits of `s7` are the same
in both runs, and the loop iteration by iteration (`loop_ct`): at iteration
`t` both runs have sampled as many coefficients, so the tests in `t2` agree
(`acc_eq`), and with them the branches of `accept` and the addresses of its
stores; the coefficients are computed by code that the taint analysis
proves leaks nothing of them but the address of the byte read (`load_ct`,
`hi_ct`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Sample.RejBounded

open VG VG.RISCV64
open VG.Proof.MlDsa.RISCV64.Sample
open VG.Impl.MlDsa.RISCV64.Sample
open VG.Impl.Sha3.RISCV64.Stream (mov)
open VG.Proof.MlDsa.Sample (hbTry rbStep rbFold Stored zw ifT ifF hbTry_length halfByteOk_le rbFold_snoc
  rbFold_length_le rbB rbC hbTry_eq halfByteOk_eq hbOks rbFold_length_congr stored_nil H_eq leak_hbOks)
open VG.Proof.MlKem.RISCV64 (ptr_add count_sub count_nz wp_loop_nz)
open VG.Proof.MlKem.RISCV64.Sample (toNat_setWidth8 taint_block relct_wp)
open VG.Proof.MlDsa.RISCV64.Pack (subwV lo_sub_beq selBlk_ok)
open VG.Spec.MlDsa (Zq q ofInt halfByteOk H rejBoundedLeak)
open VG.Proof.MlDsa (rejBoundedContract rejBoundedSig)
open VG.Spec.Sha3 (bytesAt)

variable {N : Nat}

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

theorem rbB_four : rbB 4 = 9 := rfl

theorem rbB_le {η : Nat} : rbB η ≤ 15 := by unfold rbB; split <;> omega

theorem csub_ten : csub 10 = [.addi .a6 .a6 (-(10 : Nat)), .shift .srl .d .t1 .a6 63, .shift .sll .d .a7 .t1 3,
    .add .a6 .a6 .a7, .shift .sll .d .a7 .t1 1, .add .a6 .a6 .a7] := rfl

theorem csub_five : csub 5 = [.addi .a6 .a6 (-(5 : Nat)), .shift .srl .d .t1 .a6 63, .shift .sll .d .a7 .t1 2,
    .add .a6 .a6 .a7, .add .a6 .a6 .t1] := rfl

/-- The block of a half-byte: `a7` its coefficient, `t2` the test. -/
theorem half_run {η : Nat} (hη : η = 2 ∨ η = 4) (s : State) (h4 : s.gpr .a4 = BitVec.ofNat 64 8380417) :
    WP isa (.block (rbHalf η)) s fun t =>
      t.gpr .a7 = rbF η (s.gpr .a6) ∧ t.gpr .t2 = accH (s.gpr .a6) (rbB η) (s.gpr .a2) ∧
      (∀ r, r ≠ .a6 → r ≠ .a7 → r ≠ .t1 → r ≠ .t2 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  rcases hη with rfl | rfl
  · mrun [rbHalf, testJ, rbVal, csub_ten, csub_five, addQNeg, rbBound, rbB_two, rbF, cs10, cs5, aq, accH,
      List.append_assoc, h4]
    intro r a b c d
    simp only [a, b, c, d, ite_false]
  · mrun [rbHalf, testJ, rbVal, addQNeg, rbBound, rbB_four, rbF, aq, accH, List.append_assoc, h4]
    intro r _ b c d
    simp only [b, c, d, ite_false]

/-! ## The invariant between the pieces -/

/-- The call, from its entry state: `seed = a0`, `eta = a1`, `a = a2`,
`scratch = a3`. -/
abbrev spOf (σ : State) : Sp := ⟨σ.gpr .a0, 66, σ.gpr .a3, σ.gpr .a2⟩

/-- `η`, the low 32 bits of `a1`. -/
abbrev etaOf (σ : State) : Nat := ((σ.gpr .a1).setWidth 32).toNat

/-- The XOF output the function uses: 544 bytes of `H(ρ)`. -/
abbrev X (σ : State) : List Byte := Spec.MlDsa.H ((spOf σ).msg σ) 544

theorem X_length (σ : State) : (X σ).length = 544 := Proof.MlDsa.Sample.H_length _ _

/-- The byte of iteration `t`. -/
abbrev zAt (X : List Byte) (t : Nat) : Byte := X.getD t 0

/-- Iteration `t`, with the coefficients `L` stored, for the `N` bytes `X` of XOF
output; `s7`–`s9` as the prologue left them. -/
structure Base (N : Nat) (σ : State) (X : List Byte) (t : Nat) (L : List Zq) (s : State) : Prop where
  env : Env (spOf σ) σ s
  out : bytesAt s.mem ((spOf σ).at' 840) N = X
  a0 : s.gpr .a0 = σ.gpr .a3 + BitVec.ofNat 64 (840 + t)
  a3 : s.gpr .a3 = BitVec.ofNat 64 (N - t)
  a4 : s.gpr .a4 = BitVec.ofNat 64 8380417
  at' : At (spOf σ) L s
  hN : N ≤ 544
  s7 : s.gpr .s7 = σ.gpr .a1
  s8 : s.gpr .s8 = BitVec.ofNat 64 66
  s9 : s.gpr .s9 = σ.gpr .a0

section
variable {σ : State} (hp : SpOk (spOf σ) σ)
include hp

/-- `Base` through a block that writes no memory and only `a5`–`a7`, `t1`, `t2`. -/
theorem Base.keep {X : List Byte} {t : Nat} {L : List Zq} {s s' : State} (h : Base N σ X t L s)
    (hm : s'.mem = s.mem)
    (g : ∀ r, r ≠ .a5 → r ≠ .a6 → r ≠ .a7 → r ≠ .t1 → r ≠ .t2 → s'.gpr r = s.gpr r) (rd : s'.rd = s.rd)
    (wr : s'.wr = s.wr) (sp : s'.sp = s.sp) : Base N σ X t L s' := by
  have gp : ∀ r ∈ preserved, s'.gpr r = s.gpr r := fun r hr =>
    g r (by rintro rfl; exact absurd hr (by decide)) (by rintro rfl; exact absurd hr (by decide))
      (by rintro rfl; exact absurd hr (by decide)) (by rintro rfl; exact absurd hr (by decide))
      (by rintro rfl; exact absurd hr (by decide))
  exact ⟨h.env.regs hp hm gp rd wr sp, by rw [hm]; exact h.out, (g _ (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans h.a0, (g _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.a3,
    (g _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.a4,
    ⟨(g _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.at'.a1,
      (g _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.at'.a2, h.at'.len,
      by rw [hm]; exact h.at'.st⟩, h.hN,
    (g _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.s7,
    (g _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.s8,
    (g _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.s9⟩

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

/-- After the block of the half-byte `b`: its coefficient in `a7`, the test
in `t2`, `a5` = `v`. -/
structure H1 (η N : Nat) (σ : State) (X : List Byte) (t : Nat) (L : List Zq) (b : Nat) (v : BitVec 64)
    (s : State) : Prop where
  base : Base N σ X t L s
  a5 : s.gpr .a5 = v
  a7 : s.gpr .a7 = rbF η (BitVec.ofNat 64 b)
  t2 : s.gpr .t2 = accH (BitVec.ofNat 64 b) (rbB η) (BitVec.ofNat 64 L.length)

section
variable {σ : State} (hp : SpOk (spOf σ) σ)
include hp

theorem half_ok {η : Nat} (hη : η = 2 ∨ η = 4) {X : List Byte} {t : Nat} {L : List Zq} {b : Nat} {s : State}
    (h : Base N σ X t L s) (h6 : s.gpr .a6 = BitVec.ofNat 64 b) :
    WP isa (.block (rbHalf η)) s (H1 η N σ X t L b (s.gpr .a5)) :=
  WP.mono (half_run hη s h.a4) fun s' ⟨g7, g2, g, m, rd, wr, sp⟩ =>
    ⟨h.keep hp m (fun r _ a b c d => g r a b c d) rd wr sp, g .a5 (by decide) (by decide) (by decide) (by decide),
      by rw [g7, h6], by rw [g2, h6, h.at'.a2]⟩

/-- `accept` after the block of a half-byte: what `tryJ` does. -/
theorem try_ok {η : Nat} (hη : η = 2 ∨ η = 4) {X : List Byte} {t : Nat} {L : List Zq} {b : Nat} (hb : b < 16)
    {v : BitVec 64} {s : State} (h : H1 η N σ X t L b v s) :
    WP isa (accept .a7) s fun s' => Base N σ X t (tryJ η L b) s' ∧ s'.gpr .a5 = v := by
  have l := h.base
  have hlen := l.at'.len
  have ea := accH_val hb (rbB_le (η := η)) hlen
  rw [← h.t2] at ea
  unfold tryJ
  rw [hbTry_eq hη]
  by_cases hz : s.gpr .t2 = 0
  · have hn : ¬ (b < rbB η ∧ L.length < 256) := fun hc => by rw [hz, ifT hc] at ea; exact absurd ea (by decide)
    have e : (if L.length < 256 then (if b < rbB η then L ++ [ofInt (rbC η b)] else L) else L) = L := by
      by_cases hl : L.length < 256
      · rw [ifT hl, ifF (fun hc => hn ⟨hc, hl⟩)]
      · rw [ifF hl]
    rw [e]
    exact WP.mono (accept_skip hz) fun s' e' => by subst e'; exact ⟨l, h.a5⟩
  · have hy : b < rbB η ∧ L.length < 256 := by
      by_contra hc; rw [ifF hc] at ea; exact hz ea
    rw [ifT hy.2, ifT hy.1]
    refine WP.mono (accept_store hp l.env l.at' hy.2 (x := ofInt (rbC η b)) (by rw [h.a7]; exact rbF_eq hη hy.1) hz)
      fun s' ⟨at', env', rr, hf⟩ => ⟨⟨env', ?_, (rr _ (by decide) (by decide)).trans l.a0,
        (rr _ (by decide) (by decide)).trans l.a3, (rr _ (by decide) (by decide)).trans l.a4, at', l.hN,
        (rr _ (by decide) (by decide)).trans l.s7, (rr _ (by decide) (by decide)).trans l.s8,
        (rr _ (by decide) (by decide)).trans l.s9⟩,
        (rr _ (by decide) (by decide)).trans h.a5⟩
    have := l.hN
    rw [MlKem.bytesAt_frame hf (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact (hp.a_scr.sub_right (sub_scr (a := 840) (n := N) (by omega))).symm) (by omega)]
    exact l.out

/-! ## An iteration -/

/-- The byte of iteration `t`. -/
theorem byte_ok {X : List Byte} {t : Nat} (ht : t < N) {L : List Zq} {s : State} (h : Base N σ X t L s) :
    InRegions (s.rd ++ s.wr) (s.gpr .a0) 1 ∧ s.mem (s.gpr .a0) = zAt X t := by
  have := h.hN
  rw [h.a0]
  refine ⟨by rw [← BitVec.add_zero (σ.gpr .a3 + _), ptr_add]; exact inScrRd hp h.env.wr (by omega), ?_⟩
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
theorem lo_ok {X : List Byte} {t : Nat} (ht : t < N) {L : List Zq} {s : State} (h : Base N σ X t L s) :
    WP isa (.block [.load .b .a5 .a0 0, .shift .sll .d .a6 .a5 60, .shift .srl .d .a6 .a6 60]) s fun s' =>
      Base N σ X t L s' ∧ s'.gpr .a5 = (zAt X t).setWidth 64 ∧
        s'.gpr .a6 = BitVec.ofNat 64 ((zAt X t).toNat % 16) := by
  obtain ⟨i0, v0⟩ := byte_ok hp ht h
  have hk : WP isa (.block [.load .b .a5 .a0 0, .shift .sll .d .a6 .a5 60, .shift .srl .d .a6 .a6 60]) s
      fun s' => s'.gpr .a5 = (zAt X t).setWidth 64 ∧ s'.gpr .a6 = (zAt X t).setWidth 64 <<< 60 >>> 60 ∧
      (∀ r, r ≠ .a5 → r ≠ .a6 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
    mrun [i0, v0]
    intro r a b
    simp only [a, b, ite_false]
  refine WP.mono hk fun s' ⟨g5, g6, g, m, rd, wr, sp⟩ =>
    ⟨h.keep hp m (fun r a b _ _ _ => g r a b) rd wr sp, g5, by rw [g6, lo_eq]⟩

/-- The load of the byte and the block of its low half-byte. -/
theorem loHalf_ok {η : Nat} (hη : η = 2 ∨ η = 4) {X : List Byte} {t : Nat} (ht : t < N) {L : List Zq}
    {s : State} (h : Base N σ X t L s) :
    WP isa (.block (([.load .b .a5 .a0 0, .shift .sll .d .a6 .a5 60, .shift .srl .d .a6 .a6 60] : List Instr) ++
      rbHalf η)) s (H1 η N σ X t L ((zAt X t).toNat % 16) ((zAt X t).setWidth 64)) := by
  rw [WP.block_append_iff]
  exact WP.mono (lo_ok hp ht h) fun s1 ⟨b1, e5, e6⟩ => e5 ▸ half_ok hp hη b1 e6

/-- The block of the high half-byte, from the byte in `a5`. -/
theorem hiHalf_ok {η : Nat} (hη : η = 2 ∨ η = 4) {X : List Byte} {t : Nat} {L : List Zq} {s : State}
    (h : Base N σ X t L s) (h5 : s.gpr .a5 = (zAt X t).setWidth 64) :
    WP isa (.block (.shift .srl .d .a6 .a5 4 :: rbHalf η)) s
      (H1 η N σ X t L ((zAt X t).toNat / 16) ((zAt X t).setWidth 64)) := by
  rw [← List.singleton_append, WP.block_append_iff]
  have hk : WP isa (.block [.shift .srl .d .a6 .a5 4]) s fun s4 => s4 = s.write .a6 (s.gpr .a5 >>> 4) := by
    mrun []
  refine WP.mono hk fun s4 e4 => ?_
  subst e4
  have b4 : Base N σ X t L (s.write .a6 (s.gpr .a5 >>> 4)) :=
    h.keep hp rfl (fun r _ a _ _ _ => RegUpd.gpr_write_of_ne _ _ a) rfl rfl rfl
  have h6 : (s.write .a6 (s.gpr .a5 >>> 4)).gpr .a6 = BitVec.ofNat 64 ((zAt X t).toNat / 16) := by
    rw [RegUpd.gpr_write_self, h5, hi_eq]
  have e : (s.write .a6 (s.gpr .a5 >>> 4)).gpr .a5 = (zAt X t).setWidth 64 := by
    rw [RegUpd.gpr_write_of_ne _ _ (by decide), h5]
  exact e ▸ half_ok hp hη b4 h6

/-- The tries of an iteration, from its start, then `rest`. -/
theorem tries_ok {η : Nat} (hη : η = 2 ∨ η = 4) {X : List Byte} {t : Nat} (ht : t < N) {L : List Zq}
    {s : State} (h : Base N σ X t L s) {rest : Prog isa} {Q : State → Prop}
    (hr : ∀ s', Base N σ X t (rbStep η L (zAt X t)) s' → WP isa rest s' Q) :
    WP isa (.seq (.block (([.load .b .a5 .a0 0, .shift .sll .d .a6 .a5 60, .shift .srl .d .a6 .a6 60] :
      List Instr) ++ rbHalf η))
      (.seq (accept .a7) (.seq (.block (.shift .srl .d .a6 .a5 4 :: rbHalf η)) (.seq (accept .a7) rest)))) s Q := by
  rw [rbStep_tryJ] at hr
  refine WP.seq (WP.mono (loHalf_ok hp hη ht h) fun s2 h2 => ?_)
  refine WP.seq (WP.mono (try_ok hp hη (Nat.mod_lt _ (by decide)) h2) fun s3 ⟨b3, f5⟩ => ?_)
  refine WP.seq (WP.mono (hiHalf_ok hp hη b3 f5) fun s5 h5 => ?_)
  exact WP.seq (WP.mono (try_ok hp hη (by have := (zAt X t).isLt; omega) h5) fun s6 h6 => hr s6 h6.1)

/-- The step, to iteration `t + 1`: `a3` zero iff it is the last. -/
theorem step_ok {X : List Byte} {t : Nat} (ht : t < N) {L : List Zq} {s : State} (h : Base N σ X t L s) :
    WP isa (.block [.addi .a0 .a0 1, .addi .a3 .a3 (-1)]) s fun s' =>
      Base N σ X (t + 1) L s' ∧ (s'.gpr .a3 != 0) = decide (t + 1 ≠ N) := by
  have hk : WP isa (.block [.addi .a0 .a0 1, .addi .a3 .a3 (-1)]) s fun s' =>
      s'.gpr .a0 = s.gpr .a0 + BitVec.ofNat 64 1 ∧ s'.gpr .a3 = s.gpr .a3 - BitVec.ofNat 64 1 ∧
      (∀ r, r ≠ .a0 → r ≠ .a3 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
    mrun []
    intro r a b
    simp only [a, b, ite_false]
  refine WP.mono hk fun s' ⟨r3, r6, g, m, rd, wr, sp⟩ => ⟨⟨?_, by rw [m]; exact h.out, ?_, ?_,
    (g _ (by decide) (by decide)).trans h.a4, ⟨(g _ (by decide) (by decide)).trans h.at'.a1,
      (g _ (by decide) (by decide)).trans h.at'.a2, h.at'.len, by rw [m]; exact h.at'.st⟩, h.hN,
      (g _ (by decide) (by decide)).trans h.s7, (g _ (by decide) (by decide)).trans h.s8,
      (g _ (by decide) (by decide)).trans h.s9⟩, ?_⟩
  · exact h.env.regs hp m (fun r hr => g r (by rintro rfl; exact absurd hr (by decide))
      (by rintro rfl; exact absurd hr (by decide))) rd wr sp
  · rw [r3, h.a0, ptr_add, Nat.add_assoc]
  · rw [r6, h.a3]; exact count_sub ht
  · rw [r6, h.a3, count_sub ht]; exact count_nz ht (by have := h.hN; omega)

end

/-- The coefficients after `t` iterations. -/
abbrev Lf (η : Nat) (X : List Byte) (t : Nat) : List Zq := rbFold η [] (X.take t)

theorem take_succ' (L : List Byte) {i : Nat} (h : i < L.length) : L.take (i + 1) = L.take i ++ [L.getD i 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem Lf_succ (η : Nat) {X : List Byte} (hX : X.length = N) {t : Nat} (ht : t < N) :
    Lf η X (t + 1) = rbStep η (Lf η X t) (zAt X t) := by
  simp only [Lf]
  rw [take_succ' _ (by omega), rbFold_snoc]

/-- An iteration: what `rbStep` does to the coefficients. -/
theorem body_ok {σ : State} (hp : SpOk (spOf σ) σ) {η : Nat} (hη : η = 2 ∨ η = 4) {X : List Byte}
    (hX : X.length = N) {t : Nat} (ht : t < N) {s : State} (h : Base N σ X t (Lf η X t) s) :
    WP isa (rbBody η) s fun s' => Base N σ X (t + 1) (Lf η X (t + 1)) s' ∧ (s'.gpr .a3 != 0) = decide (t + 1 ≠ N) := by
  rw [Lf_succ η hX ht]
  exact tries_ok hp hη ht h fun _ h' => step_ok hp ht h'

/-! ## Constant time: the blocks, for any `η` -/

/-- The load of the byte and the block of its low half-byte. -/
theorem load_ct {η : Nat} (hη : η = 2 ∨ η = 4) {R : State → State → Prop} (hsp : ∀ a b, R a b → a.sp = b.sp)
    (h0 : ∀ a b, R a b → a.gpr .a0 = b.gpr .a0) :
    RelCT isa R (.block (([.load .b .a5 .a0 0, .shift .sll .d .a6 .a5 60, .shift .srl .d .a6 .a6 60] :
      List Instr) ++ rbHalf η)) fun _ _ => True := by
  rcases hη with rfl | rfl <;>
  exact taint_block [.a0] hsp (fun a b hab r hr => by rw [List.mem_singleton] at hr; subst hr; exact h0 a b hab)
    (by taint_decide)

/-- The block of the high half-byte. -/
theorem hi_ct {η : Nat} (hη : η = 2 ∨ η = 4) {R : State → State → Prop} :
    RelCT isa R (.block (.shift .srl .d .a6 .a5 4 :: rbHalf η)) fun _ _ => True := by
  rcases hη with rfl | rfl <;> exact Pack.relct_noMem rfl

/-- The tests of two half-bytes accepted alike, with as many coefficients. -/
theorem acc_eq {η : Nat} (hη : η = 2 ∨ η = 4) {b₁ b₂ j : Nat} (hb₁ : b₁ < 16) (hb₂ : b₂ < 16) (hj : j ≤ 256)
    (hok : halfByteOk η b₁ = halfByteOk η b₂) :
    accH (BitVec.ofNat 64 b₁) (rbB η) (BitVec.ofNat 64 j) = accH (BitVec.ofNat 64 b₂) (rbB η) (BitVec.ofNat 64 j) := by
  rw [accH_val hb₁ rbB_le hj, accH_val hb₂ rbB_le hj]
  rw [halfByteOk_eq hη, halfByteOk_eq hη] at hok
  by_cases h₁ : b₁ < rbB η <;> by_cases h₂ : b₂ < rbB η <;> simp only [h₁, h₂, ite_true, ite_false] at hok ⊢ <;>
    first | rfl | exact absurd hok (by decide)

/-! ## Constant time: the loop -/

section
variable {σ₁ σ₂ : State} (hp₁ : SpOk (spOf σ₁) σ₁) (hp₂ : SpOk (spOf σ₂) σ₂) (hsp : σ₁.sp = σ₂.sp)
  (h2 : σ₁.gpr .a2 = σ₂.gpr .a2) (h3 : σ₁.gpr .a3 = σ₂.gpr .a3) {η : Nat} (hη : η = 2 ∨ η = 4)
  {X₁ X₂ : List Byte}

theorem base_sp {t₁ t₂ : Nat} {L₁ L₂ : List Zq} {a b : State} (ha : Base N σ₁ X₁ t₁ L₁ a) (hb : Base N σ₂ X₂ t₂ L₂ b)
    (hsp : σ₁.sp = σ₂.sp) : a.sp = b.sp := by
  rw [ha.env.sp, hb.env.sp, hsp]

theorem base_a1 {t₁ t₂ : Nat} {L₁ L₂ : List Zq} {a b : State} (ha : Base N σ₁ X₁ t₁ L₁ a) (hb : Base N σ₂ X₂ t₂ L₂ b)
    (h2 : σ₁.gpr .a2 = σ₂.gpr .a2) (hl : L₁.length = L₂.length) : a.gpr .a1 = b.gpr .a1 := by
  rw [ha.at'.a1, hb.at'.a1, hl]; exact congrArg (· + _) h2

include hp₁ hp₂ hsp h2 hη in
/-- A try, in two runs with as many coefficients and half-bytes accepted
alike. -/
theorem try_ct {t : Nat} {L₁ L₂ : List Zq} (hl : L₁.length = L₂.length) {b₁ b₂ : Nat} (hb₁ : b₁ < 16)
    (hb₂ : b₂ < 16) (hok : halfByteOk η b₁ = halfByteOk η b₂) {v₁ v₂ : BitVec 64} :
    RelCT isa (fun a b => H1 η N σ₁ X₁ t L₁ b₁ v₁ a ∧ H1 η N σ₂ X₂ t L₂ b₂ v₂ b) (accept .a7)
      fun a b => (Base N σ₁ X₁ t (tryJ η L₁ b₁) a ∧ a.gpr .a5 = v₁) ∧
        (Base N σ₂ X₂ t (tryJ η L₂ b₂) b ∧ b.gpr .a5 = v₂) :=
  relct_wp (accept_ct (fun a b hab => base_sp hab.1.base hab.2.base hsp)
    (fun a b hab => by rw [hab.1.t2, hab.2.t2, hl, acc_eq hη hb₁ hb₂ (hl ▸ hab.2.base.at'.len) hok])
    fun a b hab => base_a1 hab.1.base hab.2.base h2 hl)
    fun a b hab => ⟨try_ok hp₁ hη hb₁ hab.1, try_ok hp₂ hη hb₂ hab.2⟩

variable (hX₁ : X₁.length = N) (hX₂ : X₂.length = N) (oks : X₁.map (hbOks η) = X₂.map (hbOks η))

include oks in
theorem len_eq (t : Nat) : (Lf η X₁ t).length = (Lf η X₂ t).length :=
  rbFold_length_congr rfl (by rw [List.map_take, List.map_take, oks])

include hX₁ hX₂ oks in
theorem ok_eq {t : Nat} (ht : t < N) : hbOks η (zAt X₁ t) = hbOks η (zAt X₂ t) := by
  have h := congrArg (fun L => L[t]?) oks
  simp only [List.getElem?_map, List.getElem?_eq_getElem (show t < X₁.length by omega_arith),
    List.getElem?_eq_getElem (show t < X₂.length by omega_arith), Option.map_some, Option.some.injEq] at h
  rw [zAt, zAt, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show t < X₁.length by omega_arith), List.getElem?_eq_getElem (show t < X₂.length by omega_arith)]
  exact h

theorem tryJ_length_congr {L₁ L₂ : List Zq} (hl : L₁.length = L₂.length) {b₁ b₂ : Nat}
    (hok : halfByteOk η b₁ = halfByteOk η b₂) : (tryJ η L₁ b₁).length = (tryJ η L₂ b₂).length := by
  rw [tryJ_length, tryJ_length, hl, hok]

include hp₁ hp₂ hsp h2 h3 hη hX₁ hX₂ oks in
/-- An iteration, in two runs. -/
theorem body_ct {t : Nat} (ht : t < N) :
    RelCT isa (fun a b => Base N σ₁ X₁ t (Lf η X₁ t) a ∧ Base N σ₂ X₂ t (Lf η X₂ t) b) (rbBody η)
      fun a b => (Base N σ₁ X₁ (t + 1) (Lf η X₁ (t + 1)) a ∧ (a.gpr .a3 != 0) = decide (t + 1 ≠ N)) ∧
        (Base N σ₂ X₂ (t + 1) (Lf η X₂ (t + 1)) b ∧ (b.gpr .a3 != 0) = decide (t + 1 ≠ N)) := by
  refine relct_wp ?_ fun a b hab => ⟨body_ok hp₁ hη hX₁ ht hab.1, body_ok hp₂ hη hX₂ ht hab.2⟩
  have hl := len_eq oks t
  have hok := ok_eq hX₁ hX₂ oks ht
  simp only [hbOks, Prod.mk.injEq] at hok
  have hlo₁ : (zAt X₁ t).toNat % 16 < 16 := Nat.mod_lt _ (by decide)
  have hlo₂ : (zAt X₂ t).toNat % 16 < 16 := Nat.mod_lt _ (by decide)
  have hhi₁ : (zAt X₁ t).toNat / 16 < 16 := by have := (zAt X₁ t).isLt; omega_arith
  have hhi₂ : (zAt X₂ t).toNat / 16 < 16 := by have := (zAt X₂ t).isLt; omega_arith
  -- the byte and its low half-byte
  refine RelCT.seq (R := fun a b =>
      H1 η N σ₁ X₁ t (Lf η X₁ t) ((zAt X₁ t).toNat % 16) ((zAt X₁ t).setWidth 64) a ∧
      H1 η N σ₂ X₂ t (Lf η X₂ t) ((zAt X₂ t).toNat % 16) ((zAt X₂ t).setWidth 64) b)
    (relct_wp (load_ct hη (fun a b hab => base_sp hab.1 hab.2 hsp) fun a b hab => by
      rw [hab.1.a0, hab.2.a0, h3]) fun a b hab => ⟨loHalf_ok hp₁ hη ht hab.1, loHalf_ok hp₂ hη ht hab.2⟩) ?_
  -- its try
  refine RelCT.seq (try_ct hp₁ hp₂ hsp h2 hη hl hlo₁ hlo₂ hok.1) ?_
  -- the high half-byte
  have hl' := tryJ_length_congr (η := η) hl hok.1
  refine RelCT.seq (R := fun a b =>
      H1 η N σ₁ X₁ t (tryJ η (Lf η X₁ t) ((zAt X₁ t).toNat % 16)) ((zAt X₁ t).toNat / 16) ((zAt X₁ t).setWidth 64) a ∧
      H1 η N σ₂ X₂ t (tryJ η (Lf η X₂ t) ((zAt X₂ t).toNat % 16)) ((zAt X₂ t).toNat / 16) ((zAt X₂ t).setWidth 64) b)
    (relct_wp (hi_ct hη) fun a b hab => ⟨hiHalf_ok hp₁ hη hab.1.1 hab.1.2, hiHalf_ok hp₂ hη hab.2.1 hab.2.2⟩) ?_
  -- its try, and the step
  exact RelCT.seq (try_ct hp₁ hp₂ hsp h2 hη hl' hhi₁ hhi₂ hok.2) (Pack.relct_noMem rfl)

include hp₁ hp₂ hsp h2 h3 hη hX₁ hX₂ oks in
/-- The loop. -/
theorem loop_ct (h0 : 0 < N) :
    RelCT isa (fun a b => Base N σ₁ X₁ 0 (Lf η X₁ 0) a ∧ Base N σ₂ X₂ 0 (Lf η X₂ 0) b) (.loop (rbBody η) (.nonzero .a3))
      fun a b => Base N σ₁ X₁ N (Lf η X₁ N) a ∧ Base N σ₂ X₂ N (Lf η X₂ N) b := by
  refine RelCT.mono (RelCT.loop (M := isa) (body := rbBody η) (c := .nonzero .a3)
    (Q := fun a b => Base N σ₁ X₁ N (Lf η X₁ N) a ∧ Base N σ₂ X₂ N (Lf η X₂ N) b)
    (fun n a b => ∃ t, t < N ∧ n = N - t ∧ Base N σ₁ X₁ t (Lf η X₁ t) a ∧ Base N σ₂ X₂ t (Lf η X₂ t) b)
    (fun n => ?_) N) (fun a b hab => ⟨0, h0, rfl, hab⟩) (fun _ _ h => h)
  refine RelCT.mono (P := fun a b => ∃ t, t < N ∧ n = N - t ∧ Base N σ₁ X₁ t (Lf η X₁ t) a ∧
      Base N σ₂ X₂ t (Lf η X₂ t) b) (RelCT.exists_ fun t => ?_) (fun _ _ hab => hab) (fun _ _ h => h)
  by_cases ht : t < N
  · by_cases hn : n = N - t
    · refine RelCT.mono (P := fun a b => Base N σ₁ X₁ t (Lf η X₁ t) a ∧ Base N σ₂ X₂ t (Lf η X₂ t) b)
        (body_ct hp₁ hp₂ hsp h2 h3 hη hX₁ hX₂ oks ht) (fun _ _ hab => hab.2.2)
        fun a b ⟨⟨i₁, z₁⟩, ⟨i₂, z₂⟩⟩ => ⟨?_, fun e => ?_, fun e => ?_⟩
      · rw [Steps.eval_nonzero, Steps.eval_nonzero, z₁, z₂]
      · have : t + 1 = N := by
          have e' : (a.gpr .a3 != 0) = false := by rw [Steps.eval_nonzero] at e; exact Option.some.inj e
          rw [z₁] at e'; simpa using e'
        rw [this] at i₁ i₂; exact ⟨i₁, i₂⟩
      · have : t + 1 ≠ N := by
          have e' : (a.gpr .a3 != 0) = true := by rw [Steps.eval_nonzero] at e; exact Option.some.inj e
          rw [z₁] at e'; simpa using e'
        exact ⟨N - (t + 1), by omega_arith, t + 1, by omega_arith, rfl, i₁, i₂⟩
    · exact RelCT.of_false fun _ _ hab => hn hab.2.1
  · exact RelCT.of_false fun _ _ hab => ht hab.1

end

/-! ## Correctness -/

theorem loadQ_eq : loadQ = Impl.MlDsa.RISCV64.Pack.loadB .a4 8380417 := rfl

theorem loadBVal_q : Proof.MlDsa.RISCV64.Pack.loadBVal 8380417 = BitVec.ofNat 64 8380417 := by decide

theorem loadBVal_two : Proof.MlDsa.RISCV64.Pack.loadBVal 2 = BitVec.ofNat 64 2 := by decide

section
variable {σ : State} (hp : SpOk (spOf σ) σ)
include hp

/-- The XOF output of a try: `N` bytes of `H(ρ)`. -/
abbrev XN (N : Nat) (σ : State) : List Byte := Spec.MlDsa.H ((spOf σ).msg σ) N

omit hp in
theorem XN_length (N : Nat) (σ : State) : (XN N σ).length = N := Proof.MlDsa.Sample.H_length _ _

/-- The loop's setup, after the sponge. -/
theorem init_ok (hN : N = 272 ∨ N = 544) {s₀ s : State} (h : J6 136 N (spOf σ) σ s₀ s)
    (h7 : s.gpr .s7 = σ.gpr .a1) :
    WP isa (.block (([.addi .a0 .s11 840, mov .a1 .s10, .li .a2 0, .li .a3 N] : List Instr) ++ loadQ)) s
      (Base N σ (XN N σ) 0 []) := by
  have g10 := h.j0.env.s10
  have g11 := h.j0.env.s11
  have hk : WP isa (.block [.addi .a0 .s11 840, mov .a1 .s10, .li .a2 0, .li .a3 N]) s
      fun s' => s'.gpr .a0 = σ.gpr .a3 + BitVec.ofNat 64 (840 + 0) ∧ s'.gpr .a1 = σ.gpr .a2 ∧
        s'.gpr .a2 = BitVec.ofNat 64 0 ∧ s'.gpr .a3 = BitVec.ofNat 64 (N - 0) ∧
        (∀ r, r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → r ≠ .a3 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
    rcases hN with rfl | rfl <;>
    · mrun [mov, g10, g11]
      intro r a b c d
      simp only [a, b, c, d, ite_false]
  rw [WP.block_append_iff]
  refine WP.mono hk fun s1 ⟨g0, g1, g2, g3, g, m, rd, wr, sp⟩ => ?_
  rw [loadQ_eq]
  refine WP.mono (Proof.MlDsa.RISCV64.Pack.WP.withSp (Pack.loadB_ok .a4 loadBVal_q s1)) fun s' ⟨⟨⟨g4, m'⟩, k⟩, sp'⟩ => ?_
  have e : ∀ r, r ≠ .a4 → s'.gpr r = s1.gpr r := fun r hr => k.gpr (by simpa using hr)
  have gp : ∀ r ∈ preserved, s'.gpr r = s.gpr r := fun r hr => by
    have n : ∀ x : Reg, x ∉ preserved → r ≠ x := fun x hx e => hx (e ▸ hr)
    rw [e r (n _ (by decide)), g r (n _ (by decide)) (n _ (by decide)) (n _ (by decide)) (n _ (by decide))]
  refine ⟨h.j0.env.regs hp (m'.trans m) gp (k.2.1.trans rd) (k.2.2.trans wr) (sp'.trans sp),
    by rw [m', m, h.out]; exact (H_eq _ _).symm, by rw [e _ (by decide)]; exact g0,
    by rw [e _ (by decide)]; exact g3, g4, ?_, by omega, (gp _ (by decide)).trans h7,
    (gp _ (by decide)).trans h.j0.s8, (gp _ (by decide)).trans h.j0.s9⟩
  exact ⟨by rw [e _ (by decide), g1]; exact (BitVec.add_zero _).symm, by rw [e _ (by decide)]; exact g2,
    by simp, stored_nil _ _⟩

/-- The loop for `η`. -/
theorem loop_ok (hN : N = 272 ∨ N = 544) {η : Nat} (hη : η = 2 ∨ η = 4) {s₀ s : State}
    (h : J6 136 N (spOf σ) σ s₀ s) (h7 : s.gpr .s7 = σ.gpr .a1) :
    WP isa (rbLoop N η) s (Base N σ (XN N σ) N (Lf η (XN N σ) N)) :=
  WP.seq (WP.mono (init_ok hp hN h h7) fun _ h0 =>
    wp_loop_nz (fun t s => Base N σ (XN N σ) t (Lf η (XN N σ) t) s) (N := N) (by omega)
      (fun _ ht _ hs => body_ok hp hη (XN_length N σ) ht hs) (fun _ h => h) h0)

/-- The block of the branch on `η`, which keeps `J6` and `s7`. -/
theorem cmp_ok {s₀ s : State} (h : J6 136 N (spOf σ) σ s₀ s) (h7 : s.gpr .s7 = σ.gpr .a1) :
    WP isa (.block (Impl.MlDsa.RISCV64.Pack.loadB .a6 2 ++ ([.subw .a6 .s7 .a6] : List Instr))) s fun s' =>
      J6 136 N (spOf σ) σ s₀ s' ∧ s'.gpr .a6 = subwV (σ.gpr .a1) 2 ∧ s'.gpr .s7 = σ.gpr .a1 := by
  refine WP.mono (Proof.MlDsa.RISCV64.Pack.WP.withSp (selBlk_ok .s7 (by decide) loadBVal_two s)) fun s' ⟨⟨g6, k, m⟩, sp⟩ => ?_
  have gp : ∀ r ∈ preserved, s'.gpr r = s.gpr r := fun r hr =>
    k.gpr (by rintro hm; simp only [List.mem_singleton] at hm; subst hm; exact absurd hr (by decide))
  exact ⟨⟨h.j0.regs hp m gp k.2.1 k.2.2 sp, fun r hr => (gp r hr).trans (h.gp r hr), by rw [m]; exact h.out⟩,
    by rw [g6, h7], (gp _ (by decide)).trans h7⟩

/-- The branch on `η`, and the loop for it. -/
theorem sel_ok (hN : N = 272 ∨ N = 544) (hη : etaOf σ = 2 ∨ etaOf σ = 4) {s₀ s : State}
    (h : J6 136 N (spOf σ) σ s₀ s) (h7 : s.gpr .s7 = σ.gpr .a1) :
    WP isa (Impl.MlDsa.RISCV64.Pack.sel .s7 2 (rbLoop N 2) (rbLoop N 4)) s
      (Base N σ (XN N σ) N (Lf (etaOf σ) (XN N σ) N)) := by
  refine WP.seq (WP.mono (cmp_ok hp h h7) fun s1 ⟨j6, e6, e7⟩ => ?_)
  refine WP.ite _ (by rw [Steps.eval_zero, e6, lo_sub_beq _ (by decide)]) (fun he => ?_) (fun he => ?_)
  · simp only [decide_eq_true_eq] at he
    rw [show etaOf σ = 2 from he]
    exact loop_ok hp hN (.inl rfl) j6 e7
  · simp only [decide_eq_false_iff_not] at he
    rw [show etaOf σ = 4 from hη.resolve_left he]
    exact loop_ok hp hN (.inr rfl) j6 e7

/-- A try, from the prologue's state. -/
theorem rbTry_ok (hN : N = 272 ∨ N = 544) (hη : etaOf σ = 2 ∨ etaOf σ = 4) {s : State}
    (h : J0 (spOf σ) σ s) (h7 : s.gpr .s7 = σ.gpr .a1) :
    WP isa (rbTry N) s (Base N σ (XN N σ) N (Lf (etaOf σ) (XN N σ) N)) :=
  WP.seq (WP.mono (sponge_ok hp (rate := 136) (outlen := N) (by decide) (by omega) h) fun _ h6 =>
    sel_ok hp hN hη h6 ((h6.gp .s7 (by decide)).trans h7))

/-- The test of the first try's result: `t0 = j >> 8`. -/
theorem test_ok {X : List Byte} {L : List Zq} {s : State} (h : Base N σ X N L s) :
    WP isa (.block [.shift .srl .d .t0 .a2 8]) s fun s' => Base N σ X N L s' ∧
      (s'.gpr .t0 == 0) = decide (L.length ≠ 256) := by
  have hk : WP isa (.block [.shift .srl .d .t0 .a2 8]) s fun s' => s'.gpr .t0 = s.gpr .a2 >>> 8 ∧
      (∀ r, r ≠ .t0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
    mrun []
    intro r a
    simp only [a, ite_false]
  refine WP.mono hk fun s' ⟨r0, g, m, rd, wr, sp⟩ => ⟨⟨h.env.regs hp m (fun r hr => g r
    (by rintro rfl; exact absurd hr (by decide))) rd wr sp, by rw [m]; exact h.out,
    (g _ (by decide)).trans h.a0, (g _ (by decide)).trans h.a3, (g _ (by decide)).trans h.a4,
    ⟨(g _ (by decide)).trans h.at'.a1, (g _ (by decide)).trans h.at'.a2, h.at'.len,
      by rw [m]; exact h.at'.st⟩, h.hN, (g _ (by decide)).trans h.s7, (g _ (by decide)).trans h.s8,
    (g _ (by decide)).trans h.s9⟩, ?_⟩
  rw [r0, h.at'.a2, VG.Proof.MlKem.RISCV64.Sample.ret_val h.at'.len]
  by_cases e : L.length = 256 <;> simp [e]

omit hp in
/-- 256 coefficients from the first 272 bytes are all those of the 544. -/
theorem Lf_full {η : Nat} (hl : (Lf η (XN 272 σ) 272).length = 256) :
    Lf η (X σ) 544 = Lf η (XN 272 σ) 272 := by
  have e1 : (XN 272 σ).take 272 = XN 272 σ := List.take_of_length_le (by rw [XN_length])
  have e2 : (X σ).take 544 = X σ := List.take_of_length_le (by rw [X_length])
  simp only [Lf, e1, e2] at hl ⊢
  rw [← List.take_append_drop 272 (X σ), VG.Proof.MlDsa.Sample.rbFold_append, X,
    VG.Proof.MlDsa.Sample.H_take _ (by decide : 272 ≤ 544)]
  exact VG.Proof.MlDsa.Sample.rbFold_full (show (rbFold η [] (XN 272 σ)).length = Spec.MlDsa.n from hl) _

/-- The whole function: `a0` whether the loop sampled 256 coefficients, those
stored, and the calling convention. -/
theorem correct (hη : etaOf σ = 2 ∨ etaOf σ = 4) :
    WP isa rejBounded σ fun s' =>
      s'.gpr .a0 = (if (Lf (etaOf σ) (X σ) 544).length = 256 then 1 else 0) ∧
      Stored s'.mem (σ.gpr .a2) (Lf (etaOf σ) (X σ) 544) ∧ abiPreserved σ s' := by
  unfold rejBounded
  refine WP.seq (WP.mono (pro_rb hp rfl rfl rfl rfl) fun s₀ ⟨j0, e7⟩ => WP.seq ?_)
  refine WP.mono (rbTry_ok hp (.inl rfl) hη j0 e7) fun s₂ h₂ => WP.seq ?_
  refine WP.mono (test_ok hp h₂) fun s₃ ⟨h₃, z⟩ => WP.seq ?_
  refine WP.ite _ (Steps.eval_zero _ _) (fun e => ?_) (fun e => ?_)
  · refine WP.mono (rbTry_ok hp (.inr rfl) hη ⟨h₃.env, h₃.s9, h₃.s8⟩ h₃.s7) fun s₄ h₄ => ?_
    exact WP.mono (retEpi_ok hp h₄.env h₄.at'.a2 h₄.at'.len) fun s' ⟨r0, hm, ha⟩ =>
      ⟨r0, by rw [hm]; exact h₄.at'.st, ha⟩
  · have hl : (Lf (etaOf σ) (XN 272 σ) 272).length = 256 := by rw [z] at e; simpa using e
    refine WP.block_nil ?_
    rw [Lf_full hl]
    exact WP.mono (retEpi_ok hp h₃.env h₃.at'.a2 h₃.at'.len) fun s' ⟨r0, hm, ha⟩ =>
      ⟨r0, by rw [hm]; exact h₃.at'.st, ha⟩

end

/-! ## Constant time -/

theorem Lf_zero (η : Nat) (X : List Byte) : Lf η X 0 = [] := by simp [Lf, rbFold]

/-- Two runs, from entry states that agree on the public data. -/
structure Two (σ₁ σ₂ : State) : Prop where
  hp₁ : SpOk (spOf σ₁) σ₁
  hp₂ : SpOk (spOf σ₂) σ₂
  hη : etaOf σ₁ = 2 ∨ etaOf σ₁ = 4
  sp : σ₁.sp = σ₂.sp
  a0 : σ₁.gpr .a0 = σ₂.gpr .a0
  a1 : (σ₁.gpr .a1).setWidth 32 = (σ₂.gpr .a1).setWidth 32
  a2 : σ₁.gpr .a2 = σ₂.gpr .a2
  a3 : σ₁.gpr .a3 = σ₂.gpr .a3
  leak : rejBoundedLeak (etaOf σ₁) ((spOf σ₁).msg σ₁) = rejBoundedLeak (etaOf σ₂) ((spOf σ₂).msg σ₂)

section
variable {σ₁ σ₂ : State} (h : Two σ₁ σ₂)
include h

theorem sp_eq : spOf σ₂ = spOf σ₁ := by simp only [spOf, h.a0, h.a2, h.a3]

theorem eta_eq : etaOf σ₂ = etaOf σ₁ := by simp only [etaOf, h.a1]

theorem oks (hN : N = 272 ∨ N = 544) :
    (XN N σ₁).map (hbOks (etaOf σ₁)) = (XN N σ₂).map (hbOks (etaOf σ₁)) := by
  have hl := h.leak
  rw [eta_eq h] at hl
  exact leak_hbOks hl (B := N) (by rcases hN with rfl | rfl <;> decide)

/-- The loop for `η`, from the sponge's output. -/
theorem rbLoop_ct (hN : N = 272 ∨ N = 544) {η : Nat} (hη : η = 2 ∨ η = 4)
    (ho : (XN N σ₁).map (hbOks η) = (XN N σ₂).map (hbOks η)) :
    RelCT isa (fun a b => ((∃ x, J6 136 N (spOf σ₁) σ₁ x a) ∧ a.gpr .s7 = σ₁.gpr .a1) ∧
      ((∃ y, J6 136 N (spOf σ₂) σ₂ y b) ∧ b.gpr .s7 = σ₂.gpr .a1)) (rbLoop N η)
      fun a b => Base N σ₁ (XN N σ₁) N (Lf η (XN N σ₁) N) a ∧ Base N σ₂ (XN N σ₂) N (Lf η (XN N σ₂) N) b := by
  refine RelCT.seq (R := fun (a b : State) => Base N σ₁ (XN N σ₁) 0 (Lf η (XN N σ₁) 0) a ∧
      Base N σ₂ (XN N σ₂) 0 (Lf η (XN N σ₂) 0) b)
    (relct_wp (RelCT.block_append (RelCT.seq (R := fun _ _ => True) (Pack.relct_noMem rfl)
      (Pack.relct_noMem (by unfold loadQ Impl.MlDsa.RISCV64.Pack.loadQ VG.Impl.MlDsa.RISCV64.Arith.loadImm; rfl))))
      fun a b ⟨⟨⟨x, ha⟩, e₁⟩, ⟨⟨y, hb⟩, e₂⟩⟩ => ⟨?_, ?_⟩)
    (loop_ct h.hp₁ h.hp₂ h.sp h.a2 h.a3 hη (XN_length N σ₁) (XN_length N σ₂) ho (by omega))
  · rw [Lf_zero]; exact init_ok h.hp₁ hN ha e₁
  · rw [Lf_zero]; exact init_ok h.hp₂ hN hb e₂

/-- A try, in both runs, from the prologue's states. -/
theorem rbTry_ct (hN : N = 272 ∨ N = 544) :
    RelCT isa (fun a b => (J0 (spOf σ₁) σ₁ a ∧ a.gpr .s7 = σ₁.gpr .a1) ∧
      (J0 (spOf σ₁) σ₂ b ∧ b.gpr .s7 = σ₂.gpr .a1)) (rbTry N)
      fun a b => Base N σ₁ (XN N σ₁) N (Lf (etaOf σ₁) (XN N σ₁) N) a ∧
        Base N σ₂ (XN N σ₂) N (Lf (etaOf σ₁) (XN N σ₂) N) b := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  have eP := sp_eq h
  have hp₂' : SpOk (spOf σ₁) σ₂ := eP ▸ hp₂
  -- the sponge
  refine RelCT.seq (R := fun (a b : State) => ((∃ x, J6 136 N (spOf σ₁) σ₁ x a) ∧ a.gpr .s7 = σ₁.gpr .a1) ∧
      ((∃ y, J6 136 N (spOf σ₁) σ₂ y b) ∧ b.gpr .s7 = σ₂.gpr .a1))
    (relct_wp (RelCT.mono (sponge_ct hp₁ hp₂' h.sp (rate := 136) (outlen := N) (by decide) (by omega))
      (fun a b hab => ⟨hab.1.1, hab.2.1⟩) fun _ _ h => h) fun a b hab =>
      ⟨WP.mono (sponge_ok hp₁ (by decide) (by omega) hab.1.1) fun _ x => ⟨⟨_, x⟩, (x.gp .s7 (by decide)).trans hab.1.2⟩,
        WP.mono (sponge_ok hp₂' (by decide) (by omega) hab.2.1) fun _ x =>
          ⟨⟨_, x⟩, (x.gp .s7 (by decide)).trans hab.2.2⟩⟩) ?_
  -- the branch on `η`, and the loop
  refine RelCT.seq (R := fun (a b : State) => ((∃ x, J6 136 N (spOf σ₁) σ₁ x a) ∧
      a.gpr .a6 = subwV (σ₁.gpr .a1) 2 ∧ a.gpr .s7 = σ₁.gpr .a1) ∧
      ((∃ y, J6 136 N (spOf σ₂) σ₂ y b) ∧ b.gpr .a6 = subwV (σ₂.gpr .a1) 2 ∧ b.gpr .s7 = σ₂.gpr .a1))
    (relct_wp (Pack.relct_noMem (by unfold Impl.MlDsa.RISCV64.Pack.loadB VG.Impl.MlDsa.RISCV64.Arith.loadImm; rfl))
      fun a b hab => ⟨?_, ?_⟩) ?_
  · obtain ⟨⟨x, hx⟩, e7⟩ := hab.1
    exact WP.mono (cmp_ok hp₁ hx e7) fun s' ⟨hs, e, e'⟩ => ⟨⟨_, hs⟩, e, e'⟩
  · obtain ⟨⟨y, hy⟩, e7⟩ := hab.2
    exact WP.mono (cmp_ok hp₂ (s₀ := y) (by rw [eP]; exact hy) e7) fun s' ⟨hs, e, e'⟩ => ⟨⟨_, hs⟩, e, e'⟩
  have ho := oks h hN
  have hz : ∀ a b, (((∃ x, J6 136 N (spOf σ₁) σ₁ x a) ∧ a.gpr .a6 = subwV (σ₁.gpr .a1) 2 ∧
      a.gpr .s7 = σ₁.gpr .a1) ∧
      ((∃ y, J6 136 N (spOf σ₂) σ₂ y b) ∧ b.gpr .a6 = subwV (σ₂.gpr .a1) 2 ∧ b.gpr .s7 = σ₂.gpr .a1)) →
      isa.eval (.zero .a6) a = some (decide (etaOf σ₁ = 2)) ∧ isa.eval (.zero .a6) b = isa.eval (.zero .a6) a :=
    fun a b hab => ⟨by rw [Steps.eval_zero, hab.1.2.1, lo_sub_beq _ (by decide)],
      by rw [Steps.eval_zero, Steps.eval_zero, hab.1.2.1, hab.2.2.1, lo_sub_beq _ (by decide),
        lo_sub_beq _ (by decide), h.a1]⟩
  rcases h.hη with e | e
  · rw [e] at ho ⊢
    refine RelCT.ite (fun a b hab => (hz a b hab).2.symm)
      (RelCT.mono (rbLoop_ct h hN (η := 2) (.inl rfl) ho)
        (fun a b hab => ⟨⟨hab.1.1.1, hab.1.1.2.2⟩, ⟨hab.1.2.1, hab.1.2.2.2⟩⟩) fun _ _ h => h)
      (RelCT.of_false fun a b ⟨hab, he⟩ => by rw [(hz a b hab).1, e] at he; exact absurd he (by decide))
  · rw [e] at ho ⊢
    refine RelCT.ite (fun a b hab => (hz a b hab).2.symm)
      (RelCT.of_false fun a b ⟨hab, he⟩ => by rw [(hz a b hab).1, e] at he; exact absurd he (by decide))
      (RelCT.mono (rbLoop_ct h hN (η := 4) (.inr rfl) ho)
        (fun a b hab => ⟨⟨hab.1.1.1, hab.1.1.2.2⟩, ⟨hab.1.2.1, hab.1.2.2.2⟩⟩) fun _ _ h => h)

/-- The whole function. -/
theorem all_ct : RelCT isa (fun a b => a = σ₁ ∧ b = σ₂) Impl.MlDsa.RISCV64.Sample.rejBounded fun _ _ => True := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  have eP := sp_eq h
  have hp₂' : SpOk (spOf σ₁) σ₂ := eP ▸ hp₂
  -- the prologue
  refine RelCT.seq (R := fun (a b : State) => (J0 (spOf σ₁) σ₁ a ∧ a.gpr .s7 = σ₁.gpr .a1) ∧
      (J0 (spOf σ₁) σ₂ b ∧ b.gpr .s7 = σ₂.gpr .a1))
    (relct_wp (pro_rb_ct (fun a b hab => by rw [hab.1, hab.2]; exact h.sp)
      fun a b hab => by rw [hab.1, hab.2]; exact h.a3) fun a b hab => ⟨?_, ?_⟩) ?_
  · rw [hab.1]; exact pro_rb hp₁ rfl rfl rfl rfl
  · rw [hab.2]; exact pro_rb hp₂' h.a0.symm h.a2.symm h.a3.symm rfl
  -- the first try
  refine RelCT.seq (R := fun (a b : State) => Base 272 σ₁ (XN 272 σ₁) 272 (Lf (etaOf σ₁) (XN 272 σ₁) 272) a ∧
      Base 272 σ₂ (XN 272 σ₂) 272 (Lf (etaOf σ₁) (XN 272 σ₂) 272) b) (rbTry_ct h (.inl rfl)) ?_
  -- the test, alike in both runs: their samples are as long
  refine RelCT.seq (R := fun (a b : State) =>
      (Base 272 σ₁ (XN 272 σ₁) 272 (Lf (etaOf σ₁) (XN 272 σ₁) 272) a ∧
        (a.gpr .t0 == 0) = decide ((Lf (etaOf σ₁) (XN 272 σ₁) 272).length ≠ 256)) ∧
      (Base 272 σ₂ (XN 272 σ₂) 272 (Lf (etaOf σ₁) (XN 272 σ₂) 272) b ∧
        (b.gpr .t0 == 0) = decide ((Lf (etaOf σ₁) (XN 272 σ₂) 272).length ≠ 256)))
    (relct_wp (Pack.relct_noMem rfl) fun a b hab => ⟨test_ok hp₁ hab.1, test_ok hp₂ hab.2⟩) ?_
  have hl : (Lf (etaOf σ₁) (XN 272 σ₁) 272).length = (Lf (etaOf σ₁) (XN 272 σ₂) 272).length :=
    len_eq (oks h (.inl rfl)) 272
  -- the second try, if any
  refine RelCT.seq (R := fun (a b : State) => Env (spOf σ₁) σ₁ a ∧ Env (spOf σ₂) σ₂ b) ?_ ?_
  · refine RelCT.ite (fun a b hab => by rw [Steps.eval_zero, Steps.eval_zero, hab.1.2, hab.2.2, hl]) ?_ ?_
    · exact RelCT.mono (P := fun (a b : State) => (J0 (spOf σ₁) σ₁ a ∧ a.gpr .s7 = σ₁.gpr .a1) ∧
          (J0 (spOf σ₁) σ₂ b ∧ b.gpr .s7 = σ₂.gpr .a1))
        (Q := fun (a b : State) => Base 544 σ₁ (XN 544 σ₁) 544 (Lf (etaOf σ₁) (XN 544 σ₁) 544) a ∧
          Base 544 σ₂ (XN 544 σ₂) 544 (Lf (etaOf σ₁) (XN 544 σ₂) 544) b)
        (rbTry_ct h (.inr rfl))
        (fun a b hab => ⟨⟨⟨hab.1.1.1.env, hab.1.1.1.s9, hab.1.1.1.s8⟩, hab.1.1.1.s7⟩,
          ⟨eP ▸ (⟨hab.1.2.1.env, hab.1.2.1.s9, hab.1.2.1.s8⟩ : J0 (spOf σ₂) σ₂ b), hab.1.2.1.s7⟩⟩)
        fun a b hab => ⟨hab.1.env, hab.2.env⟩
    · exact relct_wp (Pack.relct_noMem rfl)
        fun a b hab => ⟨WP.block_nil hab.1.1.1.env, WP.block_nil hab.1.2.1.env⟩
  -- the end
  exact retEpi_ct (fun a b hab => by rw [hab.1.sp, hab.2.sp, h.sp]) fun a b hab => by
    rw [hab.1.s11, hab.2.s11]; exact h.a3

end

/-! ## `Verified` -/

/-- The precondition, as `SpOk` and `η`. -/
theorem pre_of {s : State} (h : (rejBoundedContract RISCV64.abi 1168).pre s) :
    SpOk (spOf s) s ∧ (etaOf s = 2 ∨ etaOf s = 4) := by
  sig_pre [rejBoundedContract, rejBoundedSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨h0, h1, h2, h3, d1, d2, d3, b1, b2, b3, -, fa, fscr, he, alA, alS⟩ := h
  exact ⟨⟨by rw [h2]; exact List.mem_singleton_self _, h3, d1, d2, d3, b1, b2, b3,
    show (66 : Nat) < 2 ^ 64 by decide, fa, fscr, h0, h1, alA, alS⟩, he⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 2 | .a2 => 0x2000 | .a3 => 0x3000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 66⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

end VG.Proof.MlDsa.RISCV64.Sample.RejBounded

namespace VG.Proof.MlDsa.RISCV64.Sample

open VG VG.RISCV64
open VG.Proof.MlDsa.Sample (rbFold rejBounded_some rejBounded_none stored_polyIs ifT ifF)
open VG.Proof.MlDsa (rejBoundedContract rejBoundedSig)
open RejBounded

theorem rejBounded_verified :
    Verified RISCV64.target Impl.MlDsa.RISCV64.Sample.rejBounded (rejBoundedContract RISCV64.abi 1168) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ⟨satState, ?_⟩⟩
  · obtain ⟨hp, hη⟩ := pre_of hs
    obtain ⟨t, s', he, h3, hst, ha⟩ := correct hp hη
    refine ⟨t, s', he, ha, ?_⟩
    have hL : Lf (etaOf s) (X s) 544 = rbFold (etaOf s) [] (X s) := by
      simp only [Lf]; rw [List.take_of_length_le (by rw [X_length])]
    rw [hL] at h3 hst
    sig_post [rejBoundedContract, rejBoundedSig, RISCV64.abi, RISCV64.argRegs]
    rw [h3]
    by_cases hf : (rbFold (etaOf s) [] (X s)).length = 256
    · rw [ifT hf]
      obtain ⟨hred, hpoly⟩ := stored_polyIs hst hf
      exact ⟨fun _ => hred, .inl ⟨rfl, { Spec.MlDsa.minBounds with rejBounded := 544 }, by
        show Option.map _ (Spec.MlDsa.rejBoundedPoly _ 544 _) = _
        exact (rejBounded_some _ hf).trans (congrArg some hpoly.symm)⟩⟩
    · rw [ifF hf]
      exact ⟨fun h1 => absurd h1 (by decide), .inr ⟨rfl, by
        show Option.map _ (Spec.MlDsa.rejBoundedPoly _ 481 _) = none
        exact (congrArg (Option.map _) (rejBounded_none _ (B := 544) (by decide) hf)).trans rfl⟩⟩
  · obtain ⟨hp₁, hη⟩ := pre_of h₁
    obtain ⟨hp₂, -⟩ := pre_of h₂
    sig_pub [rejBoundedContract, rejBoundedSig, RISCV64.abi, RISCV64.argRegs] at hpub
    obtain ⟨hsp, hl, h0, h1, h2, h3⟩ := hpub
    exact (all_ct ⟨hp₁, hp₂, hη, hsp, h0, h1, h2, h3, hl⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · sig_apply_check
    · decide +kernel
    · sig_reduce [rejBoundedContract, rejBoundedSig, RISCV64.abi, RISCV64.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | decide +kernel

end VG.Proof.MlDsa.RISCV64.Sample
