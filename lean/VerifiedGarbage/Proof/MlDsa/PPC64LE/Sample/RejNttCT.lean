module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.Pro
import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
import VerifiedGarbage.Proof.MlKem.PPC64LE.HashCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.Pro
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.HashCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.SigEval
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Sample.RejNtt
public import VerifiedGarbage.Proof.MlDsa.Sample.RejNtt
import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
meta import VerifiedGarbage.Impl.MlDsa.PPC64LE.Sample.RejNtt
meta import VerifiedGarbage.Proof.MlDsa.Sample.RejNtt
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd

/-! ### `MlDsa.PPC64LE.Sample.RejNtt`, which this module and modules that import it used -/

section

/-!
# ML-DSA on PPC64LE: `vg_mldsa_rej_ntt_poly`, correctness

As on 32-bit ARM (`Proof/MlDsa/Arm/Sample/RejNttCT.lean`). The function runs
in pieces: the prologue (`J0`), the sponge, whose output is `G(ρ, 1008)`
(`J6`), and the loop, iteration `t` of which starts from `LAt N σ t`, with the
coefficients `rnFold` samples from the first `3t` bytes of output stored. An
iteration loads the value of its 3 bytes and tests whether to keep it
(`pieceA`: it is less than `q` and `j < 256`), stores it if so (`pieceB`,
what `rnStep` does), and steps (`pieceC`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Sample.RejNtt

open VG VG.PPC64LE
open VG.Proof.MlDsa.PPC64LE.Sample
open VG.Impl.MlDsa.PPC64LE.Sample
open VG.Impl.Sha3.PPC64LE.Stream (mov)
open VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.PPC64LE (ptr_add count_sub count_nz wp_loop_nz)
open VG.Proof.MlKem.PPC64LE.Sample (read_one toNat_setWidth8)
open VG.Spec.MlDsa (Zq q G)
open VG.Proof.MlDsa (PolyIs)
open VG.Spec.Sha3 (bytesAt)

/-- The call, from the entry state: `seed = r3`, `a = r4`, `scratch = r5`. -/
abbrev spOf (σ : State) : Sp := ⟨σ.gpr .r3, 34, σ.gpr .r5, σ.gpr .r4⟩

/-- The seed. -/
abbrev B (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .r3) 34

/-- The XOF output of a loop of `N` iterations: `3N` bytes. -/
abbrev X (N : Nat) (σ : State) : List Byte := G (B σ) (3 * N)

/-- Byte `i` of the XOF output. -/
abbrev Xb (N : Nat) (σ : State) (i : Nat) : Byte := (X N σ).getD i 0

/-- The coefficients sampled after `t` iterations. -/
abbrev Lt (N : Nat) (σ : State) (t : Nat) : List Zq := rnFold [] ((X N σ).take (3 * t))

/-- The value of 3 bytes, as the code computes it. -/
def rnw (b₀ b₁ b₂ : Byte) : BitVec 64 :=
  b₂.setWidth 64 <<< 57 >>> 41 + b₁.setWidth 64 <<< 8 + b₀.setWidth 64

theorem rnw_toNat (b₀ b₁ b₂ : Byte) : (rnw b₀ b₁ b₂).toNat = rnZ b₀ b₁ b₂ := by
  have h0 := b₀.isLt
  have h1 := b₁.isLt
  have h2 := b₂.isLt
  unfold rnw rnZ
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft,
    toNat_setWidth8, toNat_setWidth8, toNat_setWidth8, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    Nat.shiftLeft_eq]
  omega_using []

/-- Nonzero exactly when the value `v` is kept, with `j` coefficients. -/
def accR (v j : BitVec 64) : BitVec 64 :=
  (v - BitVec.ofNat 64 8380417) >>> 63 &&& (j - BitVec.ofNat 64 256) >>> 63

theorem accR_eq {v j : BitVec 64} (hv : v.toNat < 2 ^ 23) (hj : j.toNat ≤ 256) :
    (accR v j == 0) = !decide (v.toNat < 8380417 ∧ j.toNat < 256) := by
  unfold accR
  by_cases h1 : v.toNat < 8380417 <;> by_cases h2 : j.toNat < 256
  · have e1 : (v - BitVec.ofNat 64 8380417) >>> 63 = 1 := by bv_omega
    have e2 : (j - BitVec.ofNat 64 256) >>> 63 = 1 := by bv_omega
    rw [e1, e2]; simp [h1, h2]
  · have e2 : (j - BitVec.ofNat 64 256) >>> 63 = 0 := by bv_omega
    rw [e2]; simp [h1, h2]
  · have e1 : (v - BitVec.ofNat 64 8380417) >>> 63 = 0 := by bv_omega
    rw [e1]; simp [h1, h2]
  · have e1 : (v - BitVec.ofNat 64 8380417) >>> 63 = 0 := by bv_omega
    rw [e1]; simp [h1, h2]

/-- The value of the 3 bytes of iteration `t`. -/
abbrev V (N : Nat) (σ : State) (t : Nat) : BitVec 64 := rnw (Xb N σ (3 * t)) (Xb N σ (3 * t + 1)) (Xb N σ (3 * t + 2))

theorem V_lt (N : Nat) (σ : State) (t : Nat) : (V N σ t).toNat < 2 ^ 23 := by
  rw [rnw_toNat]; unfold rnZ
  have := (Xb N σ (3 * t)).isLt; have := (Xb N σ (3 * t + 1)).isLt; have := (Xb N σ (3 * t + 2)).isLt
  omega_using []

theorem X_length (N : Nat) (σ : State) : (X N σ).length = 3 * N := G_length _ _

theorem take_add_three (L : List Byte) {i : Nat} (h : i + 3 ≤ L.length) :
    L.take (i + 3) = L.take i ++ [L.getD i 0, L.getD (i + 1) 0, L.getD (i + 2) 0] := by
  rw [List.take_add, List.drop_eq_getElem_cons (by omega_using [h]), List.drop_eq_getElem_cons (by omega_using [h]),
    List.drop_eq_getElem_cons (by omega_using [h])]
  simp only [List.take_succ_cons, List.take_zero, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show i < L.length by omega_using [h]), List.getElem?_eq_getElem (show i + 1 < L.length by omega_using [h]),
    List.getElem?_eq_getElem (show i + 2 < L.length by omega_using [h]), Option.getD_some]

theorem Lt_succ (N : Nat) (σ : State) {t : Nat} (ht : t < N) :
    Lt N σ (t + 1) = rnStep (Lt N σ t) (Xb N σ (3 * t)) (Xb N σ (3 * t + 1)) (Xb N σ (3 * t + 2)) := by
  simp only [Lt]
  rw [show 3 * (t + 1) = 3 * t + 3 by omega_using [], take_add_three _ (by rw [X_length]; omega_using [ht]),
    rnFold_snoc _ (by rw [List.length_take, X_length]; omega_using [])]

theorem Lt_length_le (N : Nat) (σ : State) (t : Nat) : (Lt N σ t).length ≤ 256 := rnFold_length_le (by simp) _

/-- At the start of iteration `t`. -/
structure LAt (N : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  env : Env (spOf σ) σ s
  nle : N ≤ 336
  out : bytesAt s.mem ((spOf σ).at' 840) (3 * N) = X N σ
  r3 : s.gpr .r3 = σ.gpr .r5 + BitVec.ofNat 64 (840 + 3 * t)
  r6 : s.gpr .r6 = BitVec.ofNat 64 (N - t)
  r7 : s.gpr .r7 = BitVec.ofNat 64 8380417
  r28 : s.gpr .r28 = BitVec.ofNat 64 34
  r29 : s.gpr .r29 = σ.gpr .r3
  at' : At (spOf σ) (Lt N σ t) s

/-- After the value of the 3 bytes and its test. -/
structure M1 (N : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  lat : LAt N σ t s
  r10 : s.gpr .r10 = V N σ t
  r12 : s.gpr .r12 = accR (V N σ t) (BitVec.ofNat 64 (Lt N σ t).length)

/-- After the coefficient of iteration `t`. -/
structure M2 (N : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  env : Env (spOf σ) σ s
  nle : N ≤ 336
  out : bytesAt s.mem ((spOf σ).at' 840) (3 * N) = X N σ
  r3 : s.gpr .r3 = σ.gpr .r5 + BitVec.ofNat 64 (840 + 3 * t)
  r6 : s.gpr .r6 = BitVec.ofNat 64 (N - t)
  r7 : s.gpr .r7 = BitVec.ofNat 64 8380417
  r28 : s.gpr .r28 = BitVec.ofNat 64 34
  r29 : s.gpr .r29 = σ.gpr .r3
  at' : At (spOf σ) (Lt N σ (t + 1)) s

section
variable {N : Nat} {σ : State} (hp : SpOk (spOf σ) σ)
include hp

/-- Byte `k` of iteration `t`. -/
theorem byte_ok {t : Nat} (ht : t < N) {s : State} (h : LAt N σ t s) {k : Nat} (hk : k < 3) :
    InRegions (s.rd ++ s.wr) (σ.gpr .r5 + BitVec.ofNat 64 (840 + 3 * t) + BitVec.ofNat 64 k) 1 ∧
      s.mem (σ.gpr .r5 + BitVec.ofNat 64 (840 + 3 * t) + BitVec.ofNat 64 k) = Xb N σ (3 * t + k) := by
  have := h.nle
  rw [ptr_add]
  refine ⟨inScrRd hp h.env.wr (by omega_using [ht, hk, this]), ?_⟩
  have := congrArg (fun L => L.getD (3 * t + k) 0) h.out
  rw [MlKem.bytesAt_getD _ _ (by omega_using [ht, hk]), ptr_add, ← Nat.add_assoc] at this
  exact this

omit hp in
theorem load_ok {s : State} {x : Addr} {j : BitVec 64} (h3 : s.gpr .r3 = x) (h5 : s.gpr .r5 = j)
    (h7 : s.gpr .r7 = BitVec.ofNat 64 8380417)
    (i0 : InRegions (s.rd ++ s.wr) x 1) (i1 : InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 1) 1)
    (i2 : InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 2) 1) :
    WP isa (.block (rnLoad ++ testJ [.sub .r12 .r10 .r7])) s fun t =>
      t.gpr .r10 = rnw (s.mem x) (s.mem (x + BitVec.ofNat 64 1)) (s.mem (x + BitVec.ofNat 64 2)) ∧
      t.gpr .r12 = accR (rnw (s.mem x) (s.mem (x + BitVec.ofNat 64 1)) (s.mem (x + BitVec.ofNat 64 2))) j ∧
      (∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  prun [rnLoad, testJ, rnw, accR, List.cons_append, List.nil_append, exec_lbz, read_one, h3, h5, h7, i0, i1, i2]
  simp only [true_and, and_true]
  intro r a b c d e
  simp only [RegUpd.gpr_write, a, b, c, d, e, ite_false]

/-- `LAt` through a block that writes no memory and none of `r3`–`r7` and
the callee-saved registers. -/
theorem LAt.keep {t : Nat} {s s' : State} (h : LAt N σ t s) (hm : s'.mem = s.mem)
    (g : ∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → s'.gpr r = s.gpr r) (rd : s'.rd = s.rd)
    (wr : s'.wr = s.wr) (sp : s'.sp = s.sp) : LAt N σ t s' := by
  have gp : ∀ r ∈ preserved, s'.gpr r = s.gpr r := fun r hr =>
    g r (by rintro rfl; exact absurd hr (by decide)) (by rintro rfl; exact absurd hr (by decide))
      (by rintro rfl; exact absurd hr (by decide)) (by rintro rfl; exact absurd hr (by decide))
      (by rintro rfl; exact absurd hr (by decide))
  exact ⟨h.env.regs hp hm gp rd wr sp, h.nle, by rw [hm]; exact h.out, (g _ (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans h.r3, (g _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.r6,
    (g _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.r7,
    (gp _ (by decide)).trans h.r28, (gp _ (by decide)).trans h.r29,
    ⟨(g _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.at'.r4,
      (g _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.at'.r5, h.at'.len,
      by rw [hm]; exact h.at'.st⟩⟩

theorem pieceA {t : Nat} (ht : t < N) {s : State} (h : LAt N σ t s) :
    WP isa (.block (rnLoad ++ testJ [.sub .r12 .r10 .r7])) s (M1 N σ t) := by
  obtain ⟨i0, v0⟩ := byte_ok hp ht h (k := 0) (by decide)
  obtain ⟨i1, v1⟩ := byte_ok hp ht h (k := 1) (by decide)
  obtain ⟨i2, v2⟩ := byte_ok hp ht h (k := 2) (by decide)
  rw [BitVec.add_zero] at i0 v0
  rw [Nat.add_zero] at v0
  refine WP.mono (load_ok h.r3 h.at'.r5 h.r7 i0 i1 i2) fun s' ⟨g10, g12, g, m, rd, wr, sp⟩ => ?_
  rw [v0, v1, v2] at g10 g12
  exact ⟨h.keep hp m g rd wr sp, g10, g12⟩

omit hp in
theorem zw_V {t : Nat} (hq : (V N σ t).toNat < q) : (V N σ t).setWidth 32 = zw (Fin.ofNat q (V N σ t).toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [zw_toNat, Fin.val_ofNat, Nat.mod_eq_of_lt hq, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (by have := V_lt N σ t; omega_using [this])]

theorem pieceB {t : Nat} (ht : t < N) {s : State} (h : M1 N σ t s) : WP isa (accept .r10) s (M2 N σ t) := by
  have l := h.lat
  have hl : (BitVec.ofNat 64 (Lt N σ t).length).toNat = (Lt N σ t).length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Lt_length_le N σ t; omega_using [this])]
  have ez := accR_eq (V_lt N σ t) (j := BitVec.ofNat 64 (Lt N σ t).length) (by rw [hl]; exact Lt_length_le N σ t)
  rw [hl, ← h.r12] at ez
  have hstep := Lt_succ N σ ht
  rw [rnStep, ← rnw_toNat] at hstep
  by_cases hz : s.gpr .r12 = 0
  · have hn : ¬ ((V N σ t).toNat < 8380417 ∧ (Lt N σ t).length < 256) := by
      intro hc; rw [hz] at ez; simp [hc] at ez
    have e : Lt N σ (t + 1) = Lt N σ t := by
      rw [hstep]
      by_cases hl' : (Lt N σ t).length < 256
      · rw [ifT (show (Lt N σ t).length < Spec.MlDsa.n from hl'),
          ifF (show ¬ (V N σ t).toNat < q from fun hq => hn ⟨hq, hl'⟩)]
      · rw [ifF (show ¬ (Lt N σ t).length < Spec.MlDsa.n from hl')]
    exact WP.mono (accept_skip hz) fun s' e' => by
      subst e'; exact ⟨l.env, l.nle, l.out, l.r3, l.r6, l.r7, l.r28, l.r29, e ▸ l.at'⟩
  · have hy : (V N σ t).toNat < 8380417 ∧ (Lt N σ t).length < 256 := by
      have : (s.gpr .r12 == 0) = false := by simpa using hz
      rw [this] at ez; simpa using ez
    have e : Lt N σ (t + 1) = Lt N σ t ++ [Fin.ofNat q (V N σ t).toNat] := by
      rw [hstep, ifT (show (Lt N σ t).length < Spec.MlDsa.n from hy.2), ifT (show (V N σ t).toNat < q from hy.1)]
    refine WP.mono (accept_store hp l.env l.at' hy.2 (by rw [h.r10]; exact zw_V hy.1) hz)
      fun s' ⟨at', env', rr, hf⟩ => ⟨env', l.nle, ?_, (rr _ (by decide) (by decide)).trans l.r3,
        (rr _ (by decide) (by decide)).trans l.r6, (rr _ (by decide) (by decide)).trans l.r7,
        (rr _ (by decide) (by decide)).trans l.r28, (rr _ (by decide) (by decide)).trans l.r29, e ▸ at'⟩
    rw [MlKem.bytesAt_frame hf (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact (hp.a_scr.sub_right (sub_scr (a := 840) (n := 3 * N) (by have := l.nle; omega_using [this]))).symm) (by have := l.nle; omega_using [this])]
    exact l.out

theorem pieceC {t : Nat} (ht : t < N) {s : State} (h : M2 N σ t s) :
    WP isa (.block [.addi .r3 .r3 3, .subi .r6 .r6 1]) s fun s' =>
      LAt N σ (t + 1) s' ∧ (s'.gpr .r6 != 0) = decide (t + 1 ≠ N) := by
  have hk : WP isa (.block [.addi .r3 .r3 3, .subi .r6 .r6 1]) s fun s' =>
      s'.gpr .r3 = s.gpr .r3 + BitVec.ofNat 64 3 ∧ s'.gpr .r6 = s.gpr .r6 - BitVec.ofNat 64 1 ∧
      (∀ r, r ≠ .r3 → r ≠ .r6 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
    prun []
    simp only [true_and, and_true]
    intro r a b
    simp only [RegUpd.gpr_write, a, b, ite_false]
  refine WP.mono hk fun s' ⟨r3, r6, g, m, rd, wr, sp⟩ => ⟨⟨?_, h.nle, by rw [m]; exact h.out, ?_, ?_,
    (g _ (by decide) (by decide)).trans h.r7, (g _ (by decide) (by decide)).trans h.r28,
    (g _ (by decide) (by decide)).trans h.r29, ⟨(g _ (by decide) (by decide)).trans h.at'.r4,
      (g _ (by decide) (by decide)).trans h.at'.r5, h.at'.len, by rw [m]; exact h.at'.st⟩⟩, ?_⟩
  · exact h.env.regs hp m (fun r hr => g r (by rintro rfl; exact absurd hr (by decide))
      (by rintro rfl; exact absurd hr (by decide))) rd wr sp
  · rw [r3, h.r3, ptr_add, show 840 + 3 * t + 3 = 840 + 3 * (t + 1) by omega_using []]
  · rw [r6, h.r6]; exact count_sub ht
  · rw [r6, h.r6, count_sub ht]; exact count_nz ht (by have := h.nle; omega_using [this])

end

section
variable {N : Nat} {σ : State} (hp : SpOk (spOf σ) σ)
include hp

/-- An iteration. -/
theorem body_ok {t : Nat} (ht : t < N) {s : State} (h : LAt N σ t s) :
    WP isa rnBody s fun s' => LAt N σ (t + 1) s' ∧ (s'.gpr .r6 != 0) = decide (t + 1 ≠ N) :=
  WP.seq (WP.mono (pieceA hp ht h) fun _ h1 => WP.seq (WP.mono (pieceB hp ht h1) fun _ h2 => pieceC hp ht h2))

omit hp in
theorem Lt_zero : Lt N σ 0 = [] := by simp [Lt, rnFold]

/-- The loop's setup, after the sponge. -/
theorem lat0 (hN : N ≤ 336) {s₀ s : State} (h : J6 168 (3 * N) (spOf σ) σ s₀ s) :
    WP isa (.block (([.addi .r3 .r31 840, mov .r4 .r30, .li .r5 0, .li .r6 N] : List Instr) ++ loadQ)) s
      (LAt N σ 0) := by
  have g30 := h.j0.env.r30
  have g31 := h.j0.env.r31
  have hN' : N < 32768 := by omega_using [hN]
  have hk : WP isa (.block (([.addi .r3 .r31 840, mov .r4 .r30, .li .r5 0, .li .r6 N] : List Instr) ++ loadQ)) s
      fun s' => s'.gpr .r3 = σ.gpr .r5 + BitVec.ofNat 64 (840 + 3 * 0) ∧ s'.gpr .r4 = σ.gpr .r4 ∧
        s'.gpr .r5 = BitVec.ofNat 64 0 ∧ s'.gpr .r6 = BitVec.ofNat 64 N ∧
        s'.gpr .r7 = BitVec.ofNat 64 8380417 ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
    prun [loadQ, List.cons_append, List.nil_append, exec_lis, exec_ori, loadQ_val, g30, g31, hN']
    simp only [true_and, and_true]
    pres_tac
  refine WP.mono hk fun s' ⟨g3, g4, g5, g6, g7, gp, m, rd, wr, sp⟩ => ⟨h.j0.env.regs hp m gp rd wr sp, hN,
    by rw [m, h.out]; exact (G_eq _ _).symm, g3, by rw [Nat.sub_zero]; exact g6, g7,
    (gp _ (by decide)).trans h.j0.r28, (gp _ (by decide)).trans h.j0.r29, ?_⟩
  rw [Lt_zero]
  exact ⟨by rw [g4]; exact (BitVec.add_zero _).symm, g5, by simp, stored_nil _ _⟩

theorem loop_ok (hN0 : 0 < N) (hN : N ≤ 336) {s₀ s : State} (h : J6 168 (3 * N) (spOf σ) σ s₀ s) :
    WP isa (rnLoop N) s (LAt N σ N) :=
  WP.seq (WP.mono (lat0 hp hN h) fun _ h0 =>
    wp_loop_nz (LAt N σ) (N := N) hN0 (fun _ ht _ h => body_ok hp ht h) (fun _ h => h) h0)

/-- A try with `N` iterations, from the registers of the sponge's arguments. -/
theorem rnTry_ok (hN0 : 0 < N) (hN : N ≤ 336) {s : State} (j0 : J0 (spOf σ) σ s) :
    WP isa (rnTry N) s (LAt N σ N) :=
  WP.seq (WP.mono (sponge_ok hp (rate := 168) (outlen := 3 * N) (by decide) (by omega_using [hN]) j0) fun _ h =>
    loop_ok hp hN0 hN h)

/-- The test of `j = 256`. -/
theorem jtest_ok {t : Nat} {s : State} (h : LAt N σ t s) :
    WP isa (.block [.subi .r12 .r5 256]) s fun s' => LAt N σ t s' ∧
      isa.eval (.zero .d .r12) s' = some (decide ((Lt N σ t).length = 256)) := by
  have hk : WP isa (.block [.subi .r12 .r5 256]) s fun s' => s' = s.write .r12 (s.gpr .r5 - BitVec.ofNat 64 256) := by
    prun []
  refine WP.mono hk fun s' e' => ?_
  subst e'
  refine ⟨h.keep hp rfl (fun r _ _ _ _ a => RegUpd.gpr_write_of_ne _ _ a) rfl rfl rfl, ?_⟩
  rw [eval_zero, RegUpd.gpr_write_self, h.at'.r5]
  have hl := Lt_length_le N σ t
  by_cases e : (Lt N σ t).length = 256
  · rw [e]; rfl
  · rw [decide_eq_false e]
    exact congrArg some (beq_eq_false_iff_ne.mpr (by bv_omega))

omit hp in
theorem Lt_all : Lt N σ N = rnFold [] (X N σ) := by
  simp only [Lt]; rw [List.take_of_length_le (by rw [X_length])]

/-- The coefficients the function samples: those of the first 840 bytes if
there are 256 of them, and those of 1008 bytes otherwise. -/
abbrev Lr (σ : State) : List Zq :=
  if (rnFold [] (X 280 σ)).length = 256 then rnFold [] (X 280 σ) else rnFold [] (X 336 σ)

theorem end_ok {s : State} (h : LAt N σ N s) (hL : rnFold [] (X N σ) = Lr σ) :
    WP isa (.block (retJ ++ epi)) s fun s' => s'.gpr .r3 = (if (Lr σ).length = 256 then 1 else 0) ∧
      ((Lr σ).length = 256 → PolyIs s'.mem (σ.gpr .r4) (toPoly (Lr σ))) ∧
      abiPreserved σ s' :=
  WP.mono (retEpi_ok hp h.env h.at'.r5 (Lt_length_le _ _ _)) fun s' ⟨h3, hm, ha⟩ =>
    ⟨by rw [h3, Lt_all, hL], fun hf => by
      rw [hm]
      have hs := h.at'.st
      rw [Lt_all, hL] at hs
      exact stored_polyIs hs hf, ha⟩

/-- The function, from an entry state whose regions are those of a call. -/
theorem correct : WP isa Impl.MlDsa.PPC64LE.Sample.rejNTT σ fun s' =>
    s'.gpr .r3 = (if (Lr σ).length = 256 then 1 else 0) ∧
      ((Lr σ).length = 256 → PolyIs s'.mem (σ.gpr .r4) (toPoly (Lr σ))) ∧
      abiPreserved σ s' := by
  unfold rejNTT
  refine WP.seq (WP.mono (pro_rn hp rfl rfl rfl rfl) fun _ ⟨j1, _⟩ => ?_)
  refine WP.seq (WP.mono (rnTry_ok hp (N := 280) (by decide) (by decide) j1) fun s1 h1 => ?_)
  refine WP.seq (WP.seq (WP.mono (jtest_ok hp h1) fun s2 ⟨h2, ev⟩ =>
    WP.ite _ ev (fun he => ?_) (fun he => ?_)))
  · simp only [decide_eq_true_eq] at he
    rw [Lt_all] at he
    exact WP.block_nil (end_ok hp h2 (by rw [Lr, ifT he]))
  · simp only [decide_eq_false_iff_not] at he
    rw [Lt_all] at he
    exact WP.mono (rnTry_ok hp (N := 336) (by decide) (by decide) ⟨h2.env, h2.r29, h2.r28⟩)
      fun s3 h3 => end_ok hp h3 (by rw [Lr, ifF he])

end

end VG.Proof.MlDsa.PPC64LE.Sample.RejNtt

end

end

/-!
# ML-DSA on PPC64LE: `vg_mldsa_rej_ntt_poly`, constant time but for the seed, and `Verified`

As on 32-bit ARM (`Proof/MlDsa/Arm/Sample/RejNttCT.lean`). Two runs from
entry states whose seeds (the declared leak), pointers and stack pointers
agree leak the same (`all_ct`): the prologue and the blocks around the loops
by the taint analysis, each try (`rnTry_ct`): the sponge by `sponge_ct`, and
the loop, whose
branches and stores depend on the XOF output, by relating the two runs
iteration by iteration (`body_ct`): both are at the same iteration with the
same coefficients sampled and the same bytes to read, so each branch goes
the same way and each store goes to the same address; so the test of
whether the first try sampled 256 coefficients agrees too.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Sample.RejNtt

open VG VG.PPC64LE
open VG.Proof.MlDsa.PPC64LE.Sample
open VG.Impl.MlDsa.PPC64LE.Sample
open VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.PPC64LE (relct_noMem relct_nil)
open VG.Proof.MlKem.PPC64LE.Sample (taint_block relct_wp)
open VG.Spec.MlDsa (Zq q G)
open VG.Proof.MlDsa (PolyIs)
open VG.Spec.Sha3 (bytesAt rates)

/-- Two runs, from entry states that agree on the public data. -/
structure Two (σ₁ σ₂ : State) : Prop where
  hp₁ : SpOk (spOf σ₁) σ₁
  hp₂ : SpOk (spOf σ₂) σ₂
  sp : σ₁.sp = σ₂.sp
  r3 : σ₁.gpr .r3 = σ₂.gpr .r3
  r4 : σ₁.gpr .r4 = σ₂.gpr .r4
  r5 : σ₁.gpr .r5 = σ₂.gpr .r5
  B : B σ₁ = B σ₂

section
variable {σ₁ σ₂ : State} (h : Two σ₁ σ₂)
include h

theorem sp_eq : spOf σ₂ = spOf σ₁ := by simp only [spOf, h.r3, h.r4, h.r5]

theorem X_eq (N : Nat) : X N σ₁ = X N σ₂ := by simp only [X, h.B]

theorem Lt_eq (N t : Nat) : Lt N σ₁ t = Lt N σ₂ t := by simp only [Lt, X_eq h]

theorem V_eq (N t : Nat) : V N σ₁ t = V N σ₂ t := by simp only [V, Xb, X_eq h]

theorem lsp {N N' t t' : Nat} {a b : State} (ha : LAt N σ₁ t a) (hb : LAt N' σ₂ t' b) : a.sp = b.sp := by
  rw [ha.env.sp, hb.env.sp, h.sp]

/-! ## The loop -/

theorem body_ct {N t : Nat} (ht : t < N) :
    RelCT isa (fun a b => LAt N σ₁ t a ∧ LAt N σ₂ t b) rnBody fun a b =>
      (LAt N σ₁ (t + 1) a ∧ (a.gpr .r6 != 0) = decide (t + 1 ≠ N)) ∧
      (LAt N σ₂ (t + 1) b ∧ (b.gpr .r6 != 0) = decide (t + 1 ≠ N)) := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  refine relct_wp ?_ fun a b hab => ⟨body_ok hp₁ ht hab.1, body_ok hp₂ ht hab.2⟩
  refine RelCT.seq (R := fun a b => M1 N σ₁ t a ∧ M1 N σ₂ t b) (relct_wp ?_ fun a b hab =>
    ⟨pieceA hp₁ ht hab.1, pieceA hp₂ ht hab.2⟩) ?_
  · exact taint_block [.r3] (fun a b hab => lsp h hab.1 hab.2) (fun a b hab r hr => by
      rw [List.mem_singleton] at hr; subst hr; rw [hab.1.r3, hab.2.r3, h.r5]) (by taint_decide)
  refine RelCT.seq (R := fun a b => M2 N σ₁ t a ∧ M2 N σ₂ t b) (relct_wp ?_ fun a b hab =>
    ⟨pieceB hp₁ ht hab.1, pieceB hp₂ ht hab.2⟩) (relct_noMem rfl)
  refine accept_ct (fun a b hab => lsp h hab.1.lat hab.2.lat) (fun a b hab => ?_) fun a b hab => ?_
  · rw [hab.1.r12, hab.2.r12, V_eq h, Lt_eq h]
  · rw [hab.1.lat.at'.r4, hab.2.lat.at'.r4, Lt_eq h, sp_eq h]

theorem loop_ct {N : Nat} (hN : 0 < N) :
    RelCT isa (fun a b => LAt N σ₁ 0 a ∧ LAt N σ₂ 0 b) (.loop rnBody (.nonzero .d .r6)) fun a b =>
      LAt N σ₁ N a ∧ LAt N σ₂ N b := by
  refine RelCT.mono (RelCT.loop (M := isa) (body := rnBody) (c := .nonzero .d .r6)
    (Q := fun a b => LAt N σ₁ N a ∧ LAt N σ₂ N b)
    (fun n a b => ∃ t, t < N ∧ n = N - t ∧ LAt N σ₁ t a ∧ LAt N σ₂ t b) (fun n => ?_) N)
    (fun a b hab => ⟨0, hN, rfl, hab⟩) (fun _ _ h => h)
  refine RelCT.mono (P := fun a b => ∃ t, t < N ∧ n = N - t ∧ LAt N σ₁ t a ∧ LAt N σ₂ t b)
    (RelCT.exists_ fun t => ?_) (fun _ _ hab => hab) (fun _ _ h => h)
  by_cases ht : t < N
  · by_cases hn : n = N - t
    · refine RelCT.mono (P := fun a b => LAt N σ₁ t a ∧ LAt N σ₂ t b) (body_ct h ht) (fun _ _ hab => hab.2.2)
        fun a b ⟨⟨i₁, z₁⟩, ⟨i₂, z₂⟩⟩ => ⟨?_, fun e => ?_, fun e => ?_⟩
      · rw [eval_nonzero, eval_nonzero, z₁, z₂]
      · have : t + 1 = N := by
          have e' : (a.gpr .r6 != 0) = false := by rw [eval_nonzero] at e; exact Option.some.inj e
          rw [z₁] at e'; simpa using e'
        rw [this] at i₁ i₂; exact ⟨i₁, i₂⟩
      · have : t + 1 ≠ N := by
          have e' : (a.gpr .r6 != 0) = true := by rw [eval_nonzero] at e; exact Option.some.inj e
          rw [z₁] at e'; simpa using e'
        exact ⟨N - (t + 1), by omega_using [ht, hn], t + 1, by omega_using [ht, this], rfl, i₁, i₂⟩
    · exact RelCT.of_false fun _ _ hab => hn hab.2.1
  · exact RelCT.of_false fun _ _ hab => ht hab.1

/-! ## The whole function -/

/-- A try with `N` iterations: the sponge, and the loop. -/
theorem rnTry_ct {N : Nat} (hN0 : 0 < N) (hN : N ≤ 336) :
    RelCT isa (fun a b => J0 (spOf σ₁) σ₁ a ∧ J0 (spOf σ₁) σ₂ b) (rnTry N) fun a b => LAt N σ₁ N a ∧ LAt N σ₂ N b := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  have eP := sp_eq h
  have hp₂' : SpOk (spOf σ₁) σ₂ := eP ▸ hp₂
  refine RelCT.seq (R := fun a b => (∃ x, J6 168 (3 * N) (spOf σ₁) σ₁ x a) ∧ (∃ y, J6 168 (3 * N) (spOf σ₁) σ₂ y b))
    (relct_wp (sponge_ct hp₁ hp₂' h.sp (by decide) (by omega_using [hN])) fun a b hab =>
      ⟨WP.mono (sponge_ok hp₁ (by decide) (by omega_using [hN]) hab.1) fun _ x => ⟨_, x⟩,
        WP.mono (sponge_ok hp₂' (by decide) (by omega_using [hN]) hab.2) fun _ x => ⟨_, x⟩⟩) ?_
  exact RelCT.seq (R := fun a b => LAt N σ₁ 0 a ∧ LAt N σ₂ 0 b)
    (relct_wp (relct_noMem rfl) fun a b ⟨⟨x, ha⟩, ⟨y, hb⟩⟩ =>
      ⟨lat0 hp₁ hN ha, lat0 hp₂ hN (by rw [eP]; exact hb)⟩) (loop_ct h hN0)

theorem all_ct : RelCT isa (fun a b => a = σ₁ ∧ b = σ₂) Impl.MlDsa.PPC64LE.Sample.rejNTT fun _ _ => True := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  have eP := sp_eq h
  have hp₂' : SpOk (spOf σ₁) σ₂ := eP ▸ hp₂
  refine RelCT.seq (R := fun a b => J0 (spOf σ₁) σ₁ a ∧ J0 (spOf σ₁) σ₂ b) (relct_wp (pro_rn_ct
    (fun a b hab => by rw [hab.1, hab.2]; exact h.sp) fun a b hab => by rw [hab.1, hab.2]; exact h.r5)
    fun a b hab => ⟨?_, ?_⟩) ?_
  · rw [hab.1]; exact WP.mono (pro_rn hp₁ rfl rfl rfl rfl) fun _ x => x.1
  · rw [hab.2]; exact WP.mono (pro_rn hp₂' h.r3.symm h.r4.symm h.r5.symm rfl) fun _ x => x.1
  refine RelCT.seq (rnTry_ct h (N := 280) (by decide) (by decide)) ?_
  refine RelCT.seq (R := fun (a b : State) => (∃ N t, LAt N σ₁ t a) ∧ (∃ N t, LAt N σ₂ t b)) ?_ ?_
  · refine RelCT.seq (R := fun (a b : State) =>
        (LAt 280 σ₁ 280 a ∧ isa.eval (.zero .d .r12) a = some (decide ((Lt 280 σ₁ 280).length = 256))) ∧
        (LAt 280 σ₂ 280 b ∧ isa.eval (.zero .d .r12) b = some (decide ((Lt 280 σ₂ 280).length = 256))))
      (relct_wp (relct_noMem rfl) fun a b hab => ⟨jtest_ok hp₁ hab.1, jtest_ok hp₂ hab.2⟩) ?_
    refine RelCT.ite (fun a b hab => by rw [hab.1.2, hab.2.2, Lt_eq h]) ?_ ?_
    · exact RelCT.mono relct_nil (fun _ _ h => h) fun a b hab => ⟨⟨_, _, hab.1.1.1⟩, ⟨_, _, hab.1.2.1⟩⟩
    · refine RelCT.mono (rnTry_ct h (N := 336) (by decide) (by decide)) (fun a b hab => ⟨?_, ?_⟩)
        fun a b hab => ⟨⟨_, _, hab.1⟩, ⟨_, _, hab.2⟩⟩
      · exact ⟨hab.1.1.1.env, hab.1.1.1.r29, hab.1.1.1.r28⟩
      · have b₂ := hab.1.2.1
        exact eP ▸ ⟨b₂.env, b₂.r29, b₂.r28⟩
  exact retEpi_ct (fun a b ⟨⟨_, _, ha⟩, ⟨_, _, hb⟩⟩ => lsp h ha hb)
    fun a b ⟨⟨_, _, ha⟩, ⟨_, _, hb⟩⟩ => by rw [ha.env.r31, hb.env.r31]; exact h.r5

end

/-! ## `Verified` -/

theorem spOk_of {s : State} (h : (Proof.MlDsa.rejNTTContract PPC64LE.abi 48).pre s) : SpOk (spOf s) s := by
  sig_pre [Proof.MlDsa.rejNTTContract, Proof.MlDsa.rejNTTSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨by rw [h1]; exact List.mem_singleton_self _, h2, h3, h4, h5, h6, h7, h8, show (34 : Nat) < 2 ^ 64 by decide, h10, h11, h0⟩

theorem leakBytes_inj : ∀ {a b : List Byte}, a.map (fun x => x.toNat) = b.map (fun x => x.toNat) → a = b
  | [], [], _ => rfl
  | x :: a, y :: b, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, leakBytes_inj h.2]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 34⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

end VG.Proof.MlDsa.PPC64LE.Sample.RejNtt

namespace VG.Proof.MlDsa.PPC64LE.Sample

open VG VG.PPC64LE
open VG.Proof.MlDsa.Sample
open RejNtt

theorem rejNTT_verified :
    Verified PPC64LE.target Impl.MlDsa.PPC64LE.Sample.rejNTT (Proof.MlDsa.rejNTTContract PPC64LE.abi 48) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, h3, hpoly, ha⟩ := correct (spOk_of hs)
    refine ⟨t, s', he, ha, ?_⟩
    sig_post [Proof.MlDsa.rejNTTContract, Proof.MlDsa.rejNTTSig, PPC64LE.abi, PPC64LE.argRegs]
    rw [h3]
    by_cases h1 : (rnFold [] (X 280 s)).length = 256
    · rw [Lr, ifT h1, ifT h1] at *
      have hpi := hpoly h1
      exact ⟨fun _ => hpi.1, .inl ⟨rfl, { Spec.MlDsa.minBounds with rejNTT := 840 }, by
        show Spec.MlDsa.rejNTTPoly (3 * 280) _ = _
        exact (rejNTT_some h1).trans (congrArg some hpi.2.symm)⟩⟩
    · simp only [Lr, ifF h1] at hpoly ⊢
      by_cases hf : (rnFold [] (X 336 s)).length = 256
      · rw [ifT hf]
        have hpi := hpoly hf
        exact ⟨fun _ => hpi.1, .inl ⟨rfl, { Spec.MlDsa.minBounds with rejNTT := 1008 }, by
          show Spec.MlDsa.rejNTTPoly (3 * 336) _ = _
          exact (rejNTT_some hf).trans (congrArg some hpi.2.symm)⟩⟩
      · rw [ifF hf]
        exact ⟨fun e => absurd e (by decide), .inr ⟨rfl, rejNTT_none (B := 3 * 336) (by decide) (by decide) hf⟩⟩
  · sig_pub [Proof.MlDsa.rejNTTContract, Proof.MlDsa.rejNTTSig, PPC64LE.abi, PPC64LE.argRegs] at hpub
    obtain ⟨hsp, hb, h3, h4, h5⟩ := hpub
    exact (all_ct ⟨spOk_of h₁, spOk_of h₂, hsp, h3, h4, h5, leakBytes_inj hb⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩
      e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.rejNTTContract, Proof.MlDsa.rejNTTSig, PPC64LE.abi, PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | decide +kernel

end VG.Proof.MlDsa.PPC64LE.Sample
