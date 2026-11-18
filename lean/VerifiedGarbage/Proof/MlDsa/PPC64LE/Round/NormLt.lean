module

import VerifiedGarbage.Proof.MlDsa.PPC64LE.Round.Arith
public import VerifiedGarbage.Proof.MlDsa.Round.Mem
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
import VerifiedGarbage.Proof.MlKem.PPC64LE.Add
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.Common
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Round.Arith
meta import VerifiedGarbage.Proof.MlDsa.Round.Mem
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Add
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.Common
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Run
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
meta import Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Round
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.MlDsa.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.Pro
import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
import VerifiedGarbage.Proof.MlKem.PPC64LE.HashCT
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.Pro
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.HashCT
meta import VerifiedGarbage.Proof.Framework.SigEval
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.MlDsa.Sample.LeWord
import VerifiedGarbage.Proof.MlDsa.Sample.LeNat
import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Sample.Ball
public import VerifiedGarbage.Proof.MlDsa.Sample.ExpandMask
meta import VerifiedGarbage.Proof.MlDsa.Sample.LeWord
meta import VerifiedGarbage.Proof.MlDsa.Sample.LeNat
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Impl.MlDsa.PPC64LE.Sample.Ball
meta import VerifiedGarbage.Proof.MlDsa.Sample.ExpandMask

/-! ### `MlDsa.PPC64LE.Sample.BallCT`, which the modules that import this one used -/

section

/-! ### `MlDsa.PPC64LE.Sample.Ball`, which this module and modules that import it used -/

section

/-! ### `MlDsa.PPC64LE.Sample.BallLoop`, which this module and modules that import it used -/

section

/-!
# ML-DSA on PPC64LE: the loops of `vg_mldsa_sample_in_ball`

As on 32-bit ARM (`Proof/MlDsa/Arm/Sample/Ball.lean`). A call is
described by `spOf σ` (`c̃`, its length, `scratch` and `c`), `τ` is the low
32 bits of `r5`, and the XOF output is `X σ`, `H(c̃, 272)`. The polynomial `c`
is kept in memory as the words that represent its coefficients modulo `q`
(`CStored`); the first loop zeroes it (`zero_ok`). The setup of the second
(`setup_ok`) loads the sign bits, the first 8 bytes of output as a
little-endian doubleword, into `r9`. Iteration `t` of the second starts from
`BAt σ t`: with the polynomial and `i` (in `r5`, and `r4` at `c[i]`) that
`bFold` computes from the first `t` bytes after the sign bits, and the sign
bits not yet used in `r9`, the first 8 bytes shifted right once per
coefficient set (`Sg`). The pieces of an iteration are `pieceA` (`i < 256`?),
`tryA` (the byte `j`, and `j ≤ i`?), `setOk` (`c[i] ← c[j]`, `c[j] ← ±1`) and
`pieceC` (the step).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Sample.Ball

open VG VG.PPC64LE
open VG.Proof.MlDsa.PPC64LE.Sample
open VG.Impl.MlDsa.PPC64LE.Sample
open VG.Impl.Sha3.PPC64LE.Stream (mov)
open VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.PPC64LE (ptr_add count_sub count_nz wp_loop_nz)
open VG.Proof.MlKem.PPC64LE.Sample (read_one toNat_setWidth8)
open VG.Spec.MlDsa (Zq q H IPoly n ofInt toRq)
open VG.Proof.MlDsa (coeffAt PolyIs)
open VG.Spec.Sha3 (bytesAt)

/-- The call, from the entry state: `ctilde = r3`, `len = r4`, `c = r6`,
`scratch = r7`. -/
abbrev spOf (σ : State) : Sp := ⟨σ.gpr .r3, (σ.gpr .r4).toNat, σ.gpr .r7, σ.gpr .r6⟩

/-- `τ`, the low 32 bits of `r5`. -/
abbrev tau (σ : State) : Nat := ((σ.gpr .r5).setWidth 32).toNat

/-- `c̃`. -/
abbrev B (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .r3) (σ.gpr .r4).toNat

/-- The XOF output. -/
abbrev X (σ : State) : List Byte := H (B σ) 272

/-- The first `i`. -/
abbrev i0 (σ : State) : Nat := 256 - tau σ

/-- The sign bits, as a number. -/
abbrev Wn (σ : State) : Nat := leNat ((X σ).take 8)

/-- The polynomial and `i` after `t` iterations. -/
abbrev St (σ : State) (t : Nat) : IPoly × Nat :=
  bFold (tau σ) (signs (X σ)) (Vector.replicate n 0, i0 σ) (((X σ).drop 8).take t)

/-- The polynomial `c` of `R` is stored at `p`, as elements of `ℤ_q`. -/
def CStored (m : Mem) (p : Addr) (c : IPoly) : Prop := ∀ k < 256, coeffAt m p k = zw (ofInt c[k]!)

/-- What the proofs need of the entry state. -/
structure Pre (σ : State) : Prop where
  ok : SpOk (spOf σ) σ
  tau_le : tau σ ≤ 60

theorem X_length (σ : State) : (X σ).length = 272 := H_length _ _

theorem St_le (σ : State) (t : Nat) : (St σ t).2 ≤ 256 := bFold_le (by simp) _

theorem St_ge (σ : State) (t : Nat) : i0 σ ≤ (St σ t).2 :=
  bFold_ge (τ := tau σ) (h := signs (X σ)) (Vector.replicate n 0, i0 σ) _

/-- The sign bits not yet used, from their value. -/
abbrev Sg (σ : State) (i : Nat) (s : State) : Prop := (s.gpr .r9).toNat = Wn σ / 2 ^ (i - i0 σ)

/-! ## Zeroing -/

/-- After `k` iterations of the zeroing loop. -/
structure ZAt (σ : State) (k : Nat) (s : State) : Prop where
  env : Env (spOf σ) σ s
  r27 : s.gpr .r27 = zx (σ.gpr .r5)
  out : bytesAt s.mem ((spOf σ).at' 840) 272 = X σ
  r12 : s.gpr .r12 = 0
  r4 : s.gpr .r4 = (spOf σ).a + BitVec.ofNat 64 (4 * k)
  r6 : s.gpr .r6 = BitVec.ofNat 64 (256 - k)
  zero : ∀ j < k, coeffAt s.mem (spOf σ).a j = 0

/-- After the zeroing. -/
structure ZDone (σ : State) (s : State) : Prop where
  env : Env (spOf σ) σ s
  r27 : s.gpr .r27 = zx (σ.gpr .r5)
  out : bytesAt s.mem ((spOf σ).at' 840) 272 = X σ
  st : CStored s.mem (spOf σ).a (Vector.replicate n 0)

section
variable {σ : State} (hp : SpOk (spOf σ) σ)
include hp

theorem zBody_ok {k : Nat} (hk : k < 256) {s : State} (h : ZAt σ k s) :
    WP isa (.block [.store .w .r12 .r4 0, .addi .r4 .r4 4, .subi .r6 .r6 1]) s fun s' =>
      ZAt σ (k + 1) s' ∧ (s'.gpr .r6 != 0) = decide (k + 1 ≠ 256) := by
  have cA := coeff_contains (spOf σ).a (i := k) hk
  have iA : InRegions s.wr ((spOf σ).a + BitVec.ofNat 64 (4 * k)) 4 :=
    ⟨(spOf σ).aR, by rw [h.env.wr, hp.wr]; simp, cA⟩
  have hk' : WP isa (.block [.store .w .r12 .r4 0, .addi .r4 .r4 4, .subi .r6 .r6 1]) s fun t =>
      t.mem = s.mem.writeW ((spOf σ).a + BitVec.ofNat 64 (4 * k)) ((s.gpr .r12).setWidth 32) ∧
      t.gpr .r4 = (spOf σ).a + BitVec.ofNat 64 (4 * k) + BitVec.ofNat 64 4 ∧
      t.gpr .r6 = s.gpr .r6 - BitVec.ofNat 64 1 ∧
      (∀ r, r ≠ .r4 → r ≠ .r6 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
    prun [exec_store_w, h.r4, iA]
    simp only [true_and, and_true]
    intro r h4 h6
    simp only [RegUpd.gpr_write, h4, h6, ite_false]
  refine WP.mono hk' fun t ⟨m, r4, r6, rr, rd, wr, sp⟩ => ?_
  have hf : Frame [(spOf σ).aR] s.mem t.mem := by
    rw [m]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ cA
  refine ⟨⟨h.env.step hp hf (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact .inr (.inl fun _ h => h))
    (fun r hr => rr r (by rintro rfl; exact absurd hr (by decide)) (by rintro rfl; exact absurd hr (by decide)))
    rd wr sp, (rr _ (by decide) (by decide)).trans h.r27, ?_, (rr _ (by decide) (by decide)).trans h.r12,
    by rw [r4, MlKem.PPC64LE.ptr_succ], by rw [r6, h.r6]; exact count_sub hk, fun j hj => ?_⟩, ?_⟩
  · rw [MlKem.bytesAt_frame hf (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact (hp.a_scr.sub_right (sub_scr (a := 840) (n := 272) (by decide))).symm) (by decide)]
    exact h.out
  · rw [m, coeffAt_writeW _ _ (by omega_arith) hk, h.r12]
    by_cases e : k = j
    · rw [ifT e]; rfl
    · rw [ifF e]; exact h.zero j (by omega_arith)
  · rw [r6, h.r6, count_sub hk]; exact count_nz hk (by decide)

/-- The zeroing loop, from what the sponge leaves. -/
theorem zero_ok {s₀ s : State} (h : J6 136 272 (spOf σ) σ s₀ s) (h27 : s₀.gpr .r27 = zx (σ.gpr .r5)) :
    WP isa bZero s (ZDone σ) := by
  have g30 := h.j0.env.r30
  have hk : WP isa (.block [.li .r12 0, mov .r4 .r30, .li .r6 256]) s fun t =>
      t.gpr .r12 = 0 ∧ t.gpr .r4 = (spOf σ).a + BitVec.ofNat 64 (4 * 0) ∧
      t.gpr .r6 = BitVec.ofNat 64 (256 - 0) ∧ (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
    prun [g30]
    simp only [true_and, and_true]
    refine ⟨rfl, ?_⟩
    pres_tac
  refine WP.seq (WP.mono hk fun s1 ⟨r12, r4, r6, gp, m, rd, wr, sp⟩ => ?_)
  refine wp_loop_nz (ZAt σ) (N := 256) (by decide) (fun k hk s h => zBody_ok hp hk h)
    (fun s h => ⟨h.env, h.r27, h.out, fun k hk => ?_⟩) ⟨h.j0.env.regs hp m gp rd wr sp,
      by rw [gp _ (by decide), h.gp _ (by decide), h27], by rw [m, h.out]; exact (H_eq _ _).symm, r12, r4, r6,
      fun _ h => absurd h (Nat.not_lt_zero _)⟩
  rw [h.zero k hk, getElem!_pos _ k (by simp only [n]; omega_arith), Vector.getElem_replicate]
  rfl

end

/-! ## Small facts -/

/-- `(x - y) >>> 63` is zero exactly when `y ≤ x`. -/
theorem sgn_beq {x y : Nat} (hx : x < 2 ^ 62) (hy : y < 2 ^ 62) :
    ((BitVec.ofNat 64 x - BitVec.ofNat 64 y) >>> 63 == 0) = decide (y ≤ x) := by
  by_cases h : y ≤ x
  · have e : (BitVec.ofNat 64 x - BitVec.ofNat 64 y) >>> 63 = 0 := by bv_omega
    rw [e, decide_eq_true h]; rfl
  · have e : (BitVec.ofNat 64 x - BitVec.ofNat 64 y) >>> 63 = 1 := by bv_omega
    rw [e, decide_eq_false h]; rfl

theorem byte_ofNat (b : Byte) : b.setWidth 64 = BitVec.ofNat 64 b.toNat :=
  BitVec.eq_of_toNat_eq (by rw [toNat_setWidth8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := b.isLt; omega_arith)])

theorem shl2 {j : Nat} (hj : j < 2 ^ 32) : BitVec.ofNat 64 j <<< 2 = BitVec.ofNat 64 (4 * j) :=
  BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega_arith), Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith)

theorem setWidth_32_64_32 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x :=
  BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth]
    have := x.isLt
    omega_arith)

/-- The word of the sign, from the low bit of `x`. -/
theorem sgn_val (x : BitVec 64) :
    ((x <<< 63 >>> 63) * BitVec.ofNat 64 8380415 + BitVec.ofNat 64 1).setWidth 32 =
      if x.toNat % 2 = 1 then BitVec.ofNat 32 8380416 else 1 := by
  have e : x <<< 63 >>> 63 = BitVec.ofNat 64 (x.toNat % 2) := BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
      Nat.shiftRight_eq_div_pow]
    have := x.isLt
    omega_arith)
  rw [e]
  by_cases h : x.toNat % 2 = 1
  · rw [ifT h, h]; decide
  · rw [ifF h, show x.toNat % 2 = 0 by omega_arith]; decide

/-- The word of the sign: 1, or `q - 1` for -1. -/
theorem sgn_word (b : Bool) :
    (if b then (BitVec.ofNat 32 8380416) else 1) = zw (ofInt (if b then -1 else 1)) := by
  cases b <;> decide

/-! ## An iteration -/

/-- Byte `t` after the sign bits. -/
abbrev Xb (σ : State) (t : Nat) : Byte := (X σ).getD (8 + t) 0

theorem take_succ' (L : List Byte) {i : Nat} (h : i < L.length) : L.take (i + 1) = L.take i ++ [L.getD i 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem St_succ (σ : State) {t : Nat} (ht : t < 264) :
    St σ (t + 1) = bStep (tau σ) (signs (X σ)) (St σ t) (Xb σ t) := by
  simp only [St]
  rw [take_succ' _ (by rw [List.length_drop, X_length]; omega_arith), bFold_snoc, List.getD_eq_getElem?_getD,
    List.getElem?_drop, ← List.getD_eq_getElem?_getD]

/-- At the start of iteration `t`. -/
structure BAt (σ : State) (t : Nat) (s : State) : Prop where
  env : Env (spOf σ) σ s
  out : bytesAt s.mem ((spOf σ).at' 840) 272 = X σ
  r3 : s.gpr .r3 = (spOf σ).scr + BitVec.ofNat 64 (848 + t)
  r4 : s.gpr .r4 = coeffAddr (spOf σ).a (St σ t).2
  r5 : s.gpr .r5 = BitVec.ofNat 64 (St σ t).2
  sg : Sg σ (St σ t).2 s
  r6 : s.gpr .r6 = BitVec.ofNat 64 (264 - t)
  r7 : s.gpr .r7 = BitVec.ofNat 64 8380415
  st : CStored s.mem (spOf σ).a (St σ t).1

section
variable {σ : State} (hp : SpOk (spOf σ) σ)
include hp

/-- `BAt` after code that writes no memory and only `r8`, `r10`–`r12`. -/
theorem BAt.keep {t : Nat} {s s' : State} (h : BAt σ t s) (hm : s'.mem = s.mem)
    (g : ∀ r, r ≠ .r8 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → s'.gpr r = s.gpr r) (rd : s'.rd = s.rd)
    (wr : s'.wr = s.wr) (sp : s'.sp = s.sp) : BAt σ t s' := by
  have gp : ∀ r ∈ preserved, s'.gpr r = s.gpr r := fun r hr =>
    g r (by rintro rfl; exact absurd hr (by decide)) (by rintro rfl; exact absurd hr (by decide))
      (by rintro rfl; exact absurd hr (by decide)) (by rintro rfl; exact absurd hr (by decide))
  exact ⟨h.env.regs hp hm gp rd wr sp, by rw [hm]; exact h.out,
    (g _ (by decide) (by decide) (by decide) (by decide)).trans h.r3,
    (g _ (by decide) (by decide) (by decide) (by decide)).trans h.r4,
    (g _ (by decide) (by decide) (by decide) (by decide)).trans h.r5,
    by show _ = _; rw [g _ (by decide) (by decide) (by decide) (by decide)]; exact h.sg,
    (g _ (by decide) (by decide) (by decide) (by decide)).trans h.r6,
    (g _ (by decide) (by decide) (by decide) (by decide)).trans h.r7, by rw [hm]; exact h.st⟩

end

/-- After the test of `i`. -/
structure M1 (σ : State) (t : Nat) (s : State) : Prop where
  bat : BAt σ t s
  z : (s.gpr .r12 == 0) = decide (256 ≤ (St σ t).2)

/-- After the test of the byte `j`, if `i < 256`. -/
structure T1 (σ : State) (t : Nat) (s : State) : Prop where
  bat : BAt σ t s
  lt : (St σ t).2 < 256
  r8 : s.gpr .r8 = BitVec.ofNat 64 (Xb σ t).toNat
  z : (s.gpr .r11 == 0) = decide ((Xb σ t).toNat ≤ (St σ t).2)

/-- After the coefficients of iteration `t`. -/
structure M2 (σ : State) (t : Nat) (s : State) : Prop where
  env : Env (spOf σ) σ s
  out : bytesAt s.mem ((spOf σ).at' 840) 272 = X σ
  r3 : s.gpr .r3 = (spOf σ).scr + BitVec.ofNat 64 (848 + t)
  r4 : s.gpr .r4 = coeffAddr (spOf σ).a (St σ (t + 1)).2
  r5 : s.gpr .r5 = BitVec.ofNat 64 (St σ (t + 1)).2
  sg : Sg σ (St σ (t + 1)).2 s
  r6 : s.gpr .r6 = BitVec.ofNat 64 (264 - t)
  r7 : s.gpr .r7 = BitVec.ofNat 64 8380415
  st : CStored s.mem (spOf σ).a (St σ (t + 1)).1

/-- `M2` when iteration `t` changes nothing. -/
theorem M2.of_same {σ : State} {t : Nat} {s : State} (l : BAt σ t s) (hst : St σ (t + 1) = St σ t) : M2 σ t s :=
  ⟨l.env, l.out, l.r3, by rw [hst]; exact l.r4, by rw [hst]; exact l.r5, by rw [hst]; exact l.sg, l.r6, l.r7,
    by rw [hst]; exact l.st⟩

section
variable {σ : State} (hp : SpOk (spOf σ) σ)
include hp

theorem pieceA {t : Nat} {s : State} (h : BAt σ t s) :
    WP isa (.block [.subi .r12 .r5 256, .lsr .d .r12 .r12 63]) s (M1 σ t) := by
  have hk : WP isa (.block [.subi .r12 .r5 256, .lsr .d .r12 .r12 63]) s fun t =>
      t.gpr .r12 = (s.gpr .r5 - BitVec.ofNat 64 256) >>> 63 ∧
      (∀ r, r ≠ .r12 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
    prun []
    simp only [true_and, and_true]
    intro r h12
    simp only [RegUpd.gpr_write, h12, ite_false]
  refine WP.mono hk fun s' ⟨g12, g, m, rd, wr, sp⟩ => ⟨h.keep hp m (fun r _ _ _ d => g r d) rd wr sp, ?_⟩
  have := St_le σ t
  rw [g12, h.r5, sgn_beq (by omega_arith) (by decide)]

theorem tryA {t : Nat} (ht : t < 264) {s : State} (h : M1 σ t s) (hz : (s.gpr .r12 == 0) = false) :
    WP isa (.block [.lbz .r8 .r3 0, .sub .r11 .r5 .r8, .lsr .d .r11 .r11 63]) s (T1 σ t) := by
  have hl : (St σ t).2 < 256 := by
    have := h.z; rw [hz] at this; simp at this; omega_arith
  have l := h.bat
  have iB : InRegions (s.rd ++ s.wr) ((spOf σ).scr + BitVec.ofNat 64 (848 + t)) 1 :=
    inScrRd hp l.env.wr (a := 848 + t) (by omega_arith)
  have hb : s.mem ((spOf σ).scr + BitVec.ofNat 64 (848 + t)) = Xb σ t := by
    have := congrArg (fun L => L.getD (8 + t) 0) l.out
    rw [MlKem.bytesAt_getD _ _ (by omega_arith), ptr_add, show 840 + (8 + t) = 848 + t by omega_arith] at this
    exact this
  have hk : WP isa (.block [.lbz .r8 .r3 0, .sub .r11 .r5 .r8, .lsr .d .r11 .r11 63]) s fun u =>
      u.gpr .r8 = (s.mem ((spOf σ).scr + BitVec.ofNat 64 (848 + t))).setWidth 64 ∧
      u.gpr .r11 = (s.gpr .r5 - (s.mem ((spOf σ).scr + BitVec.ofNat 64 (848 + t))).setWidth 64) >>> 63 ∧
      (∀ r, r ≠ .r8 → r ≠ .r11 → u.gpr r = s.gpr r) ∧ u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧
      u.sp = s.sp := by
    prun [exec_lbz, read_one, l.r3, iB]
    simp only [true_and, and_true]
    intro r h8 h11
    simp only [RegUpd.gpr_write, h8, h11, ite_false]
  refine WP.mono hk fun s' ⟨g8, g11, g, m, rd, wr, sp⟩ =>
    ⟨l.keep hp m (fun r a _ c _ => g r a c) rd wr sp, hl, by rw [g8, hb, byte_ofNat], ?_⟩
  have := (Xb σ t).isLt
  rw [g11, hb, byte_ofNat, l.r5, sgn_beq (by omega_arith) (by omega_arith)]

omit hp in
/-- The sign bit of `i`, from the sign bits not yet used. -/
theorem sign_bit {i : Nat} (hτ : tau σ ≤ 256) (hi0 : i0 σ ≤ i) {s : State} (hs : Sg σ i s) :
    ((s.gpr .r9).toNat % 2 = 1) = ((signs (X σ)).getD (i + tau σ - 256) false = true) := by
  have e0 : i0 σ = 256 - tau σ := rfl
  rw [signs_getD, testBit_eq, show i + tau σ - 256 = i - i0 σ by omega_arith, hs, decide_eq_true_iff]

omit hp in
theorem bSet_ok (s : State) {Ai Aj : Addr} (hAi : s.gpr .r4 = Ai) (hAj : s.gpr .r30 + s.gpr .r8 <<< 2 = Aj)
    (iJ : InRegions (s.rd ++ s.wr) Aj 4) (wI : InRegions s.wr Ai 4) (wJ : InRegions s.wr Aj 4) :
    WP isa (.block bSet) s fun u =>
      u.mem = (s.mem.writeW Ai (((s.mem.readW Aj 32).setWidth 64).setWidth 32)).writeW Aj
        ((s.gpr .r9 <<< 63 >>> 63 * s.gpr .r7 + BitVec.ofNat 64 1).setWidth 32) ∧
      u.gpr .r9 = s.gpr .r9 >>> 1 ∧ u.gpr .r4 = s.gpr .r4 + BitVec.ofNat 64 4 ∧
      u.gpr .r5 = s.gpr .r5 + BitVec.ofNat 64 1 ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → u.gpr r = s.gpr r) ∧
      u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp := by
  prun [bSet, exec_load_w, exec_store_w, exec_mul, hAj, hAi, iJ, wI, wJ]
  simp only [true_and, and_true]
  intro r a b c d e f
  simp only [RegUpd.gpr_write, a, b, c, d, e, f, ite_false]

end

theorem sgn_val' (x : BitVec 64) {b : Bool} (hb : x.toNat % 2 = 1 ↔ b = true) :
    ((x <<< 63 >>> 63) * BitVec.ofNat 64 8380415 + BitVec.ofNat 64 1).setWidth 32 =
      if b then BitVec.ofNat 32 8380416 else 1 := by
  rw [sgn_val]
  by_cases h : x.toNat % 2 = 1
  · rw [ifT h, ifT (hb.mp h)]
  · rw [ifF h, ifF (fun e => h (hb.mpr e))]

section
variable {σ : State} (hp : SpOk (spOf σ) σ)
include hp

/-- `c[i] ← c[j]`, `c[j] ← ±1`, `i` incremented. -/
theorem setOk (hτ : tau σ ≤ 256) {t : Nat} (ht : t < 264) {s : State} (h : T1 σ t s)
    (hz : (s.gpr .r11 == 0) = true) : WP isa (.block bSet) s (M2 σ t) := by
  have l := h.bat
  have hi := h.lt
  have hj : (Xb σ t).toNat ≤ (St σ t).2 := by have := h.z; rw [hz] at this; simpa using this
  have hAj : s.gpr .r30 + s.gpr .r8 <<< 2 = coeffAddr (spOf σ).a (Xb σ t).toNat := by
    rw [l.env.r30, h.r8, shl2 (by have := (Xb σ t).isLt; omega_arith)]
  have inI : (spOf σ).aR.Contains (coeffAddr (spOf σ).a (St σ t).2) 4 := coeff_contains _ hi
  have inJ : (spOf σ).aR.Contains (coeffAddr (spOf σ).a (Xb σ t).toNat) 4 := coeff_contains _ (by omega_arith)
  have wA : (spOf σ).aR ∈ s.wr := by rw [l.env.wr, hp.wr]; simp
  refine WP.mono (bSet_ok s l.r4 hAj ⟨_, List.mem_append_right _ wA, inJ⟩ ⟨_, wA, inI⟩ ⟨_, wA, inJ⟩)
    fun u ⟨m, g9, g4, g5, g, rd, wr, sp⟩ => ?_
  have hst := St_succ σ ht
  rw [bStep, ifT hi, ifF (show ¬ (Xb σ t).toNat > (St σ t).2 by omega_arith)] at hst
  have hf : Frame [(spOf σ).aR] s.mem u.mem := by
    rw [m]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ inI).writeW (List.mem_singleton_self _) _ inJ
  have gk : ∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → u.gpr r = s.gpr r := g
  have ge := St_ge σ t
  refine ⟨l.env.step hp hf (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact .inr (.inl fun _ h => h))
    (fun r hr => gk r (by rintro rfl; exact absurd hr (by decide)) (by rintro rfl; exact absurd hr (by decide))
      (by rintro rfl; exact absurd hr (by decide)) (by rintro rfl; exact absurd hr (by decide))
      (by rintro rfl; exact absurd hr (by decide)) (by rintro rfl; exact absurd hr (by decide)))
    rd wr sp, ?_, (gk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans l.r3,
    ?_, ?_, ?_, (gk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans l.r6,
    (gk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans l.r7, ?_⟩
  · rw [MlKem.bytesAt_frame hf (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact (hp.a_scr.sub_right (sub_scr (a := 840) (n := 272) (by decide))).symm) (by decide)]
    exact l.out
  · rw [g4, l.r4, hst]; exact MlKem.PPC64LE.ptr_succ _ 4 _
  · rw [g5, l.r5, hst, BitVec.ofNat_add]
  · rw [hst]
    show (u.gpr .r9).toNat = _
    have hs := l.sg
    simp only [Sg] at hs
    rw [g9, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hs, Nat.div_div_eq_div_mul, ← Nat.pow_succ,
      show (St σ t).2 + 1 - i0 σ = (St σ t).2 - i0 σ + 1 by omega_arith]
  · intro k hk
    have hsb := Iff.of_eq (sign_bit hτ ge l.sg)
    rw [hst, m, l.r7, sgn_val' _ hsb, sgn_word, coeffAt_writeW _ _ hk (by omega_arith), coeffAt_writeW _ _ hk hi,
      ipoly_set!_get _ _ (by simp only [n]; omega_arith), ipoly_set!_get _ _ (by simp only [n]; omega_arith)]
    by_cases ejk : (Xb σ t).toNat = k
    · rw [ifT ejk, ifT ejk]
    · rw [ifF ejk, ifF ejk]
      by_cases eik : (St σ t).2 = k
      · subst eik; rw [ifT rfl, ifT rfl, setWidth_32_64_32, ← coeffAt_eq, l.st _ (by omega_arith)]
      · rw [ifF eik, ifF eik]; exact l.st k hk

theorem tryB (hτ : tau σ ≤ 256) {t : Nat} (ht : t < 264) {s : State} (h : T1 σ t s) :
    WP isa (.ite (.zero .d .r11) (.block bSet) (.block [])) s (M2 σ t) := by
  refine WP.ite _ (eval_zero _ _) (fun e => setOk hp hτ ht h e) (fun e => ?_)
  have hj : (St σ t).2 < (Xb σ t).toNat := by
    have := h.z; rw [e] at this; exact Nat.lt_of_not_le (of_decide_eq_false this.symm)
  have hst := St_succ σ ht
  rw [bStep, ifT h.lt, ifT hj] at hst
  exact wp_nil (M2.of_same h.bat hst)

theorem pieceB (hτ : tau σ ≤ 256) {t : Nat} (ht : t < 264) {s : State} (h : M1 σ t s) :
    WP isa (.ite (.zero .d .r12) (.block []) bTry) s (M2 σ t) := by
  refine WP.ite _ (eval_zero _ _) (fun e => ?_) (fun e => WP.seq (WP.mono (tryA hp ht h e) fun _ h1 => tryB hp hτ ht h1))
  have hl : (St σ t).2 = 256 := by
    have := h.z; rw [e] at this; simp at this; have := St_le σ t; omega_arith
  exact wp_nil (M2.of_same h.bat (by rw [St_succ σ ht, bStep_full hl]))

theorem pieceC {t : Nat} (ht : t < 264) {s : State} (h : M2 σ t s) :
    WP isa (.block [.addi .r3 .r3 1, .subi .r6 .r6 1]) s fun s' =>
      BAt σ (t + 1) s' ∧ (s'.gpr .r6 != 0) = decide (t + 1 ≠ 264) := by
  have hk : WP isa (.block [.addi .r3 .r3 1, .subi .r6 .r6 1]) s fun s' =>
      s'.gpr .r3 = s.gpr .r3 + BitVec.ofNat 64 1 ∧ s'.gpr .r6 = s.gpr .r6 - BitVec.ofNat 64 1 ∧
      (∀ r, r ≠ .r3 → r ≠ .r6 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
    prun []
    simp only [true_and, and_true]
    intro r a b
    simp only [RegUpd.gpr_write, a, b, ite_false]
  refine WP.mono hk fun s' ⟨r3, r6, g, m, rd, wr, sp⟩ => ⟨⟨?_, by rw [m]; exact h.out, ?_,
    (g _ (by decide) (by decide)).trans h.r4, (g _ (by decide) (by decide)).trans h.r5,
    by show _ = _; rw [g _ (by decide) (by decide)]; exact h.sg, ?_, (g _ (by decide) (by decide)).trans h.r7,
    by rw [m]; exact h.st⟩, ?_⟩
  · exact h.env.regs hp m (fun r hr => g r (by rintro rfl; exact absurd hr (by decide))
      (by rintro rfl; exact absurd hr (by decide))) rd wr sp
  · rw [r3, h.r3, ptr_add, Nat.add_assoc]
  · rw [r6, h.r6]; exact count_sub ht
  · rw [r6, h.r6, count_sub ht]; exact count_nz ht (by decide)

/-- An iteration. -/
theorem body_ok (hτ : tau σ ≤ 256) {t : Nat} (ht : t < 264) {s : State} (h : BAt σ t s) :
    WP isa bBody s fun s' => BAt σ (t + 1) s' ∧ (s'.gpr .r6 != 0) = decide (t + 1 ≠ 264) :=
  WP.seq (WP.mono (pieceA hp h) fun _ h1 => WP.seq (WP.mono (pieceB hp hτ ht h1) fun _ h2 => pieceC hp ht h2))

end

end VG.Proof.MlDsa.PPC64LE.Sample.Ball

end

end

/-!
# ML-DSA on PPC64LE: `vg_mldsa_sample_in_ball`, correctness

As on 32-bit ARM (`Proof/MlDsa/Arm/Sample/Ball.lean`). The function runs in
pieces: the prologue (`J0`, with `r27` the zero-extended `τ`), the sponge,
whose output is `H(c̃, 272)` (`J6`), the zeroing of `c` (`ZDone`), the setup
of the loop, which loads the sign bits (`setup_ok`, with `readW_leNat`: the
doubleword is the first 8 bytes of output as a little-endian number), and the
264 iterations of the loop (`BAt`, `body_ok`), after which `c` and `i` are
what `ballFold` computes.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Sample.Ball

open VG VG.PPC64LE
open VG.Proof.MlDsa.PPC64LE.Sample
open VG.Impl.MlDsa.PPC64LE.Sample
open VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.PPC64LE (wp_loop_nz)
open VG.Spec.MlDsa (Zq q H IPoly n ofInt toRq)
open VG.Proof.MlDsa (coeffAt PolyIs)
open VG.Spec.Sha3 (bytesAt)

/-! ## The setup of the loop -/

/-- `lis` and `ori` of `q - 2`. -/
theorem q2_val :
    ((0x7F : BitVec 16) ++ (0 : BitVec 16)).signExtend 64 ||| (0xDFFF : BitVec 16).setWidth 64 =
      BitVec.ofNat 64 8380415 := by decide

/-- The first `i`, `256 - τ`. -/
theorem i0_val (x : BitVec 64) (h : (x.setWidth 32).toNat ≤ 256) :
    BitVec.ofNat 64 256 - zx x = BitVec.ofNat 64 (256 - (x.setWidth 32).toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, zx_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega_using [h]

section
variable {σ : State} (hp : SpOk (spOf σ) σ) (hτ : tau σ ≤ 256)
include hp hτ

theorem setup_ok {s : State} (h : ZDone σ s) : WP isa (.block bSetup) s (BAt σ 0) := by
  have g30 := h.env.r30
  have g31 := h.env.r31
  have g27 := h.r27
  have i9 : InRegions (s.rd ++ s.wr) ((spOf σ).scr + BitVec.ofNat 64 840) 8 := inScrRd hp h.env.wr (by decide)
  have hk : WP isa (.block bSetup) s fun u =>
      u.gpr .r9 = s.mem.readW ((spOf σ).scr + BitVec.ofNat 64 840) 64 ∧
      u.gpr .r5 = BitVec.ofNat 64 256 - zx (σ.gpr .r5) ∧
      u.gpr .r4 = (spOf σ).a + (BitVec.ofNat 64 256 - zx (σ.gpr .r5)) <<< 2 ∧
      u.gpr .r3 = (spOf σ).scr + BitVec.ofNat 64 848 ∧ u.gpr .r6 = BitVec.ofNat 64 264 ∧
      u.gpr .r7 = BitVec.ofNat 64 8380415 ∧
      (∀ r ∈ preserved, u.gpr r = s.gpr r) ∧ u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp := by
    prun [bSetup, exec_lis, exec_ori, q2_val, g30, g31, g27, i9]
    simp only [true_and, and_true]
    pres_tac
  refine WP.mono hk fun u ⟨g9, g5, g4, g3, g6, g7, gp, m, rd, wr, sp⟩ => ?_
  have e0 := i0_val (σ.gpr .r5) hτ
  have hSt : St σ 0 = (Vector.replicate n 0, i0 σ) := rfl
  refine ⟨h.env.regs hp m gp rd wr sp, by rw [m]; exact h.out, g3, ?_, ?_, ?_, g6, g7, by rw [m, hSt]; exact h.st⟩
  · rw [g4, e0, hSt, shl2 (by omega_using [])]
  · rw [g5, e0, hSt]
  · show (u.gpr .r9).toNat = _
    rw [hSt, Nat.sub_self, Nat.pow_zero, Nat.div_one, g9, readW_leNat _ _ (X σ) fun k hk => by
      have := congrArg (fun L => L.getD k 0) h.out
      rw [MlKem.bytesAt_getD _ _ (by omega_using [hk])] at this
      exact this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have := leNat_lt ((X σ).take 8)
    rw [List.length_take, X_length] at this
    exact this

/-- The loop, from the zeroed polynomial. -/
theorem loop_ok {s : State} (h : ZDone σ s) : WP isa bLoop s (BAt σ 264) :=
  WP.seq (WP.mono (setup_ok hp hτ h) fun _ h0 =>
    wp_loop_nz (BAt σ) (N := 264) (by decide) (fun t ht s h => body_ok hp hτ ht h) (fun _ h => h) h0)

end

/-! ## The end -/

theorem St_all (σ : State) : St σ 264 = ballFold (tau σ) (X σ) := by
  simp only [St, ballFold, i0]; rw [List.take_of_length_le (by rw [List.length_drop, X_length])]

theorem end_ok {σ : State} (hp : SpOk (spOf σ) σ) {s : State} (h : BAt σ 264 s) :
    WP isa (.block (retJ ++ epi)) s fun s' =>
      s'.gpr .r3 = (if (ballFold (tau σ) (X σ)).2 = 256 then 1 else 0) ∧
      ((ballFold (tau σ) (X σ)).2 = 256 →
        PolyIs s'.mem (σ.gpr .r6) (toRq (ballFold (tau σ) (X σ)).1)) ∧
      abiPreserved σ s' :=
  WP.mono (retEpi_ok hp h.env h.r5 (St_le _ _)) fun s' ⟨h3, hm, ha⟩ => ⟨by rw [h3, St_all], fun _ => by
    rw [hm]
    have hst := h.st
    rw [St_all] at hst
    refine polyIs_of_coeffAt fun i hi => ?_
    rw [hst i hi, getElem!_pos _ i hi, getElem!_pos _ i hi]
    simp only [toRq, Vector.getElem_map], ha⟩

/-- The function, from an entry state whose regions are those of a call. -/
theorem correct {σ : State} (hp : Pre σ) : WP isa Impl.MlDsa.PPC64LE.Sample.sampleInBall σ fun s' =>
    s'.gpr .r3 = (if (ballFold (tau σ) (X σ)).2 = 256 then 1 else 0) ∧
      ((ballFold (tau σ) (X σ)).2 = 256 →
        PolyIs s'.mem (σ.gpr .r6) (toRq (ballFold (tau σ) (X σ)).1)) ∧
      abiPreserved σ s' := by
  have hτ : tau σ ≤ 256 := by have := hp.tau_le; omega_using [this]
  exact WP.seq (WP.mono (pro_ball hp.ok rfl (by simp) rfl rfl) fun s₁ ⟨j1, h27⟩ =>
    WP.seq (WP.mono (sponge_ok hp.ok (rate := 136) (outlen := 272) (by decide) (by decide) j1)
      fun _ h2 => WP.seq (WP.mono (zero_ok hp.ok h2 h27) fun _ h3 => WP.seq (WP.mono (loop_ok hp.ok hτ h3)
        fun _ h4 => end_ok hp.ok h4))))

end VG.Proof.MlDsa.PPC64LE.Sample.Ball

end

end

/-!
# ML-DSA on PPC64LE: `vg_mldsa_sample_in_ball`, constant time but for `c̃`, and `Verified`

As on 32-bit ARM (`Proof/MlDsa/Arm/Sample/BallCT.lean`). Two runs whose `c̃`
(the declared leak), `len`, `τ` (the low 32 bits of `r5`), pointers and stack
pointer agree (`Two`) leak the same: the prologue, the zeroing and the blocks
around the loop by the taint analysis, the sponge by `sponge_ct`, and the
loop, whose branches and addresses depend on the SHAKE256 output, by relating
the two runs iteration by iteration (`body_ct`): both are at the same
iteration with the same `i` and byte `j` (being those of the same output), so
each branch goes the same way, and each piece between the branches is
constant time in registers that hold the same values in both runs.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Sample.Ball

open VG VG.PPC64LE
open VG.Proof.MlDsa.PPC64LE.Sample
open VG.Impl.MlDsa.PPC64LE.Sample
open VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.PPC64LE (relct_noMem)
open VG.Proof.MlKem.PPC64LE.Sample (taint_block relct_wp)
open VG.Spec.MlDsa (Zq q H IPoly n ofInt toRq)
open VG.Proof.MlDsa (coeffAt PolyIs)
open VG.Spec.Sha3 (bytesAt rates)

/-- Any code, by the taint analysis from the registers `rs`. -/
theorem taint_prog {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hsp : ∀ a b, P a b → a.sp = b.sp) (hP : ∀ a b, P a b → ∀ r ∈ rs, a.gpr r = b.gpr r)
    {hc : VG.Taint.Hint VG.PPC64LE.taint.T}
    (h : (VG.PPC64LE.taint.check (Taint.ofRegs rs) c hc).isSome = true) :
    RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := VG.PPC64LE.taint) (Taint.ofRegs rs)
    (fun a b hab => ⟨hsp a b hab, fun r hr => hP a b hab r (Taint.mem_ofRegs.mp hr)⟩) h

/-- `zx` depends only on the low 32 bits. -/
theorem zx_congr {x y : BitVec 64} (h : x.setWidth 32 = y.setWidth 32) : zx x = zx y :=
  BitVec.eq_of_toNat_eq (by rw [zx_toNat, zx_toNat, h])

/-- Two runs, from entry states that agree on the public data. -/
structure Two (σ₁ σ₂ : State) : Prop where
  p₁ : Pre σ₁
  p₂ : Pre σ₂
  sp : σ₁.sp = σ₂.sp
  r3 : σ₁.gpr .r3 = σ₂.gpr .r3
  r4 : σ₁.gpr .r4 = σ₂.gpr .r4
  r5 : (σ₁.gpr .r5).setWidth 32 = (σ₂.gpr .r5).setWidth 32
  r6 : σ₁.gpr .r6 = σ₂.gpr .r6
  r7 : σ₁.gpr .r7 = σ₂.gpr .r7
  B : B σ₁ = B σ₂

section
variable {σ₁ σ₂ : State} (two : Two σ₁ σ₂)
include two

theorem Two.P_eq : spOf σ₂ = spOf σ₁ := by simp only [spOf, two.r3, two.r4, two.r6, two.r7]
theorem Two.X_eq : X σ₁ = X σ₂ := by simp only [X, two.B]
theorem Two.tau_eq : tau σ₁ = tau σ₂ := by simp only [tau, two.r5]
theorem Two.St_eq (t : Nat) : St σ₁ t = St σ₂ t := by simp only [St, i0, two.X_eq, two.tau_eq]
theorem Two.Xb_eq (t : Nat) : Xb σ₁ t = Xb σ₂ t := by simp only [Xb, two.X_eq]

theorem Two.bsp {t t' : Nat} {a b : State} (ha : BAt σ₁ t a) (hb : BAt σ₂ t' b) : a.sp = b.sp := by
  rw [ha.env.sp, hb.env.sp, two.sp]

/-! ## The loop -/

theorem body_ct {t : Nat} (ht : t < 264) :
    RelCT isa (fun a b => BAt σ₁ t a ∧ BAt σ₂ t b) bBody fun a b =>
      (BAt σ₁ (t + 1) a ∧ (a.gpr .r6 != 0) = decide (t + 1 ≠ 264)) ∧
      (BAt σ₂ (t + 1) b ∧ (b.gpr .r6 != 0) = decide (t + 1 ≠ 264)) := by
  have hp₁ := two.p₁.ok
  have hp₂ := two.p₂.ok
  have hτ₁ : tau σ₁ ≤ 256 := by have := two.p₁.tau_le; omega_arith
  have hτ₂ : tau σ₂ ≤ 256 := by have := two.p₂.tau_le; omega_arith
  have eP := two.P_eq
  refine relct_wp ?_ fun a b hab => ⟨body_ok hp₁ hτ₁ ht hab.1, body_ok hp₂ hτ₂ ht hab.2⟩
  refine RelCT.seq (R := fun a b => M1 σ₁ t a ∧ M1 σ₂ t b) (relct_wp (relct_noMem rfl) fun a b hab =>
    ⟨pieceA hp₁ hab.1, pieceA hp₂ hab.2⟩) ?_
  refine RelCT.seq (R := fun _ _ => True) ?_ (relct_noMem rfl)
  refine RelCT.ite (fun a b h => by rw [eval_zero, eval_zero, h.1.z, h.2.z, two.St_eq]) (relct_noMem rfl) ?_
  have zb : ∀ {a b : State}, M1 σ₁ t a → M1 σ₂ t b → (a.gpr .r12 == 0) = false → (b.gpr .r12 == 0) = false :=
    fun ha hb e => by rw [hb.z, ← two.St_eq, ← ha.z]; exact e
  refine RelCT.seq (R := fun a b => T1 σ₁ t a ∧ T1 σ₂ t b) (relct_wp (taint_block [.r3]
      (fun a b h => two.bsp h.1.1.bat h.1.2.bat) (fun a b h r hr => by
        rw [List.mem_singleton] at hr; subst hr; rw [h.1.1.bat.r3, h.1.2.bat.r3, eP]) (by taint_decide))
    fun a b h => by
      have za : (a.gpr .r12 == 0) = false := by rw [eval_zero] at h; exact Option.some.inj h.2
      exact ⟨tryA hp₁ ht h.1.1 za, tryA hp₂ ht h.1.2 (zb h.1.1 h.1.2 za)⟩) ?_
  refine RelCT.ite (fun a b h => by rw [eval_zero, eval_zero, h.1.z, h.2.z, two.St_eq, two.Xb_eq]) ?_
    (relct_noMem rfl)
  refine taint_block [.r4, .r8, .r30] (fun a b h => two.bsp h.1.1.bat h.1.2.bat) (fun a b h r hr => ?_)
    (by taint_decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h.1.1.bat.r4, h.1.2.bat.r4, eP, two.St_eq]
  · rw [h.1.1.r8, h.1.2.r8, two.Xb_eq]
  · rw [h.1.1.bat.env.r30, h.1.2.bat.env.r30, eP]

theorem loop_ct :
    RelCT isa (fun a b => BAt σ₁ 0 a ∧ BAt σ₂ 0 b) (.loop bBody (.nonzero .d .r6)) fun a b =>
      BAt σ₁ 264 a ∧ BAt σ₂ 264 b := by
  refine RelCT.mono (RelCT.loop (M := isa) (body := bBody) (c := .nonzero .d .r6)
    (Q := fun a b => BAt σ₁ 264 a ∧ BAt σ₂ 264 b)
    (fun n a b => ∃ t, t < 264 ∧ n = 264 - t ∧ BAt σ₁ t a ∧ BAt σ₂ t b) (fun n => ?_) 264)
    (fun a b hab => ⟨0, by decide, rfl, hab⟩) (fun _ _ h => h)
  refine RelCT.mono (P := fun a b => ∃ t, t < 264 ∧ n = 264 - t ∧ BAt σ₁ t a ∧ BAt σ₂ t b)
    (RelCT.exists_ fun t => ?_) (fun _ _ hab => hab) (fun _ _ h => h)
  by_cases ht : t < 264
  · by_cases hn : n = 264 - t
    · refine RelCT.mono (P := fun a b => BAt σ₁ t a ∧ BAt σ₂ t b) (body_ct two ht) (fun _ _ hab => hab.2.2)
        fun a b ⟨⟨i₁, z₁⟩, ⟨i₂, z₂⟩⟩ => ⟨?_, fun e => ?_, fun e => ?_⟩
      · rw [eval_nonzero, eval_nonzero, z₁, z₂]
      · have : t + 1 = 264 := by
          have e' : (a.gpr .r6 != 0) = false := by rw [eval_nonzero] at e; exact Option.some.inj e
          rw [z₁] at e'; simpa using e'
        rw [this] at i₁ i₂; exact ⟨i₁, i₂⟩
      · have : t + 1 ≠ 264 := by
          have e' : (a.gpr .r6 != 0) = true := by rw [eval_nonzero] at e; exact Option.some.inj e
          rw [z₁] at e'; simpa using e'
        exact ⟨264 - (t + 1), by omega_arith, t + 1, by omega_arith, rfl, i₁, i₂⟩
    · exact RelCT.of_false fun _ _ hab => hn hab.2.1
  · exact RelCT.of_false fun _ _ hab => ht hab.1

/-! ## The whole function -/

theorem all_ct : RelCT isa (fun a b => a = σ₁ ∧ b = σ₂) Impl.MlDsa.PPC64LE.Sample.sampleInBall fun _ _ => True := by
  have hp₁ := two.p₁.ok
  have hp₂ := two.p₂.ok
  have eP := two.P_eq
  have hp₂' : SpOk (spOf σ₁) σ₂ := eP ▸ hp₂
  have hτ₁ : tau σ₁ ≤ 256 := by have := two.p₁.tau_le; omega_arith
  have hτ₂ : tau σ₂ ≤ 256 := by have := two.p₂.tau_le; omega_arith
  have ez := zx_congr two.r5
  -- the prologue
  refine RelCT.seq (R := fun (a b : State) => (J0 (spOf σ₁) σ₁ a ∧ a.gpr .r27 = zx (σ₁.gpr .r5)) ∧
      (J0 (spOf σ₁) σ₂ b ∧ b.gpr .r27 = zx (σ₂.gpr .r5))) (relct_wp (pro_ball_ct
    (fun a b hab => by rw [hab.1, hab.2]; exact two.sp) fun a b hab => by rw [hab.1, hab.2]; exact two.r7)
    fun a b hab => ⟨?_, ?_⟩) ?_
  · rw [hab.1]; exact pro_ball hp₁ rfl (by simp) rfl rfl
  · rw [hab.2]; exact pro_ball hp₂' two.r3.symm (by rw [← two.r4]; simp) two.r6.symm two.r7.symm
  -- the sponge
  refine RelCT.seq (R := fun (a b : State) => (∃ x, J6 136 272 (spOf σ₁) σ₁ x a ∧ x.gpr .r27 = zx (σ₁.gpr .r5)) ∧
      (∃ y, J6 136 272 (spOf σ₁) σ₂ y b ∧ y.gpr .r27 = zx (σ₂.gpr .r5)))
    (relct_wp (RelCT.mono (sponge_ct hp₁ hp₂' two.sp (by decide) (by decide)) (fun a b h => ⟨h.1.1, h.2.1⟩)
      fun _ _ h => h) fun a b hab =>
      ⟨WP.mono (sponge_ok hp₁ (by decide) (by decide) hab.1.1) fun _ x => ⟨_, x, hab.1.2⟩,
        WP.mono (sponge_ok hp₂' (by decide) (by decide) hab.2.1) fun _ x => ⟨_, x, hab.2.2⟩⟩) ?_
  -- the zeroing
  refine RelCT.seq (R := fun a b => ZDone σ₁ a ∧ ZDone σ₂ b) (relct_wp (taint_prog [.r30]
      (fun a b h => by
        obtain ⟨⟨x, ha, _⟩, ⟨y, hb, _⟩⟩ := h; rw [ha.j0.env.sp, hb.j0.env.sp, two.sp])
      (fun a b h r hr => by
        obtain ⟨⟨x, ha, _⟩, ⟨y, hb, _⟩⟩ := h
        rw [List.mem_singleton] at hr; subst hr; rw [ha.j0.env.r30, hb.j0.env.r30]) (by taint_decide))
    fun a b ⟨⟨x, ha, h₁⟩, ⟨y, hb, h₂⟩⟩ => ⟨zero_ok hp₁ ha h₁, zero_ok hp₂ (by rw [eP]; exact hb) h₂⟩) ?_
  -- the loop
  refine RelCT.seq (R := fun a b => BAt σ₁ 264 a ∧ BAt σ₂ 264 b) (RelCT.seq (R := fun a b => BAt σ₁ 0 a ∧ BAt σ₂ 0 b)
    (relct_wp (taint_block [.r27, .r30, .r31] (fun a b h => by rw [h.1.env.sp, h.2.env.sp, two.sp])
      (fun a b h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.1.r27, h.2.r27, ez]
        · rw [h.1.env.r30, h.2.env.r30, eP]
        · rw [h.1.env.r31, h.2.env.r31, eP]) (by taint_decide))
      fun a b h => ⟨setup_ok hp₁ hτ₁ h.1, setup_ok hp₂ hτ₂ h.2⟩) (loop_ct two)) ?_
  -- the end
  exact retEpi_ct (fun a b hab => two.bsp hab.1 hab.2) fun a b hab => by
    rw [hab.1.env.r31, hab.2.env.r31, eP]

end

/-! ## `Verified` -/

theorem pre_of {s : State} (h : (Proof.MlDsa.sampleInBallContract PPC64LE.abi 48).pre s) : Pre s := by
  sig_pre [Proof.MlDsa.sampleInBallContract, Proof.MlDsa.sampleInBallSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h0, h1, h2, d1, d2, d3, b1, b2, b3, f1, f2, f3, hb⟩ := h
  simp only [Proof.MlDsa.ballParams, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hb
  exact ⟨⟨by rw [h1]; exact List.mem_singleton_self _, h2, d1, d2, d3, b1, b2, b3, (s.gpr .r4).isLt, f2, f3, h0⟩,
    by simp only [tau]; omega_arith⟩

theorem post_of {s₀ s : State}
    (h3 : s.gpr .r3 = (if (ballFold (tau s₀) (X s₀)).2 = 256 then 1 else 0))
    (hc : (ballFold (tau s₀) (X s₀)).2 = 256 → PolyIs s.mem (s₀.gpr .r6) (toRq (ballFold (tau s₀) (X s₀)).1)) :
    (Proof.MlDsa.sampleInBallContract PPC64LE.abi 48).post s₀ s := by
  sig_post [Proof.MlDsa.sampleInBallContract, Proof.MlDsa.sampleInBallSig, PPC64LE.abi, PPC64LE.argRegs]
  rw [h3]
  by_cases hf : (ballFold (tau s₀) (X s₀)).2 = 256
  · rw [ifT hf]
    obtain ⟨hred, hpoly⟩ := hc hf
    exact ⟨fun _ => hred, .inl ⟨rfl, { Spec.MlDsa.minBounds with ball := 272 }, by
      show Option.map toRq (Spec.MlDsa.sampleInBall (tau s₀) 272 (B s₀)) =
        some (Proof.MlDsa.polyAt s.mem (s₀.gpr .r6))
      rw [sampleInBall_some _ (by decide) hf]
      exact congrArg some hpoly.symm⟩⟩
  · rw [ifF hf]
    exact ⟨fun h1 => absurd h1 (by decide), .inr ⟨rfl, by
      show Option.map toRq (Spec.MlDsa.sampleInBall (tau s₀) 221 (B s₀)) = none
      rw [sampleInBall_none _ (B := 272) (by decide) (by decide) hf]; rfl⟩⟩

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
    | .r3 => 0x1000 | .r4 => 32 | .r5 => 39 | .r6 => 0x2000 | .r7 => 0x3000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 32⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

end VG.Proof.MlDsa.PPC64LE.Sample.Ball

namespace VG.Proof.MlDsa.PPC64LE.Sample

open VG VG.PPC64LE
open Ball

theorem sampleInBall_verified :
    Verified PPC64LE.target Impl.MlDsa.PPC64LE.Sample.sampleInBall (Proof.MlDsa.sampleInBallContract PPC64LE.abi 48) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, h3, hc, hpres⟩ := correct (pre_of hs)
    exact ⟨t, s', he, hpres, post_of h3 hc⟩
  · sig_pub [Proof.MlDsa.sampleInBallContract, Proof.MlDsa.sampleInBallSig, PPC64LE.abi, PPC64LE.argRegs] at hpub
    obtain ⟨hsp, hb, h3, h4, h5, h6, h7⟩ := hpub
    exact (all_ct ⟨pre_of h₁, pre_of h₂, hsp, h3, h4, h5, h6, h7, leakBytes_inj hb⟩ s₁ s₂ t₁ t₂ s₁' s₂'
      ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.sampleInBallContract, Proof.MlDsa.sampleInBallSig, PPC64LE.abi, PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | decide +kernel

end VG.Proof.MlDsa.PPC64LE.Sample

end

end

/-!
# ML-DSA on PPC64LE: `vg_mldsa_norm_lt`

One symbolic execution of the loop body, for any pointer (`body_ok`), which
ands into `r9` the bit `ok a` (`ok_toNat`: 1 exactly when `a < bound` or
`q - a < bound`, `normZq_lt`); the invariant says `r9` is 1 exactly when
every coefficient so far is in bounds (`Inv`), and `normRq_lt` turns that
into the norm.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Round.NormLt

open VG VG.PPC64LE VG.Impl.MlDsa.PPC64LE.Round
open VG.Impl.MlDsa.PPC64LE.Arith (loadImm loadQ)
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Round (pR coeff_contains polyAt_val normZq_lt normRq_lt reduced_zero)
open VG.Proof.MlKem.PPC64LE (wp_loop_nz count_sub count_nz ptr_succ)

/-! ## Values -/

/-- The bit the body ands in, for the coefficient `a` and the bound `b`. -/
def ok (a b : BitVec 64) : BitVec 64 := (a - b) >>> 63 ||| (8380417 - a - b) >>> 63

theorem ok_toNat {a b : BitVec 64} (ha : a.toNat < q) (hb : b.toNat < 2 ^ 32) :
    ok a b = if a.toNat < b.toNat ∨ q - a.toNat < b.toNat then 1 else 0 := by
  rw [VG.Proof.MlDsa.Round.q_eq] at ha ⊢
  unfold ok
  split <;> rename_i h
  · rcases h with h | h
    · have : (a - b) >>> 63 = 1 := by bv_omega
      rw [this]
      have : (8380417 - a - b) >>> 63 = 0 ∨ (8380417 - a - b) >>> 63 = 1 := by bv_omega
      rcases this with e | e <;> rw [e] <;> decide
    · have : (8380417 - a - b) >>> 63 = 1 := by bv_omega
      rw [this]
      have : (a - b) >>> 63 = 0 ∨ (a - b) >>> 63 = 1 := by bv_omega
      rcases this with e | e <;> rw [e] <;> decide
  · have h1 : (a - b) >>> 63 = 0 := by bv_omega
    have h2 : (8380417 - a - b) >>> 63 = 0 := by bv_omega
    rw [h1, h2]; decide

/-! ## The loop body -/

section
variable {s : State} {x c v : BitVec 64} (h3 : s.gpr .r3 = x) (h5 : s.gpr .r5 = 8380417) (h9 : s.gpr .r9 = v)
  (h10 : s.gpr .r10 = c) (ia : InRegions (s.rd ++ s.wr) x 4)
include h3 h5 h9 h10 ia

theorem body_ok :
    WP isa (.block nlBody) s fun s' =>
      s'.gpr .r3 = x + 4 ∧ s'.gpr .r10 = c - 1 ∧ s'.gpr .r4 = s.gpr .r4 ∧ s'.gpr .r5 = 8380417 ∧
      s'.gpr .r9 = v &&& ok ((s.mem.readW x 32).setWidth 64) (s.gpr .r4) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.lr = s.lr ∧ ∀ r ∈ preserved, s'.gpr r = s.gpr r := by
  crun [nlBody, ok, h3, h5, h9, h10, ia, preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]
  simp [Mem.readW, Mem.read]

end

/-! ## The loop -/

section
variable (s₀ : State)

abbrev Fp : Addr := s₀.gpr .r3
abbrev B : BitVec 64 := (s₀.gpr .r4).setWidth 32 |>.setWidth 64

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [pR (Fp s₀)]
  wr : s₀.wr = []
  fit : (Fp s₀).toNat + 1024 ≤ 2 ^ 64
  red : Reduced s₀.mem (Fp s₀)

/-- All of the first `i` coefficients are in bounds. -/
def AllOk (s₀ : State) (i : Nat) : Prop :=
  ∀ j < i, normZq (polyAt s₀.mem (Fp s₀))[j]! < (B s₀).toNat

instance (s₀ : State) (i : Nat) : Decidable (AllOk s₀ i) := by unfold AllOk; infer_instance

/-- After `i` iterations. -/
structure Inv (s₀ : State) (i : Nat) (s : State) : Prop where
  r3 : s.gpr .r3 = Fp s₀ + BitVec.ofNat 64 (4 * i)
  r4 : s.gpr .r4 = B s₀
  r5 : s.gpr .r5 = 8380417
  r9 : s.gpr .r9 = if AllOk s₀ i then 1 else 0
  r10 : s.gpr .r10 = BitVec.ofNat 64 (256 - i)
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lr : s.lr = s₀.lr
  pres : ∀ r ∈ preserved, s.gpr r = s₀.gpr r

theorem ite_and_ite (a b : Prop) [Decidable a] [Decidable b] :
    ((if a then 1 else 0 : BitVec 64) &&& if b then 1 else 0) = if a ∧ b then 1 else 0 := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb]

theorem allOk_succ (s₀ : State) {i : Nat} (hi : i < 256) :
    AllOk s₀ (i + 1) ↔ AllOk s₀ i ∧ normZq (polyAt s₀.mem (Fp s₀))[i]! < (B s₀).toNat := by
  unfold AllOk
  constructor
  · intro h; exact ⟨fun j hj => h j (by omega_using [hj]), h i (by omega_using [])⟩
  · intro ⟨h, h'⟩ j hj
    by_cases e : j = i
    · subst e; exact h'
    · exact h j (by omega_using [hj, e])

theorem inv_step {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 256) {s : State} (h : Inv s₀ i s) :
    WP isa (.block nlBody) s fun s' => Inv s₀ (i + 1) s' ∧ (s'.gpr .r10 != 0) = decide (i + 1 ≠ 256) := by
  have cF := coeff_contains (Fp s₀) (i := i) hi
  refine WP.mono (body_ok h.r3 h.r5 h.r9 h.r10 (by rw [h.rd, h.wr, hp.rd, hp.wr]; exact ⟨_, by simp, cF⟩))
    fun s' ⟨r3, r10, r4, r5, r9, m, rd, wr, sp, lr, pres⟩ => ⟨⟨?_, r4.trans h.r4, r5, ?_, ?_, m.trans h.mem,
      rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, lr.trans h.lr, fun r hr => (pres r hr).trans (h.pres r hr)⟩, ?_⟩
  · rw [r3]; exact ptr_succ _ 4 i
  · have hv := polyAt_val hp.red (i := i) hi
    have ha : ((s.mem.readW (Fp s₀ + BitVec.ofNat 64 (4 * i)) 32).setWidth 64).toNat =
        ((polyAt s₀.mem (Fp s₀))[i]!).val := by
      rw [h.mem, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (coeffAt s₀.mem (Fp s₀) i).isLt; omega_using [])]
      exact hv.symm
    have hb : (s.gpr .r4).toNat < 2 ^ 32 := by
      rw [h.r4, B, BitVec.toNat_setWidth, BitVec.toNat_setWidth]
      exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.mod_lt _ (by decide))
    rw [r9, ok_toNat (by rw [ha]; exact Fin.isLt _) hb, ha, h.r4]
    have e := allOk_succ s₀ hi
    rw [normZq_lt] at e
    rw [ite_and_ite]
    by_cases hc : AllOk s₀ (i + 1)
    · rw [ite_eq_left hc, ite_eq_left (e.mp hc)]
    · rw [ite_eq_right hc, ite_eq_right (fun h' => hc (e.mpr h'))]
  · rw [r10]; exact count_sub hi
  · rw [r10, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub hi]; exact count_nz hi (by decide)

/-- The result, after the loop. -/
def Post (s₀ s : State) : Prop :=
  (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧ s.lr = s₀.lr ∧
    s.gpr .r3 = if AllOk s₀ 256 then 1 else 0

theorem exit_ok {s₀ s : State} (h : Inv s₀ 256 s) : WP isa (.block [.logic .or .r3 .r9 .r9]) s (Post s₀) := by
  refine WP.cons exec_logic (wp_nil ⟨?_, h.sp, h.lr, ?_⟩)
  · intro r hr
    have : ¬r = .r3 := by revert r hr; decide
    rw [RegUpd.gpr_write_of_ne _ _ this]; exact h.pres r hr
  · rw [RegUpd.gpr_write_self, BitVec.or_self]; exact h.r9

theorem correct {s₀ : State} (hp : Pre s₀) : WP isa normLt s₀ (Post s₀) := by
  refine WP.seq (WP.cons (exec_lsr_w (by decide)) (WP.cons (exec_li (by decide)) (WP.cons (exec_li (by decide))
    (WP.cons exec_lis (WP.cons exec_ori (wp_nil ?_))))))
  refine WP.seq (wp_loop_nz (Inv s₀) (N := 256) (by decide) (fun i hi s h => inv_step hp hi h)
    (fun s h => exit_ok h) ?_)
  refine ⟨by simp [State.write], by simp [State.write, B], ?_, ?_, by simp [State.write], rfl, rfl, rfl, rfl, rfl,
    fun r hr => ?_⟩
  · simp only [State.write, reduceCtorEq, ite_false, ite_true]
    exact VG.Proof.MlDsa.PPC64LE.Arith.loadImm_val (by decide)
  · have : AllOk s₀ 0 := fun j hj => absurd hj (Nat.not_lt_zero j)
    simp [State.write, this]
  · have : r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r9 ∧ r ≠ .r10 := by revert r hr; decide
    simp [State.write, this.1, this.2.1, this.2.2.1, this.2.2.2]

/-! ## Verified -/

theorem pre_of {s : State} (h : (Proof.MlDsa.normLtContract PPC64LE.abi).pre s) : Pre s := by
  sig_pre [Proof.MlDsa.normLtContract, Proof.MlDsa.normLtSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := []

theorem verified : Verified PPC64LE.target normLt (Proof.MlDsa.normLtContract PPC64LE.abi) := by
  refine ⟨fun s hs => ?_, VG.Proof.MlKem.PPC64LE.Add.ctRegs [.r3] (fun s₁ s₂ h => ?_)
    (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · have hp := pre_of hs
    obtain ⟨t, s', he, h⟩ := correct hp
    refine ⟨t, s', he, ⟨h.1, h.2.1, h.2.2.1⟩, ?_⟩
    sig_post [Proof.MlDsa.normLtContract, Proof.MlDsa.normLtSig, PPC64LE.abi, PPC64LE.argRegs]
    rw [h.2.2.2]
    have e : AllOk s 256 ↔ normRq [polyAt s.mem (Fp s)] < (B s).toNat := by
      rw [normRq_lt]; rfl
    have eb : (B s).toNat = ((s.gpr .r4).setWidth 32).toNat := by
      simp only [B, BitVec.toNat_setWidth]
      exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))
    rw [eb] at e
    by_cases hc : AllOk s 256
    · rw [ite_eq_left hc, ite_eq_left (e.mp hc)]; rfl
    · rw [ite_eq_right hc, ite_eq_right (fun h' => hc (e.mpr h'))]; rfl
  · sig_pub [Proof.MlDsa.normLtContract, Proof.MlDsa.normLtSig, PPC64LE.abi, PPC64LE.argRegs] at h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact h.2.1
  · sig_pub [Proof.MlDsa.normLtContract, Proof.MlDsa.normLtSig, PPC64LE.abi, PPC64LE.argRegs] at h
    exact h.1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.normLtContract, Proof.MlDsa.normLtSig, PPC64LE.abi, PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _
        | decide +kernel

end VG.Proof.MlDsa.PPC64LE.Round.NormLt
