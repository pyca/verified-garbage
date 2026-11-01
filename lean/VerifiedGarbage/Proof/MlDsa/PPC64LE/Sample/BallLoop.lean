module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.Pro
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Sample.Ball
public import VerifiedGarbage.Proof.MlDsa.Sample.ExpandMask
import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# ML-DSA on PPC64LE: the loops of `vg_mldsa_sample_in_ball`

As on 32-bit ARM (`Proof/MlDsa/Arm/Sample/BallLoop.lean`). A call is
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
