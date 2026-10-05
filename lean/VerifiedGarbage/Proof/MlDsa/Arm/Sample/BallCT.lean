import VerifiedGarbage.Proof.MlDsa.Arm.Sample.ExpandMask
import VerifiedGarbage.Impl.MlDsa.Arm.Sample.Ball
import VerifiedGarbage.Proof.MlDsa.Sample.Signs

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Sample.BallLoop`. -/
section

/-!
# ML-DSA on 32-bit ARM: the loops of `vg_mldsa_sample_in_ball`

A call is described by `spOf σ` (`c̃`, its length, `scratch`, `c` and `τ`),
and the XOF output is `X σ`, `H(c̃, 272)`. The polynomial `c` is kept in
memory as the words that represent its coefficients modulo `q` (`CStored`);
the first loop zeroes it (`zero_ok`). Iteration `t` of the second starts from
`BAt σ t`: with the polynomial and `i` (in `r2`) that `bFold` computes from
the first `t` bytes after the sign bits, and the sign bits not yet used in
`r1` (low word) and `r4` (high word), whose value `r1 + 2³² r4` is that of the
first 8 bytes shifted right once per coefficient set (`Sg`). The pieces of an
iteration are `pieceA` (`i ≥ 256`?), `tryA` (the byte `j`, and `j ≤ i`?),
`setOk` (`c[i] ← c[j]`, `c[j] ← ±1`) and `pieceC` (the step).
-/

namespace VG.Proof.MlDsa.Arm.Sample.Ball

open VG VG.Arm
open VG.Proof.MlKem.Arm
open VG.Proof.MlDsa.Arm.Sample
open VG.Impl.MlDsa.Arm.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q H IPoly n ofInt coeffAt)
open VG.Spec.Sha3 (bytesAt)

/-- The call, from the entry state: `ctilde = r0`, `len = r1`, `tau = r2`,
`c = r3` and `scratch` on the stack. -/
abbrev spOf (σ : State) : Sp := ⟨σ.gpr .r0, (σ.gpr .r1).toNat, stackArg σ 0, σ.gpr .r3, σ.gpr .r2⟩

/-- `τ`. -/
abbrev tau (σ : State) : Nat := (σ.gpr .r2).toNat

/-- `c̃`. -/
abbrev B (σ : State) : List Byte := bytesAt σ.mem (State.addr (σ.gpr .r0)) (σ.gpr .r1).toNat

/-- The XOF output. -/
abbrev X (σ : State) : List Byte := VG.Spec.MlDsa.H (VG.Proof.MlDsa.Arm.Sample.Ball.B σ) 272

/-- The first `i`. -/
abbrev i0 (σ : State) : Nat := 256 - VG.Proof.MlDsa.Arm.Sample.Ball.tau σ

/-- The sign bits, as a number. -/
abbrev Wn (σ : State) : Nat := leNat ((VG.Proof.MlDsa.Arm.Sample.Ball.X σ).take 8)

/-- The polynomial and `i` after `t` iterations. -/
abbrev St (σ : State) (t : Nat) : IPoly × Nat :=
  bFold (VG.Proof.MlDsa.Arm.Sample.Ball.tau σ) (signs (VG.Proof.MlDsa.Arm.Sample.Ball.X σ)) (Vector.replicate n 0, VG.Proof.MlDsa.Arm.Sample.Ball.i0 σ) (((VG.Proof.MlDsa.Arm.Sample.Ball.X σ).drop 8).take t)

/-- The polynomial `c` of `R` is stored at `p`, as elements of `ℤ_q`. -/
def CStored (m : Mem) (p : Addr) (c : IPoly) : Prop := ∀ k < 256, coeffAt m p k = zw (ofInt c[k]!)

/-- What the proofs need of the entry state. -/
structure Pre (σ : State) : Prop where
  ok : SpOk (VG.Proof.MlDsa.Arm.Sample.Ball.spOf σ) σ
  arg : InRegions (σ.rd ++ σ.wr) (stackArgAddr σ 0) 4
  tau_ge : 39 ≤ VG.Proof.MlDsa.Arm.Sample.Ball.tau σ
  tau_le : VG.Proof.MlDsa.Arm.Sample.Ball.tau σ ≤ 60

theorem X_length (σ : State) : (VG.Proof.MlDsa.Arm.Sample.Ball.X σ).length = 272 := VG.Proof.MlDsa.Sample.H_length _ _

theorem St_le (σ : State) (t : Nat) : (VG.Proof.MlDsa.Arm.Sample.Ball.St σ t).2 ≤ 256 := bFold_le (by simp) _

theorem St_ge (σ : State) (t : Nat) : VG.Proof.MlDsa.Arm.Sample.Ball.i0 σ ≤ (VG.Proof.MlDsa.Arm.Sample.Ball.St σ t).2 :=
  bFold_ge (τ := VG.Proof.MlDsa.Arm.Sample.Ball.tau σ) (h := signs (VG.Proof.MlDsa.Arm.Sample.Ball.X σ)) (Vector.replicate n 0, VG.Proof.MlDsa.Arm.Sample.Ball.i0 σ) _

/-- The sign bits not yet used, from their value. -/
abbrev Sg (σ : State) (i : Nat) (s : State) : Prop :=
  (s.gpr .r1).toNat + 2 ^ 32 * (s.gpr .r4).toNat = VG.Proof.MlDsa.Arm.Sample.Ball.Wn σ / 2 ^ (i - VG.Proof.MlDsa.Arm.Sample.Ball.i0 σ)

/-! ## Zeroing -/

/-- After `k` iterations of the zeroing loop. -/
structure ZAt (σ : State) (k : Nat) (s : State) : Prop where
  env : Env (VG.Proof.MlDsa.Arm.Sample.Ball.spOf σ) σ s
  r7 : s.gpr .r7 = σ.gpr .r2
  out : bytesAt s.mem ((VG.Proof.MlDsa.Arm.Sample.Ball.spOf σ).at' 840) 272 = VG.Proof.MlDsa.Arm.Sample.Ball.X σ
  r12 : s.gpr .r12 = 0
  r0 : s.gpr .r0 = σ.gpr .r3 + BitVec.ofNat 32 (4 * k)
  r3 : s.gpr .r3 = BitVec.ofNat 32 (1 * (256 - k))
  zero : ∀ j < k, coeffAt s.mem (VG.Proof.MlDsa.Arm.Sample.Ball.spOf σ).A j = 0

/-- After the zeroing. -/
structure ZDone (σ : State) (s : State) : Prop where
  env : Env (VG.Proof.MlDsa.Arm.Sample.Ball.spOf σ) σ s
  r7 : s.gpr .r7 = σ.gpr .r2
  out : bytesAt s.mem ((VG.Proof.MlDsa.Arm.Sample.Ball.spOf σ).at' 840) 272 = VG.Proof.MlDsa.Arm.Sample.Ball.X σ
  st : VG.Proof.MlDsa.Arm.Sample.Ball.CStored s.mem (VG.Proof.MlDsa.Arm.Sample.Ball.spOf σ).A (Vector.replicate n 0)

theorem zInit_ok (s : State) :
    WP isa (.block [.mov .r12 (.imm 0), .mov .r0 (.reg .r5), .mov .r3 (.imm 256)]) s fun s' =>
      s'.gpr .r12 = 0 ∧ s'.gpr .r0 = s.gpr .r5 ∧ s'.gpr .r3 = BitVec.ofNat 32 256 ∧
        (∀ r, r ≠ .r12 → r ≠ .r0 → r ≠ .r3 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [and_self, and_true, true_and]
  exact fun r h12 h0 h3 => by simp [h12, h0, h3]

theorem zStep_ok (s : State) {a : Addr} (ha : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = a)
    (hw : InRegions s.wr a 4) :
    WP isa (.block [.str .r12 .r0 0, .dp .add .r0 .r0 (.imm 4), .subs .r3 .r3 (.imm 1)]) s fun s' =>
      s'.mem = s.mem.writeW a (s.gpr .r12) ∧ s'.gpr .r0 = s.gpr .r0 + BitVec.ofNat 32 4 ∧
        s'.gpr .r3 = s.gpr .r3 - BitVec.ofNat 32 1 ∧ s'.z = (s.gpr .r3 - BitVec.ofNat 32 1 == 0) ∧
        (∀ r, r ≠ .r0 → r ≠ .r3 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [ha, hw, and_self, and_true, true_and]
  refine ⟨rfl, rfl, rfl, fun r h0 h3 => ?_⟩
  simp [h0, h3]

section
variable {σ : State} (hp : SpOk (VG.Proof.MlDsa.Arm.Sample.Ball.spOf σ) σ)
include hp

theorem zBody_ok {k : Nat} (hk : k < 256) {s : State} (h : VG.Proof.MlDsa.Arm.Sample.Ball.ZAt σ k s) :
    WP isa (.block [.str .r12 .r0 0, .dp .add .r0 .r0 (.imm 4), .subs .r3 .r3 (.imm 1)]) s fun s' =>
      VG.Proof.MlDsa.Arm.Sample.Ball.ZAt σ (k + 1) s' ∧ s'.z = decide (k + 1 = 256) := by
  have ea : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = VG.Proof.MlDsa.Sample.coeffAddr (VG.Proof.MlDsa.Arm.Sample.Ball.spOf σ).A k := by
    rw [h.r0]; exact addr_coeff hp.fa (by omega) hk
  have hin : InRegions s.wr (VG.Proof.MlDsa.Sample.coeffAddr (VG.Proof.MlDsa.Arm.Sample.Ball.spOf σ).A k) 4 := by
    rw [h.env.wr, hp.wr]; exact ⟨(VG.Proof.MlDsa.Arm.Sample.Ball.spOf σ).aR, by simp, VG.Proof.MlDsa.Sample.coeff_contains _ hk⟩
  refine WP.mono (VG.Proof.MlDsa.Arm.Sample.Ball.zStep_ok s ea hin) fun s' ⟨m, r0, r3, z, g, rd, wr, sp⟩ => ?_
  have hf : Frame [(VG.Proof.MlDsa.Arm.Sample.Ball.spOf σ).aR] s.mem s'.mem := by
    rw [m]; exact (Frame.refl _ _).writeW (by simp) _ (VG.Proof.MlDsa.Sample.coeff_contains _ hk)
  refine ⟨⟨h.env.step hp hf (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact .inr (.inl fun _ h => h))
    (g _ (by decide) (by decide)) (g _ (by decide) (by decide)) rd wr sp,
    by rw [g _ (by decide) (by decide)]; exact h.r7, ?_, by rw [g _ (by decide) (by decide)]; exact h.r12,
    by rw [r0, h.r0, ptr_add_add32, Nat.mul_succ], by rw [r3, h.r3]; exact count_sub (k := 1) hk, fun j hj => ?_⟩,
    by rw [z, h.r3]; exact count_z (k := 1) hk (by decide) (by decide)⟩
  · rw [MlKem.bytesAt_frame hf (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact (hp.a_scr.sub_right (sub_scr (a := 840) (n := 272) (by omega))).symm) (by omega)]
    exact h.out
  · rw [m, VG.Proof.MlDsa.Sample.coeffAt_writeW _ _ (by omega) hk, h.r12]
    by_cases e : k = j
    · rw [ifT e]
    · rw [ifF e]; exact h.zero j (by omega)

/-- The zeroing loop, from what the sponge leaves. -/
theorem zero_ok {s : State} (h : J6 136 272 (VG.Proof.MlDsa.Arm.Sample.Ball.spOf σ) σ s) : WP isa bZero s (VG.Proof.MlDsa.Arm.Sample.Ball.ZDone σ) := by
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sample.Ball.zInit_ok s) fun s1 ⟨r12, r0, r3, g, m, rd, wr, sp⟩ => ?_)
  refine wp_loop_ne (VG.Proof.MlDsa.Arm.Sample.Ball.ZAt σ) (N := 256) (by decide) (fun k hk s h => VG.Proof.MlDsa.Arm.Sample.Ball.zBody_ok hp hk h)
    (fun s h => ⟨h.env, h.r7, h.out, fun k hk => ?_⟩) ⟨h.env.same m (g _ (by decide) (by decide) (by decide))
      (g _ (by decide) (by decide) (by decide)) rd wr sp, by rw [g _ (by decide) (by decide) (by decide), h.r7],
      by rw [m, h.out]; exact (VG.Proof.MlDsa.Sample.H_eq _ _).symm, r12, by rw [r0, h.env.r5]; simp, r3,
      fun _ h => absurd h (Nat.not_lt_zero _)⟩
  rw [h.zero k hk, getElem!_pos _ k (by simp only [n]; omega), Vector.getElem_replicate]
  rfl

end

/-! ## Setting a coefficient -/

/-- The word of the sign: 1, or `q - 1` for -1. -/
theorem sgn_word (b : Bool) :
    (if b then (BitVec.ofNat 32 8380416) else 1) = zw (ofInt (if b then -1 else 1)) := by
  cases b <;> decide

/-- `r1 & 1`, compared with zero. -/
theorem and1_beq (x : BitVec 32) : ((x &&& 1) - 0 == 0) = decide (x.toNat % 2 = 0) := by
  have h1 : (x &&& 1).toNat = x.toNat % 2 := by
    rw [BitVec.toNat_and, show (1 : BitVec 32).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  rw [show (x &&& 1) - 0 = x &&& 1 from BitVec.sub_zero _]
  by_cases h : x.toNat % 2 = 0
  · rw [decide_eq_true h, beq_iff_eq]; exact BitVec.eq_of_toNat_eq (by rw [h1, h]; rfl)
  · rw [decide_eq_false h, beq_eq_false_iff_ne]
    intro e; have := congrArg BitVec.toNat e; rw [h1] at this; exact h this

/-- The sign bits shifted right by one, from `r4:r1`. -/
theorem shr_or (x y : BitVec 32) :
    (x >>> 1 ||| y <<< 31).toNat = x.toNat / 2 + 2 ^ 31 * (y.toNat % 2) := by
  have hx : (x >>> 1).toNat = x.toNat / 2 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hy : (y <<< 31).toNat = 2 ^ 31 * (y.toNat % 2) := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  rw [BitVec.toNat_or, hx, hy, Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt (by have := x.isLt; omega), Nat.add_comm]

theorem bSet1_ok (s : State) {A B : Addr} (hA : State.addr (s.gpr .r5 + s.gpr .r8 <<< 2 + BitVec.ofNat 32 0) = A)
    (hB : State.addr (s.gpr .r5 + s.gpr .r2 <<< 2 + BitVec.ofNat 32 0) = B)
    (hr : InRegions (s.rd ++ s.wr) A 4) (hw : InRegions s.wr B 4) :
    WP isa (.block [.dp .add .r10 .r5 (.shifted .r8 .lsl 2), .ldr .r11 .r10 0,
      .dp .add .r12 .r5 (.shifted .r2 .lsl 2), .str .r11 .r12 0, .dp .and .r11 .r1 (.imm 1), .cmp .r11 (.imm 0)]) s
      fun s' => s'.mem = s.mem.writeW B (s.mem.readW A 32) ∧ s'.gpr .r10 = s.gpr .r5 + s.gpr .r8 <<< 2 ∧
        s'.z = decide ((s.gpr .r1).toNat % 2 = 0) ∧
        (∀ r, r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        s'.sp = s.sp := by
  have hA' : State.addr (s.gpr .r5 + s.gpr .r8 <<< 2 + 0) = A := hA
  have hB' : State.addr (s.gpr .r5 + s.gpr .r2 <<< 2 + 0) = B := hB
  run_block [hA, hB, hA', hB', hr, hw, VG.Proof.MlDsa.Arm.Sample.Ball.and1_beq, and_self, and_true, true_and]
  exact fun r h10 h11 h12 => by simp [h10, h11, h12]

/-- The word of the sign, from `Z` = the sign bit is 0. -/
theorem bSign_ok (s : State) (b : Bool) (hz : s.z = !b) :
    WP isa (.ite .eq (.block [.mov .r11 (.imm 1)]) (.block [.movw .r11 0xE000, .movt .r11 0x7F])) s fun s' =>
      s'.gpr .r11 = (if b then (BitVec.ofNat 32 8380416) else 1) ∧ (∀ r, r ≠ .r11 → s'.gpr r = s.gpr r) ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine WP.ite s.z rfl (fun e => ?_) (fun e => ?_)
  · have hb : b = false := by rw [hz] at e; simpa using e
    subst hb
    run_block [and_self, and_true, true_and]
    exact fun r h => by simp [h]
  · have hb : b = true := by rw [hz] at e; simpa using e
    subst hb
    run_block [and_self, and_true, true_and]
    exact fun r h => by simp [h]

theorem bSet3_ok (s : State) {A : Addr} (hA : State.addr (s.gpr .r10 + BitVec.ofNat 32 0) = A)
    (hw : InRegions s.wr A 4) :
    WP isa (.block [.str .r11 .r10 0, .mov .r1 (.shifted .r1 .lsr 1), .dp .orr .r1 .r1 (.shifted .r4 .lsl 31),
        .mov .r4 (.shifted .r4 .lsr 1), .dp .add .r2 .r2 (.imm 1)]) s fun s' =>
      s'.mem = s.mem.writeW A (s.gpr .r11) ∧ s'.gpr .r1 = s.gpr .r1 >>> 1 ||| s.gpr .r4 <<< 31 ∧
        s'.gpr .r4 = s.gpr .r4 >>> 1 ∧ s'.gpr .r2 = s.gpr .r2 + 1 ∧
        (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r4 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        s'.sp = s.sp := by
  run_block [hA, hw, and_self, and_true, true_and]
  exact fun r h1 h2 h4 => by simp [h1, h2, h4]

/-! ## An iteration -/

/-- Byte `t` after the sign bits. -/
abbrev Xb (σ : State) (t : Nat) : Byte := (VG.Proof.MlDsa.Arm.Sample.Ball.X σ).getD (8 + t) 0

theorem take_succ' (L : List Byte) {i : Nat} (h : i < L.length) : L.take (i + 1) = L.take i ++ [L.getD i 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem St_succ (σ : State) {t : Nat} (ht : t < 264) :
    VG.Proof.MlDsa.Arm.Sample.Ball.St σ (t + 1) = bStep (VG.Proof.MlDsa.Arm.Sample.Ball.tau σ) (signs (VG.Proof.MlDsa.Arm.Sample.Ball.X σ)) (VG.Proof.MlDsa.Arm.Sample.Ball.St σ t) (VG.Proof.MlDsa.Arm.Sample.Ball.Xb σ t) := by
  simp only [VG.Proof.MlDsa.Arm.Sample.Ball.St]
  rw [VG.Proof.MlDsa.Arm.Sample.Ball.take_succ' _ (by rw [List.length_drop, VG.Proof.MlDsa.Arm.Sample.Ball.X_length]; omega), bFold_snoc, List.getD_eq_getElem?_getD,
    List.getElem?_drop, ← List.getD_eq_getElem?_getD]

/-- At the start of iteration `t`. -/
structure BAt (σ : State) (t : Nat) (s : State) : Prop where
  env : Env (VG.Proof.MlDsa.Arm.Sample.Ball.spOf σ) σ s
  out : bytesAt s.mem ((VG.Proof.MlDsa.Arm.Sample.Ball.spOf σ).at' 840) 272 = VG.Proof.MlDsa.Arm.Sample.Ball.X σ
  r0 : s.gpr .r0 = stackArg σ 0 + BitVec.ofNat 32 (848 + t)
  r2 : s.gpr .r2 = BitVec.ofNat 32 (VG.Proof.MlDsa.Arm.Sample.Ball.St σ t).2
  sg : VG.Proof.MlDsa.Arm.Sample.Ball.Sg σ (VG.Proof.MlDsa.Arm.Sample.Ball.St σ t).2 s
  r3 : s.gpr .r3 = BitVec.ofNat 32 (1 * (264 - t))
  st : VG.Proof.MlDsa.Arm.Sample.Ball.CStored s.mem (VG.Proof.MlDsa.Arm.Sample.Ball.spOf σ).A (VG.Proof.MlDsa.Arm.Sample.Ball.St σ t).1

/-- `BAt` after code that writes no memory and keeps `r0`–`r6`. -/
theorem BAt.same {σ s s' : State} {t : Nat} (h : VG.Proof.MlDsa.Arm.Sample.Ball.BAt σ t s) (hm : s'.mem = s.mem)
    (g : ∀ r ∈ [Reg.r0, .r1, .r2, .r3, .r4, .r5, .r6], s'.gpr r = s.gpr r) (rd : s'.rd = s.rd)
    (wr : s'.wr = s.wr) (sp : s'.sp = s.sp) : VG.Proof.MlDsa.Arm.Sample.Ball.BAt σ t s' :=
  ⟨h.env.same hm (g .r5 (by simp)) (g .r6 (by simp)) rd wr sp, by rw [hm]; exact h.out,
    (g .r0 (by simp)).trans h.r0, (g .r2 (by simp)).trans h.r2,
    by show _ = _; rw [g .r1 (by simp), g .r4 (by simp)]; exact h.sg, (g .r3 (by simp)).trans h.r3,
    by rw [hm]; exact h.st⟩

/-- After the test of `i`. -/
structure M1 (σ : State) (t : Nat) (s : State) : Prop where
  bat : VG.Proof.MlDsa.Arm.Sample.Ball.BAt σ t s
  z : s.z = decide (256 ≤ (VG.Proof.MlDsa.Arm.Sample.Ball.St σ t).2)

/-- After the test of the byte `j`, if `i < 256`. -/
structure T1 (σ : State) (t : Nat) (s : State) : Prop where
  bat : VG.Proof.MlDsa.Arm.Sample.Ball.BAt σ t s
  lt : (VG.Proof.MlDsa.Arm.Sample.Ball.St σ t).2 < 256
  r8 : s.gpr .r8 = BitVec.ofNat 32 (VG.Proof.MlDsa.Arm.Sample.Ball.Xb σ t).toNat
  z : s.z = decide ((VG.Proof.MlDsa.Arm.Sample.Ball.Xb σ t).toNat ≤ (VG.Proof.MlDsa.Arm.Sample.Ball.St σ t).2)

/-- After the coefficients of iteration `t`. -/
structure M2 (σ : State) (t : Nat) (s : State) : Prop where
  env : Env (VG.Proof.MlDsa.Arm.Sample.Ball.spOf σ) σ s
  out : bytesAt s.mem ((VG.Proof.MlDsa.Arm.Sample.Ball.spOf σ).at' 840) 272 = VG.Proof.MlDsa.Arm.Sample.Ball.X σ
  r0 : s.gpr .r0 = stackArg σ 0 + BitVec.ofNat 32 (848 + t)
  r2 : s.gpr .r2 = BitVec.ofNat 32 (VG.Proof.MlDsa.Arm.Sample.Ball.St σ (t + 1)).2
  sg : VG.Proof.MlDsa.Arm.Sample.Ball.Sg σ (VG.Proof.MlDsa.Arm.Sample.Ball.St σ (t + 1)).2 s
  r3 : s.gpr .r3 = BitVec.ofNat 32 (1 * (264 - t))
  st : VG.Proof.MlDsa.Arm.Sample.Ball.CStored s.mem (VG.Proof.MlDsa.Arm.Sample.Ball.spOf σ).A (VG.Proof.MlDsa.Arm.Sample.Ball.St σ (t + 1)).1

theorem pieceA {σ : State} {t : Nat} {s : State} (h : VG.Proof.MlDsa.Arm.Sample.Ball.BAt σ t s) : WP isa (.block jFull) s (VG.Proof.MlDsa.Arm.Sample.Ball.M1 σ t) :=
  WP.mono (jFull_ok s h.r2 (by have := VG.Proof.MlDsa.Arm.Sample.Ball.St_le σ t; omega)) fun _ ⟨z, g, m, rd, wr, sp⟩ =>
    ⟨h.same m (fun r hr => g r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
      rd wr sp, z⟩

theorem ldrb_ok (s : State) {A : Addr} (ha : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = A)
    (hr : InRegions (s.rd ++ s.wr) A 1) :
    WP isa (.block [.ldrb .r8 .r0 0]) s fun s' => s'.gpr .r8 = BitVec.ofNat 32 (s.mem A).toNat ∧
      (∀ r, r ≠ .r8 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [ha, hr, and_self, and_true, true_and]
  refine ⟨BitVec.eq_of_toNat_eq ?_, fun r h => by simp [h]⟩
  rw [setWidth32_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (s.mem A).isLt; omega)]

section
variable {σ : State} (hp : SpOk (VG.Proof.MlDsa.Arm.Sample.Ball.spOf σ) σ)
include hp

theorem tryA {t : Nat} (ht : t < 264) {s : State} (h : VG.Proof.MlDsa.Arm.Sample.Ball.M1 σ t s) (hz : s.z = false) :
    WP isa (.block [.ldrb .r8 .r0 0, .dp .sub .r11 .r2 (.reg .r8), .mov .r11 (.shifted .r11 .lsr 31),
      .cmp .r11 (.imm 0)]) s (VG.Proof.MlDsa.Arm.Sample.Ball.T1 σ t) := by
  have hl : (VG.Proof.MlDsa.Arm.Sample.Ball.St σ t).2 < 256 := by
    have := h.z; rw [hz] at this; simp at this; omega
  have l := h.bat
  have ea : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = (VG.Proof.MlDsa.Arm.Sample.Ball.spOf σ).at' (840 + (8 + t)) := by
    rw [l.r0, ptr_add_add32, show 848 + t + 0 = 840 + (8 + t) by omega]; exact at_eq hp (by omega)
  have hb : s.mem ((VG.Proof.MlDsa.Arm.Sample.Ball.spOf σ).at' (840 + (8 + t))) = VG.Proof.MlDsa.Arm.Sample.Ball.Xb σ t := by
    have := congrArg (fun L => L.getD (8 + t) 0) l.out
    rw [MlKem.bytesAt_getD _ _ (by omega), add_ofNat_add] at this
    exact this
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.Arm.Sample.Ball.ldrb_ok s ea (inScrRd hp l.env (by omega))) fun s1 ⟨g8, g1, m1, rd1, wr1, sp1⟩ => ?_
  rw [hb] at g8
  have l1 : VG.Proof.MlDsa.Arm.Sample.Ball.BAt σ t s1 := l.same m1 (fun r hr => g1 r (by
    simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) rd1 wr1 sp1
  have hj := (VG.Proof.MlDsa.Arm.Sample.Ball.Xb σ t).isLt
  refine WP.mono (sgn_ok s1 .r2 (.reg .r8) (y := BitVec.ofNat 32 (VG.Proof.MlDsa.Arm.Sample.Ball.Xb σ t).toNat) (by simp [Op2.eval, g8])
    (by rw [l1.r2, toNat_ofNat32 (by omega)]; omega) (by rw [toNat_ofNat32 (by omega)]; omega))
    fun s2 ⟨z2, g2, m2, rd2, wr2, sp2⟩ => ⟨l1.same m2 (fun r hr => g2 r (by
      simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) rd2 wr2 sp2, hl,
      by rw [g2 _ (by decide), g8], ?_⟩
  rw [z2, l1.r2, toNat_ofNat32 (by omega), toNat_ofNat32 (by omega)]

omit hp in
/-- The sign bit of `i`, from the sign bits not yet used. -/
theorem sign_bit {i : Nat} (hτ : VG.Proof.MlDsa.Arm.Sample.Ball.tau σ ≤ 256) (hi0 : VG.Proof.MlDsa.Arm.Sample.Ball.i0 σ ≤ i) {s : State} (hs : VG.Proof.MlDsa.Arm.Sample.Ball.Sg σ i s) :
    decide ((s.gpr .r1).toNat % 2 = 0) = !(signs (VG.Proof.MlDsa.Arm.Sample.Ball.X σ)).getD (i + VG.Proof.MlDsa.Arm.Sample.Ball.tau σ - 256) false := by
  have hs' : (s.gpr .r1).toNat + 2 ^ 32 * (s.gpr .r4).toNat = VG.Proof.MlDsa.Arm.Sample.Ball.Wn σ / 2 ^ (i - VG.Proof.MlDsa.Arm.Sample.Ball.i0 σ) := hs
  have e0 : VG.Proof.MlDsa.Arm.Sample.Ball.i0 σ = 256 - VG.Proof.MlDsa.Arm.Sample.Ball.tau σ := rfl
  rw [signs_getD, testBit_eq, show i + VG.Proof.MlDsa.Arm.Sample.Ball.tau σ - 256 = i - VG.Proof.MlDsa.Arm.Sample.Ball.i0 σ by omega]
  have e : (s.gpr .r1).toNat % 2 = VG.Proof.MlDsa.Arm.Sample.Ball.Wn σ / 2 ^ (i - VG.Proof.MlDsa.Arm.Sample.Ball.i0 σ) % 2 := by rw [← hs']; omega
  rw [e]
  by_cases h : VG.Proof.MlDsa.Arm.Sample.Ball.Wn σ / 2 ^ (i - VG.Proof.MlDsa.Arm.Sample.Ball.i0 σ) % 2 = 1
  · rw [decide_eq_false (by omega), decide_eq_true h]; rfl
  · rw [decide_eq_true (by omega), decide_eq_false h]; rfl

omit hp in
theorem sg_succ {i : Nat} (hi0 : VG.Proof.MlDsa.Arm.Sample.Ball.i0 σ ≤ i) {s s' : State} (hs : VG.Proof.MlDsa.Arm.Sample.Ball.Sg σ i s)
    (g1 : s'.gpr .r1 = s.gpr .r1 >>> 1 ||| s.gpr .r4 <<< 31) (g4 : s'.gpr .r4 = s.gpr .r4 >>> 1) :
    VG.Proof.MlDsa.Arm.Sample.Ball.Sg σ (i + 1) s' := by
  have hs' : (s.gpr .r1).toNat + 2 ^ 32 * (s.gpr .r4).toNat = VG.Proof.MlDsa.Arm.Sample.Ball.Wn σ / 2 ^ (i - VG.Proof.MlDsa.Arm.Sample.Ball.i0 σ) := hs
  show _ = _
  rw [g1, g4, VG.Proof.MlDsa.Arm.Sample.Ball.shr_or, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, show i + 1 - VG.Proof.MlDsa.Arm.Sample.Ball.i0 σ = i - VG.Proof.MlDsa.Arm.Sample.Ball.i0 σ + 1 by omega,
    Nat.pow_succ 2 (i - VG.Proof.MlDsa.Arm.Sample.Ball.i0 σ), ← Nat.div_div_eq_div_mul, ← hs']
  omega

/-- `c[i] ← c[j]`, `c[j] ← ±1`, `i` incremented. -/
theorem setOk (hτ : VG.Proof.MlDsa.Arm.Sample.Ball.tau σ ≤ 256) {t : Nat} (ht : t < 264) {s : State} (h : VG.Proof.MlDsa.Arm.Sample.Ball.T1 σ t s) (hz : s.z = true) :
    WP isa bSet s (VG.Proof.MlDsa.Arm.Sample.Ball.M2 σ t) := by
  have l := h.bat
  have hi := h.lt
  have hj : (VG.Proof.MlDsa.Arm.Sample.Ball.Xb σ t).toNat ≤ (VG.Proof.MlDsa.Arm.Sample.Ball.St σ t).2 := by have := h.z; rw [hz] at this; simpa using this
  have hA := addr_aJ hp (j := (VG.Proof.MlDsa.Arm.Sample.Ball.Xb σ t).toNat) (by omega)
  have hB := addr_aJ hp (j := (VG.Proof.MlDsa.Arm.Sample.Ball.St σ t).2) hi
  rw [← h.r8, ← l.env.r5] at hA
  rw [← l.r2, ← l.env.r5] at hB
  have inA : (VG.Proof.MlDsa.Arm.Sample.Ball.spOf σ).aR.Contains (VG.Proof.MlDsa.Sample.coeffAddr (VG.Proof.MlDsa.Arm.Sample.Ball.spOf σ).A (VG.Proof.MlDsa.Arm.Sample.Ball.Xb σ t).toNat) 4 := VG.Proof.MlDsa.Sample.coeff_contains _ (by omega)
  have inB : (VG.Proof.MlDsa.Arm.Sample.Ball.spOf σ).aR.Contains (VG.Proof.MlDsa.Sample.coeffAddr (VG.Proof.MlDsa.Arm.Sample.Ball.spOf σ).A (VG.Proof.MlDsa.Arm.Sample.Ball.St σ t).2) 4 := VG.Proof.MlDsa.Sample.coeff_contains _ hi
  have wA : (VG.Proof.MlDsa.Arm.Sample.Ball.spOf σ).aR ∈ s.wr := by rw [l.env.wr, hp.wr]; simp
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sample.Ball.bSet1_ok s hA hB ⟨_, List.mem_append_right _ wA, inA⟩ ⟨_, wA, inB⟩)
    fun s1 ⟨m1, g10, z1, g1, rd1, wr1, sp1⟩ => ?_)
  rw [VG.Proof.MlDsa.Arm.Sample.Ball.sign_bit hτ (VG.Proof.MlDsa.Arm.Sample.Ball.St_ge σ t) l.sg] at z1
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sample.Ball.bSign_ok s1 _ z1) fun s2 ⟨g11, g2, m2, rd2, wr2, sp2⟩ => ?_)
  have e10 : State.addr (s2.gpr .r10 + BitVec.ofNat 32 0) = VG.Proof.MlDsa.Sample.coeffAddr (VG.Proof.MlDsa.Arm.Sample.Ball.spOf σ).A (VG.Proof.MlDsa.Arm.Sample.Ball.Xb σ t).toNat := by
    rw [g2 _ (by decide), g10]; exact hA
  refine WP.mono (VG.Proof.MlDsa.Arm.Sample.Ball.bSet3_ok s2 e10 (by rw [wr2, wr1]; exact ⟨_, wA, inA⟩))
    fun s3 ⟨m3, g1', g4', g2', g3, rd3, wr3, sp3⟩ => ?_
  have k : ∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r4 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → s3.gpr r = s.gpr r :=
    fun r a b c d e f => by rw [g3 r a b c, g2 r e, g1 r d e f]
  have hst := VG.Proof.MlDsa.Arm.Sample.Ball.St_succ σ ht
  rw [bStep, ifT hi, ifF (show ¬ (VG.Proof.MlDsa.Arm.Sample.Ball.Xb σ t).toNat > (VG.Proof.MlDsa.Arm.Sample.Ball.St σ t).2 by omega)] at hst
  have hf : Frame [(VG.Proof.MlDsa.Arm.Sample.Ball.spOf σ).aR] s.mem s3.mem := by
    rw [m3, m2, m1]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ inB).writeW (List.mem_singleton_self _) _ inA
  refine ⟨l.env.step hp hf (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact .inr (.inl fun _ h => h))
    (k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [rd3, rd2, rd1]) (by rw [wr3, wr2, wr1]) (by rw [sp3, sp2, sp1]), ?_,
    by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact l.r0, ?_, ?_,
    by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact l.r3, ?_⟩
  · rw [MlKem.bytesAt_frame hf (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact (hp.a_scr.sub_right (sub_scr (a := 840) (n := 272) (by omega))).symm) (by omega)]
    exact l.out
  · rw [g2', g2 _ (by decide), g1 _ (by decide) (by decide) (by decide), l.r2, hst, BitVec.ofNat_add]; rfl
  · rw [hst]
    refine VG.Proof.MlDsa.Arm.Sample.Ball.sg_succ (VG.Proof.MlDsa.Arm.Sample.Ball.St_ge σ t) l.sg ?_ ?_
    · rw [g1', g2 _ (by decide), g2 _ (by decide), g1 _ (by decide) (by decide) (by decide),
        g1 _ (by decide) (by decide) (by decide)]
    · rw [g4', g2 _ (by decide), g1 _ (by decide) (by decide) (by decide)]
  · intro k hk
    rw [hst, m3, m2, m1, g11, VG.Proof.MlDsa.Arm.Sample.Ball.sgn_word, VG.Proof.MlDsa.Sample.coeffAt_writeW _ _ hk (by omega), VG.Proof.MlDsa.Sample.coeffAt_writeW _ _ hk hi,
      ipoly_set!_get _ _ (by simp only [n]; omega), ipoly_set!_get _ _ (by simp only [n]; omega)]
    by_cases ejk : (VG.Proof.MlDsa.Arm.Sample.Ball.Xb σ t).toNat = k
    · rw [ifT ejk, ifT ejk]
    · rw [ifF ejk, ifF ejk]
      by_cases eik : (VG.Proof.MlDsa.Arm.Sample.Ball.St σ t).2 = k
      · subst eik; rw [ifT rfl, ifT rfl, ← VG.Proof.MlDsa.Sample.coeffAt_eq, l.st _ (by omega)]
      · rw [ifF eik, ifF eik]; exact l.st k hk

omit hp in
/-- `M2` when iteration `t` changes nothing. -/
theorem M2.of_same {t : Nat} {s : State} (l : VG.Proof.MlDsa.Arm.Sample.Ball.BAt σ t s) (hst : VG.Proof.MlDsa.Arm.Sample.Ball.St σ (t + 1) = VG.Proof.MlDsa.Arm.Sample.Ball.St σ t) : VG.Proof.MlDsa.Arm.Sample.Ball.M2 σ t s :=
  ⟨l.env, l.out, l.r0, by rw [hst]; exact l.r2, by rw [hst]; exact l.sg, l.r3, by rw [hst]; exact l.st⟩

theorem tryB (hτ : VG.Proof.MlDsa.Arm.Sample.Ball.tau σ ≤ 256) {t : Nat} (ht : t < 264) {s : State} (h : VG.Proof.MlDsa.Arm.Sample.Ball.T1 σ t s) :
    WP isa (.ite .eq bSet (.block [])) s (VG.Proof.MlDsa.Arm.Sample.Ball.M2 σ t) := by
  refine WP.ite s.z rfl (fun e => VG.Proof.MlDsa.Arm.Sample.Ball.setOk hp hτ ht h e) (fun e => ?_)
  have hj : (VG.Proof.MlDsa.Arm.Sample.Ball.St σ t).2 < (VG.Proof.MlDsa.Arm.Sample.Ball.Xb σ t).toNat := by
    have := h.z; rw [e] at this; exact Nat.lt_of_not_le (of_decide_eq_false this.symm)
  have hst := VG.Proof.MlDsa.Arm.Sample.Ball.St_succ σ ht
  rw [bStep, ifT h.lt, ifT hj] at hst
  exact WP.block_nil (M2.of_same h.bat hst)

theorem pieceB (hτ : VG.Proof.MlDsa.Arm.Sample.Ball.tau σ ≤ 256) {t : Nat} (ht : t < 264) {s : State} (h : VG.Proof.MlDsa.Arm.Sample.Ball.M1 σ t s) :
    WP isa (.ite .eq (.block []) bTry) s (VG.Proof.MlDsa.Arm.Sample.Ball.M2 σ t) := by
  refine WP.ite s.z rfl (fun e => ?_) (fun e => WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sample.Ball.tryA hp ht h e) fun _ h1 => VG.Proof.MlDsa.Arm.Sample.Ball.tryB hp hτ ht h1))
  have hl : (VG.Proof.MlDsa.Arm.Sample.Ball.St σ t).2 = 256 := by
    have := h.z; rw [e] at this; simp at this; have := VG.Proof.MlDsa.Arm.Sample.Ball.St_le σ t; omega
  exact WP.block_nil (M2.of_same h.bat (by rw [VG.Proof.MlDsa.Arm.Sample.Ball.St_succ σ ht, bStep_full hl]))

omit hp in
theorem pieceC {t : Nat} (ht : t < 264) {s : State} (h : VG.Proof.MlDsa.Arm.Sample.Ball.M2 σ t s) :
    WP isa (.block (VG.Impl.MlDsa.Arm.Sample.step 1)) s fun s' => VG.Proof.MlDsa.Arm.Sample.Ball.BAt σ (t + 1) s' ∧ s'.z = decide (t + 1 = 264) := by
  refine WP.mono (step_ok s (k := 1) (by decide)) fun s' ⟨r0, r3, z, g, m, rd, wr, sp⟩ =>
    ⟨⟨h.env.same m (g _ (by decide) (by decide)) (g _ (by decide) (by decide)) rd wr sp, by rw [m]; exact h.out,
      by rw [r0, h.r0, ptr_add_add32, Nat.add_assoc], by rw [g _ (by decide) (by decide)]; exact h.r2,
      by show _ = _; rw [g _ (by decide) (by decide), g _ (by decide) (by decide)]; exact h.sg,
      by rw [r3, h.r3]; exact count_sub (k := 1) ht, by rw [m]; exact h.st⟩, ?_⟩
  rw [z, h.r3]; exact count_z (k := 1) ht (by decide) (by decide)

/-- An iteration. -/
theorem body_ok (hτ : VG.Proof.MlDsa.Arm.Sample.Ball.tau σ ≤ 256) {t : Nat} (ht : t < 264) {s : State} (h : VG.Proof.MlDsa.Arm.Sample.Ball.BAt σ t s) :
    WP isa bBody s fun s' => VG.Proof.MlDsa.Arm.Sample.Ball.BAt σ (t + 1) s' ∧ s'.z = decide (t + 1 = 264) :=
  WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sample.Ball.pieceA h) fun _ h1 => WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sample.Ball.pieceB hp hτ ht h1) fun _ h2 => VG.Proof.MlDsa.Arm.Sample.Ball.pieceC ht h2))

end

end VG.Proof.MlDsa.Arm.Sample.Ball

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Sample.Ball`. -/
section

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_sample_in_ball`, correctness

The function runs in pieces: the prologue (`J0`), the sponge, whose output is
`H(c̃, 272)` (`J6`), the zeroing of `c` (`ZDone`), the setup of the loop,
which loads the sign bits (`setup_ok`, with `readW_pair`: the two words are
the first 8 bytes of output as a little-endian number), and the 264 iterations
of the loop (`BAt`, `body_ok`), after which `c` and `i` are what `ballFold`
computes.
-/

namespace VG.Proof.MlDsa.Arm.Sample.Ball

open VG VG.Arm
open VG.Proof.MlKem.Arm
open VG.Proof.MlDsa.Arm.Sample
open VG.Impl.MlDsa.Arm.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q H IPoly n ofInt coeffAt PolyIs toRq)
open VG.Spec.Sha3 (bytesAt)

/-! ## The sign bits -/

theorem readW32_getLsbD (m : Mem) (a : Addr) {k : Nat} (hk : k < 32) :
    (m.readW a 32).getLsbD k = (m (a + BitVec.ofNat 64 (k / 8))).getLsbD (k % 8) := by
  rw [← Mem.extractLsb'_read m a (n := 4) (j := k / 8) (by omega), BitVec.getLsbD_extractLsb']
  simp only [Mem.readW, BitVec.getLsbD_setWidth, show k % 8 < 8 by omega, decide_true, Bool.true_and, hk]
  congr 1; omega

/-- The two words at `a`, as a number: the first 8 bytes there. -/
theorem readW_pair (m : Mem) (a : Addr) (L : List Byte) (h : ∀ k < 8, m (a + BitVec.ofNat 64 k) = L.getD k 0) :
    (m.readW a 32).toNat + 2 ^ 32 * (m.readW (a + BitVec.ofNat 64 4) 32).toNat = leNat (L.take 8) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.add_comm, Nat.testBit_two_pow_mul_add _ (BitVec.isLt _), testBit_leNat]
  split
  · rename_i hk
    rw [BitVec.testBit_toNat, VG.Proof.MlDsa.Arm.Sample.Ball.readW32_getLsbD _ _ hk, h _ (by omega), List.getD_eq_getElem?_getD,
      List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega)]
  · rename_i hk
    rw [BitVec.testBit_toNat]
    by_cases h64 : k < 64
    · rw [VG.Proof.MlDsa.Arm.Sample.Ball.readW32_getLsbD _ _ (by omega), add_ofNat_add, show 4 + (k - 32) / 8 = k / 8 by omega,
        show (k - 32) % 8 = k % 8 by omega, h _ (by omega), List.getD_eq_getElem?_getD,
        List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega)]
    · rw [BitVec.getLsbD_of_ge _ _ (by omega), List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by rw [List.length_take]; omega)]
      simp

/-! ## The setup of the loop -/

theorem setup1_ok (s : State) {A C : Addr} (hA : State.addr (s.gpr .r6 + BitVec.ofNat 32 840) = A)
    (hC : State.addr (s.gpr .r6 + BitVec.ofNat 32 844) = C) (hrA : InRegions (s.rd ++ s.wr) A 4)
    (hrC : InRegions (s.rd ++ s.wr) C 4) :
    WP isa (.block (bSetup ++ ([.mov .r3 (.imm 264)] : List Instr))) s fun s' =>
      s'.gpr .r1 = s.mem.readW A 32 ∧ s'.gpr .r4 = s.mem.readW C 32 ∧
        s'.gpr .r2 = BitVec.ofNat 32 256 - s.gpr .r7 ∧ s'.gpr .r0 = s.gpr .r6 + BitVec.ofNat 32 848 ∧
        s'.gpr .r3 = BitVec.ofNat 32 264 ∧ s'.gpr .r5 = s.gpr .r5 ∧ s'.gpr .r6 = s.gpr .r6 ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [bSetup, hA, hC, hrA, hrC, and_self, and_true, true_and]
  exact ⟨rfl, rfl⟩

section
variable {σ : State} (hp : SpOk (VG.Proof.MlDsa.Arm.Sample.Ball.spOf σ) σ) (hτ : VG.Proof.MlDsa.Arm.Sample.Ball.tau σ ≤ 256)
include hp hτ

theorem setup_ok {s : State} (h : VG.Proof.MlDsa.Arm.Sample.Ball.ZDone σ s) :
    WP isa (.block (bSetup ++ ([.mov .r3 (.imm 264)] : List Instr))) s (VG.Proof.MlDsa.Arm.Sample.Ball.BAt σ 0) := by
  have e6 := h.env.r6
  have hA : State.addr (s.gpr .r6 + BitVec.ofNat 32 840) = (VG.Proof.MlDsa.Arm.Sample.Ball.spOf σ).at' 840 := by rw [e6]; exact at_eq hp (by omega)
  have hC : State.addr (s.gpr .r6 + BitVec.ofNat 32 844) = (VG.Proof.MlDsa.Arm.Sample.Ball.spOf σ).at' 840 + BitVec.ofNat 64 4 := by
    rw [e6, at_eq hp (by omega), add_ofNat_add]
  have hC' : InRegions (s.rd ++ s.wr) ((VG.Proof.MlDsa.Arm.Sample.Ball.spOf σ).at' 840 + BitVec.ofNat 64 4) 4 := by
    rw [add_ofNat_add]; exact inScrRd hp h.env (by omega)
  refine WP.mono (VG.Proof.MlDsa.Arm.Sample.Ball.setup1_ok s hA hC (inScrRd hp h.env (by omega)) hC')
    fun s' ⟨g1, g4, g2, g0, g3, g5, g6, m, rd, wr, sp⟩ => ?_
  have hSt : VG.Proof.MlDsa.Arm.Sample.Ball.St σ 0 = (Vector.replicate n 0, VG.Proof.MlDsa.Arm.Sample.Ball.i0 σ) := rfl
  refine ⟨h.env.same m g5 g6 rd wr sp, by rw [m]; exact h.out, by rw [g0, e6], ?_, ?_,
    by rw [g3], by rw [m, hSt]; exact h.st⟩
  · rw [g2, h.r7, hSt]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, toNat_ofNat32 (by omega), toNat_ofNat32 (by simp only [VG.Proof.MlDsa.Arm.Sample.Ball.i0]; omega)]
    have := (σ.gpr .r2).isLt
    simp only [VG.Proof.MlDsa.Arm.Sample.Ball.i0, VG.Proof.MlDsa.Arm.Sample.Ball.tau] at hτ ⊢
    omega
  · show _ = _
    rw [g1, g4, hSt, Nat.sub_self, Nat.pow_zero, Nat.div_one]
    exact VG.Proof.MlDsa.Arm.Sample.Ball.readW_pair _ _ _ fun k hk => by
      have := congrArg (fun L => L.getD k 0) h.out
      rw [MlKem.bytesAt_getD _ _ (by omega)] at this
      exact this

/-- The loop, from the zeroed polynomial. -/
theorem loop_ok {s : State} (h : VG.Proof.MlDsa.Arm.Sample.Ball.ZDone σ s) : WP isa bLoop s (VG.Proof.MlDsa.Arm.Sample.Ball.BAt σ 264) :=
  WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sample.Ball.setup_ok hp hτ h) fun _ h0 =>
    wp_loop_ne (VG.Proof.MlDsa.Arm.Sample.Ball.BAt σ) (N := 264) (by decide) (fun t ht s h => VG.Proof.MlDsa.Arm.Sample.Ball.body_ok hp hτ ht h) (fun _ h => h) h0)

end

/-! ## The end -/

theorem St_all (σ : State) : VG.Proof.MlDsa.Arm.Sample.Ball.St σ 264 = ballFold (VG.Proof.MlDsa.Arm.Sample.Ball.tau σ) (VG.Proof.MlDsa.Arm.Sample.Ball.X σ) := by
  simp only [VG.Proof.MlDsa.Arm.Sample.Ball.St, ballFold, VG.Proof.MlDsa.Arm.Sample.Ball.i0]; rw [List.take_of_length_le (by rw [List.length_drop, VG.Proof.MlDsa.Arm.Sample.Ball.X_length])]

theorem end_ok {σ : State} (hp : SpOk (VG.Proof.MlDsa.Arm.Sample.Ball.spOf σ) σ) {s : State} (h : VG.Proof.MlDsa.Arm.Sample.Ball.BAt σ 264 s) :
    WP isa (.block (retJ ++ epi)) s fun s' =>
      s'.gpr .r0 = (if (ballFold (VG.Proof.MlDsa.Arm.Sample.Ball.tau σ) (VG.Proof.MlDsa.Arm.Sample.Ball.X σ)).2 = 256 then 1 else 0) ∧
      ((ballFold (VG.Proof.MlDsa.Arm.Sample.Ball.tau σ) (VG.Proof.MlDsa.Arm.Sample.Ball.X σ)).2 = 256 →
        PolyIs s'.mem (State.addr (σ.gpr .r3)) (toRq (ballFold (VG.Proof.MlDsa.Arm.Sample.Ball.tau σ) (VG.Proof.MlDsa.Arm.Sample.Ball.X σ)).1)) ∧
      abiPreserved σ s' :=
  WP.mono (retEpi_ok hp h.env h.r2 (VG.Proof.MlDsa.Arm.Sample.Ball.St_le _ _)) fun s' ⟨h0, hm, ha⟩ => ⟨by rw [h0, VG.Proof.MlDsa.Arm.Sample.Ball.St_all], fun _ => by
    rw [hm]
    have hst := h.st
    rw [VG.Proof.MlDsa.Arm.Sample.Ball.St_all] at hst
    refine polyIs_of_coeffAt fun i hi => ?_
    rw [hst i hi, getElem!_pos _ i hi, getElem!_pos _ i hi]
    simp only [toRq, Vector.getElem_map], ha⟩

/-- The function, from an entry state whose regions are those of a call. -/
theorem correct {σ : State} (hp : VG.Proof.MlDsa.Arm.Sample.Ball.Pre σ) : WP isa Impl.MlDsa.Arm.Sample.sampleInBall σ fun s' =>
    s'.gpr .r0 = (if (ballFold (VG.Proof.MlDsa.Arm.Sample.Ball.tau σ) (VG.Proof.MlDsa.Arm.Sample.Ball.X σ)).2 = 256 then 1 else 0) ∧
      ((ballFold (VG.Proof.MlDsa.Arm.Sample.Ball.tau σ) (VG.Proof.MlDsa.Arm.Sample.Ball.X σ)).2 = 256 →
        PolyIs s'.mem (State.addr (σ.gpr .r3)) (toRq (ballFold (VG.Proof.MlDsa.Arm.Sample.Ball.tau σ) (VG.Proof.MlDsa.Arm.Sample.Ball.X σ)).1)) ∧
      abiPreserved σ s' := by
  have hτ : VG.Proof.MlDsa.Arm.Sample.Ball.tau σ ≤ 256 := by have := hp.tau_le; omega
  exact WP.seq (WP.mono (pro_ball hp.ok rfl (by simp) rfl rfl rfl hp.arg) fun _ h1 =>
    WP.seq (WP.mono (sponge_ok hp.ok (rate := 136) (outlen := 272) (by decide) (by decide) (by decide) (by decide) h1)
      fun _ h2 => WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sample.Ball.zero_ok hp.ok h2) fun _ h3 => WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sample.Ball.loop_ok hp.ok hτ h3)
        fun _ h4 => VG.Proof.MlDsa.Arm.Sample.Ball.end_ok hp.ok h4))))

end VG.Proof.MlDsa.Arm.Sample.Ball

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Sample.BallCT`. -/
section

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_sample_in_ball`, constant time but for `c̃`, and `Verified`

Two runs whose `c̃` (the declared leak), `len`, `τ`, pointers and stack
pointer agree (`Two`) leak the same: the prologue by `relct_ldrSp` (the load
of `scratch` from the stack) and the taint analysis, the sponge by
`sponge_ct`, the blocks around the loop by the taint analysis, and the loop,
whose branches and addresses depend on the SHAKE256 output, by relating the
two runs iteration by iteration (`body_ct`): both are at the same iteration
with the same `i`, sign bits and byte `j` (being those of the same output), so
each branch goes the same way, and each piece between the branches is constant
time in registers that hold the same values in both runs.
-/

namespace VG.Proof.MlDsa.Arm.Sample.Ball

open VG VG.Arm
open VG.Proof.MlKem.Arm
open VG.Proof.MlDsa.Arm.Sample
open VG.Impl.MlDsa.Arm.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q H IPoly n ofInt coeffAt PolyIs toRq)
open VG.Spec.Sha3 (bytesAt)
open VG.Arm.RegUpd (gpr_setReg_self gpr_setReg_of_ne)

/-! ## Blocks -/

/-- A block in two parts. -/
theorem relct_append {P R Q : State → State → Prop} {l₁ l₂ : List Instr} (h₁ : RelCT isa P (.block l₁) R)
    (h₂ : RelCT isa R (.block l₂) Q) : RelCT isa P (.block (l₁ ++ l₂)) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  rw [Exec.block_iff, execBlock_append] at e₁ e₂
  obtain ⟨⟨u₁, v₁⟩, a₁, e₁⟩ := Option.bind_eq_some_iff.mp e₁
  obtain ⟨⟨w₁, x₁⟩, b₁, e₁⟩ := Option.map_eq_some_iff.mp e₁
  obtain ⟨⟨u₂, v₂⟩, a₂, e₂⟩ := Option.bind_eq_some_iff.mp e₂
  obtain ⟨⟨w₂, x₂⟩, b₂, e₂⟩ := Option.map_eq_some_iff.mp e₂
  obtain ⟨rfl, r⟩ := h₁ _ _ _ _ _ _ hp (.block a₁) (.block a₂)
  obtain ⟨rfl, q⟩ := h₂ _ _ _ _ _ _ r (.block b₁) (.block b₂)
  cases e₁; cases e₂
  exact ⟨rfl, q⟩

/-- The load of an argument from the stack leaks its address. -/
theorem relct_ldrSp {P : State → State → Prop} {t : Reg} {off : Nat} (hsp : ∀ a b, P a b → a.sp = b.sp) :
    RelCT isa P (.block [.ldrSp t off]) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  have tr : ∀ {s s' : State} {tr : List Leak}, execBlock isa [.ldrSp t off] s = some (s', tr) →
      tr = [Leak.addr (State.addr (s.sp + BitVec.ofNat 32 off))] := fun {s s' tr} e => by
    simp only [execBlock] at e
    split at e
    · cases e
    · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
      rw [← e.2]; rfl
  rw [tr e₁, tr e₂, hsp _ _ hp]
  exact ⟨rfl, trivial⟩

theorem ldrSp_ok (σ : State) (hin : InRegions (σ.rd ++ σ.wr) (stackArgAddr σ 0) 4) :
    WP isa (.block [.ldrSp .r12 0]) σ fun s => s = σ.setReg .r12 (stackArg σ 0) := by
  have hin' : InRegions (σ.rd ++ σ.wr) (State.addr (σ.sp + BitVec.ofNat 32 0)) 4 := hin
  have o0 : (0 : Nat) < 4096 := by decide
  apply WP.of_runBlock
  rw [runBlock_cons]
  simp only [exec, o0, ite_true, State.load32, hin', Option.map_some, runStep_some, runBlock_nil]
  exact ⟨_, rfl, rfl⟩

/-! ## Two runs -/

/-- Two runs, from entry states that agree on the public data. -/
structure Two (σ₁ σ₂ : State) : Prop where
  p₁ : VG.Proof.MlDsa.Arm.Sample.Ball.Pre σ₁
  p₂ : VG.Proof.MlDsa.Arm.Sample.Ball.Pre σ₂
  sp : σ₁.sp = σ₂.sp
  r0 : σ₁.gpr .r0 = σ₂.gpr .r0
  r1 : σ₁.gpr .r1 = σ₂.gpr .r1
  r2 : σ₁.gpr .r2 = σ₂.gpr .r2
  r3 : σ₁.gpr .r3 = σ₂.gpr .r3
  scr : stackArg σ₁ 0 = stackArg σ₂ 0
  B : VG.Proof.MlDsa.Arm.Sample.Ball.B σ₁ = VG.Proof.MlDsa.Arm.Sample.Ball.B σ₂

section
variable {σ₁ σ₂ : State} (two : VG.Proof.MlDsa.Arm.Sample.Ball.Two σ₁ σ₂)
include two

theorem Two.P_eq : VG.Proof.MlDsa.Arm.Sample.Ball.spOf σ₁ = VG.Proof.MlDsa.Arm.Sample.Ball.spOf σ₂ := by simp only [VG.Proof.MlDsa.Arm.Sample.Ball.spOf, two.r0, two.r1, two.r2, two.r3, two.scr]
theorem Two.X_eq : VG.Proof.MlDsa.Arm.Sample.Ball.X σ₁ = VG.Proof.MlDsa.Arm.Sample.Ball.X σ₂ := by simp only [VG.Proof.MlDsa.Arm.Sample.Ball.X, two.B]
theorem Two.tau_eq : VG.Proof.MlDsa.Arm.Sample.Ball.tau σ₁ = VG.Proof.MlDsa.Arm.Sample.Ball.tau σ₂ := by simp only [VG.Proof.MlDsa.Arm.Sample.Ball.tau, two.r2]
theorem Two.St_eq (t : Nat) : VG.Proof.MlDsa.Arm.Sample.Ball.St σ₁ t = VG.Proof.MlDsa.Arm.Sample.Ball.St σ₂ t := by simp only [VG.Proof.MlDsa.Arm.Sample.Ball.St, VG.Proof.MlDsa.Arm.Sample.Ball.i0, two.X_eq, two.tau_eq]
theorem Two.Xb_eq (t : Nat) : VG.Proof.MlDsa.Arm.Sample.Ball.Xb σ₁ t = VG.Proof.MlDsa.Arm.Sample.Ball.Xb σ₂ t := by simp only [VG.Proof.MlDsa.Arm.Sample.Ball.Xb, two.X_eq]
theorem Two.Wn_eq : VG.Proof.MlDsa.Arm.Sample.Ball.Wn σ₁ = VG.Proof.MlDsa.Arm.Sample.Ball.Wn σ₂ := by simp only [VG.Proof.MlDsa.Arm.Sample.Ball.Wn, two.X_eq]

/-- The sign bits not yet used, in both runs. -/
theorem Two.sg_eq {i : Nat} {a b : State} (ha : VG.Proof.MlDsa.Arm.Sample.Ball.Sg σ₁ i a) (hb : VG.Proof.MlDsa.Arm.Sample.Ball.Sg σ₂ i b) :
    a.gpr .r1 = b.gpr .r1 ∧ a.gpr .r4 = b.gpr .r4 := by
  have ha' : (a.gpr .r1).toNat + 2 ^ 32 * (a.gpr .r4).toNat = VG.Proof.MlDsa.Arm.Sample.Ball.Wn σ₁ / 2 ^ (i - VG.Proof.MlDsa.Arm.Sample.Ball.i0 σ₁) := ha
  have hb' : (b.gpr .r1).toNat + 2 ^ 32 * (b.gpr .r4).toNat = VG.Proof.MlDsa.Arm.Sample.Ball.Wn σ₂ / 2 ^ (i - VG.Proof.MlDsa.Arm.Sample.Ball.i0 σ₂) := hb
  rw [← two.Wn_eq, show VG.Proof.MlDsa.Arm.Sample.Ball.i0 σ₂ = VG.Proof.MlDsa.Arm.Sample.Ball.i0 σ₁ by simp only [VG.Proof.MlDsa.Arm.Sample.Ball.i0, two.tau_eq]] at hb'
  have := (a.gpr .r1).isLt; have := (b.gpr .r1).isLt
  exact ⟨BitVec.eq_of_toNat_eq (by omega), BitVec.eq_of_toNat_eq (by omega)⟩

/-! ## The loop -/

omit two in
theorem pieceA_ct {t : Nat} : RelCT isa (fun a b => VG.Proof.MlDsa.Arm.Sample.Ball.BAt σ₁ t a ∧ VG.Proof.MlDsa.Arm.Sample.Ball.BAt σ₂ t b) (.block jFull)
    fun a b => VG.Proof.MlDsa.Arm.Sample.Ball.M1 σ₁ t a ∧ VG.Proof.MlDsa.Arm.Sample.Ball.M1 σ₂ t b :=
  relW (taintRel [] (fun _ _ _ _ h => absurd h List.not_mem_nil) (by taint_decide))
    fun a b h => ⟨VG.Proof.MlDsa.Arm.Sample.Ball.pieceA h.1, VG.Proof.MlDsa.Arm.Sample.Ball.pieceA h.2⟩

theorem tryA_ct {t : Nat} (ht : t < 264) :
    RelCT isa (fun a b => (VG.Proof.MlDsa.Arm.Sample.Ball.M1 σ₁ t a ∧ VG.Proof.MlDsa.Arm.Sample.Ball.M1 σ₂ t b) ∧ isa.eval .eq a = some false)
      (.block [.ldrb .r8 .r0 0, .dp .sub .r11 .r2 (.reg .r8), .mov .r11 (.shifted .r11 .lsr 31),
        .cmp .r11 (.imm 0)]) fun a b => VG.Proof.MlDsa.Arm.Sample.Ball.T1 σ₁ t a ∧ VG.Proof.MlDsa.Arm.Sample.Ball.T1 σ₂ t b := by
  refine relW (taintRel [.r0] (fun a b h r hr => ?_) (by taint_decide)) fun a b h => ?_
  · rw [List.mem_singleton] at hr; subst hr
    rw [h.1.1.bat.r0, h.1.2.bat.r0, two.scr]
  · have za : a.z = false := Option.some.inj h.2
    have zb : b.z = false := by
      rw [h.1.2.z, ← two.St_eq, ← h.1.1.z]; exact za
    exact ⟨VG.Proof.MlDsa.Arm.Sample.Ball.tryA two.p₁.ok ht h.1.1 za, VG.Proof.MlDsa.Arm.Sample.Ball.tryA two.p₂.ok ht h.1.2 zb⟩

theorem set_ct {t : Nat} (ht : t < 264) :
    RelCT isa (fun a b => (VG.Proof.MlDsa.Arm.Sample.Ball.T1 σ₁ t a ∧ VG.Proof.MlDsa.Arm.Sample.Ball.T1 σ₂ t b) ∧ isa.eval .eq a = some true) bSet
      fun a b => VG.Proof.MlDsa.Arm.Sample.Ball.M2 σ₁ t a ∧ VG.Proof.MlDsa.Arm.Sample.Ball.M2 σ₂ t b := by
  refine relW (taintRel [.r1, .r2, .r4, .r5, .r8] (fun a b h r hr => ?_) (by taint_decide)) fun a b h => ?_
  · have l₁ := h.1.1.bat
    have l₂ := h.1.2.bat
    have sg := two.sg_eq (two.St_eq t ▸ l₁.sg) l₂.sg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact sg.1
    · rw [l₁.r2, l₂.r2, two.St_eq]
    · exact sg.2
    · rw [l₁.env.r5, l₂.env.r5, two.P_eq]
    · rw [h.1.1.r8, h.1.2.r8, two.Xb_eq]
  · have za : a.z = true := Option.some.inj h.2
    have zb : b.z = true := by
      rw [h.1.2.z, ← two.St_eq, ← two.Xb_eq, ← h.1.1.z]; exact za
    have h1 := two.p₁.tau_le
    have h2 := two.p₂.tau_le
    exact ⟨VG.Proof.MlDsa.Arm.Sample.Ball.setOk two.p₁.ok (by omega) ht h.1.1 za, VG.Proof.MlDsa.Arm.Sample.Ball.setOk two.p₂.ok (by omega) ht h.1.2 zb⟩

omit two in
theorem nil_ct {P : State → State → Prop} {Q₁ Q₂ : State → Prop} (hq : ∀ a b, P a b → Q₁ a ∧ Q₂ b) :
    RelCT isa P (.block []) fun a b => Q₁ a ∧ Q₂ b :=
  relW (taintRel [] (fun _ _ _ _ h => absurd h List.not_mem_nil) (by taint_decide))
    fun a b h => ⟨WP.block_nil (hq a b h).1, WP.block_nil (hq a b h).2⟩

omit two in
theorem skip_of {σ : State} {t : Nat} (ht : t < 264) {s : State} (h : VG.Proof.MlDsa.Arm.Sample.Ball.T1 σ t s) (e : s.z = false) :
    VG.Proof.MlDsa.Arm.Sample.Ball.M2 σ t s := by
  have hj : (VG.Proof.MlDsa.Arm.Sample.Ball.St σ t).2 < (VG.Proof.MlDsa.Arm.Sample.Ball.Xb σ t).toNat := by
    have := h.z; rw [e] at this; exact Nat.lt_of_not_le (of_decide_eq_false this.symm)
  have hst := VG.Proof.MlDsa.Arm.Sample.Ball.St_succ σ ht
  rw [bStep, ifT h.lt, ifT hj] at hst
  exact M2.of_same h.bat hst

omit two in
theorem full_of {σ : State} {t : Nat} (ht : t < 264) {s : State} (h : VG.Proof.MlDsa.Arm.Sample.Ball.M1 σ t s) (e : s.z = true) :
    VG.Proof.MlDsa.Arm.Sample.Ball.M2 σ t s := by
  have hl : (VG.Proof.MlDsa.Arm.Sample.Ball.St σ t).2 = 256 := by
    have := h.z; rw [e] at this; simp at this; have := VG.Proof.MlDsa.Arm.Sample.Ball.St_le σ t; omega
  exact M2.of_same h.bat (by rw [VG.Proof.MlDsa.Arm.Sample.Ball.St_succ σ ht, bStep_full hl])

theorem body_ct {t : Nat} (ht : t < 264) :
    RelCT isa (fun a b => VG.Proof.MlDsa.Arm.Sample.Ball.BAt σ₁ t a ∧ VG.Proof.MlDsa.Arm.Sample.Ball.BAt σ₂ t b) bBody fun a b =>
      (VG.Proof.MlDsa.Arm.Sample.Ball.BAt σ₁ (t + 1) a ∧ a.z = decide (t + 1 = 264)) ∧ (VG.Proof.MlDsa.Arm.Sample.Ball.BAt σ₂ (t + 1) b ∧ b.z = decide (t + 1 = 264)) := by
  refine RelCT.seq VG.Proof.MlDsa.Arm.Sample.Ball.pieceA_ct (RelCT.seq (R := fun a b => VG.Proof.MlDsa.Arm.Sample.Ball.M2 σ₁ t a ∧ VG.Proof.MlDsa.Arm.Sample.Ball.M2 σ₂ t b) ?_ ?_)
  · refine RelCT.ite (fun a b h => by show some a.z = some b.z; rw [h.1.z, h.2.z, two.St_eq]) ?_ ?_
    · exact VG.Proof.MlDsa.Arm.Sample.Ball.nil_ct fun a b h => ⟨VG.Proof.MlDsa.Arm.Sample.Ball.full_of ht h.1.1 (Option.some.inj h.2), VG.Proof.MlDsa.Arm.Sample.Ball.full_of ht h.1.2 (by
        rw [h.1.2.z, ← two.St_eq, ← h.1.1.z]; exact Option.some.inj h.2)⟩
    · refine RelCT.seq (VG.Proof.MlDsa.Arm.Sample.Ball.tryA_ct two ht) (RelCT.ite (fun a b h => by
        show some a.z = some b.z; rw [h.1.z, h.2.z, two.St_eq, two.Xb_eq]) (VG.Proof.MlDsa.Arm.Sample.Ball.set_ct two ht) ?_)
      exact VG.Proof.MlDsa.Arm.Sample.Ball.nil_ct fun a b h => ⟨VG.Proof.MlDsa.Arm.Sample.Ball.skip_of ht h.1.1 (Option.some.inj h.2), VG.Proof.MlDsa.Arm.Sample.Ball.skip_of ht h.1.2 (by
        rw [h.1.2.z, ← two.St_eq, ← two.Xb_eq, ← h.1.1.z]; exact Option.some.inj h.2)⟩
  · exact relW (taintRel [] (fun _ _ _ _ h => absurd h List.not_mem_nil) (by taint_decide))
      fun a b h => ⟨VG.Proof.MlDsa.Arm.Sample.Ball.pieceC ht h.1, VG.Proof.MlDsa.Arm.Sample.Ball.pieceC ht h.2⟩

theorem loop_ct : RelCT isa (fun a b => VG.Proof.MlDsa.Arm.Sample.Ball.BAt σ₁ 0 a ∧ VG.Proof.MlDsa.Arm.Sample.Ball.BAt σ₂ 0 b) (.loop bBody .ne) fun a b =>
    VG.Proof.MlDsa.Arm.Sample.Ball.BAt σ₁ 264 a ∧ VG.Proof.MlDsa.Arm.Sample.Ball.BAt σ₂ 264 b := by
  refine RelCT.mono (RelCT.loop (M := isa) (body := bBody) (c := .ne)
    (Q := fun a b => VG.Proof.MlDsa.Arm.Sample.Ball.BAt σ₁ 264 a ∧ VG.Proof.MlDsa.Arm.Sample.Ball.BAt σ₂ 264 b)
    (fun n a b => ∃ t, t < 264 ∧ n = 264 - t ∧ VG.Proof.MlDsa.Arm.Sample.Ball.BAt σ₁ t a ∧ VG.Proof.MlDsa.Arm.Sample.Ball.BAt σ₂ t b) (fun n => ?_) 264)
    (fun a b hab => ⟨0, by decide, rfl, hab⟩) (fun _ _ h => h)
  refine RelCT.mono (P := fun a b => ∃ t, t < 264 ∧ n = 264 - t ∧ VG.Proof.MlDsa.Arm.Sample.Ball.BAt σ₁ t a ∧ VG.Proof.MlDsa.Arm.Sample.Ball.BAt σ₂ t b)
    (RelCT.exists_ fun t => ?_) (fun _ _ hab => hab) (fun _ _ h => h)
  by_cases ht : t < 264
  · by_cases hn : n = 264 - t
    · refine RelCT.mono (P := fun a b => VG.Proof.MlDsa.Arm.Sample.Ball.BAt σ₁ t a ∧ VG.Proof.MlDsa.Arm.Sample.Ball.BAt σ₂ t b) (VG.Proof.MlDsa.Arm.Sample.Ball.body_ct two ht) (fun _ _ hab => hab.2.2)
        fun a b ⟨⟨i₁, z₁⟩, ⟨i₂, z₂⟩⟩ => ⟨?_, fun e => ?_, fun e => ?_⟩
      · show some (!a.z) = some (!b.z); rw [z₁, z₂]
      · have : t + 1 = 264 := by
          have e' : (!a.z) = false := Option.some.inj e
          rw [z₁] at e'; simpa using e'
        rw [this] at i₁ i₂; exact ⟨i₁, i₂⟩
      · have : t + 1 ≠ 264 := by
          have e' : (!a.z) = true := Option.some.inj e
          rw [z₁] at e'; simpa using e'
        exact ⟨264 - (t + 1), by omega, t + 1, by omega, rfl, i₁, i₂⟩
    · exact RelCT.of_false fun _ _ hab => hn hab.2.1
  · exact RelCT.of_false fun _ _ hab => ht hab.1

/-! ## The whole function -/

theorem pro_ct : RelCT isa (fun a b => a = σ₁ ∧ b = σ₂)
    (.block (.ldrSp .r12 0 :: pro .r12 .r3 (.reg .r2) (.reg .r1) .r0))
    fun a b => J0 (VG.Proof.MlDsa.Arm.Sample.Ball.spOf σ₁) σ₁ a ∧ J0 (VG.Proof.MlDsa.Arm.Sample.Ball.spOf σ₂) σ₂ b := by
  refine relW ?_ fun a b h => ⟨by rw [h.1]; exact pro_ball two.p₁.ok rfl (by simp) rfl rfl rfl two.p₁.arg,
    by rw [h.2]; exact pro_ball two.p₂.ok rfl (by simp) rfl rfl rfl two.p₂.arg⟩
  show RelCT isa _ (.block ([.ldrSp .r12 0] ++ pro .r12 .r3 (.reg .r2) (.reg .r1) .r0)) _
  refine VG.Proof.MlDsa.Arm.Sample.Ball.relct_append (R := fun a b => a = σ₁.setReg .r12 (stackArg σ₁ 0) ∧ b = σ₂.setReg .r12 (stackArg σ₂ 0))
    (VG.Proof.MlDsa.Arm.Sample.Ball.relct_ldrSp (fun a b h => by rw [h.1, h.2, two.sp]) |>.wp (F₁ := fun s => s = σ₁.setReg .r12 (stackArg σ₁ 0))
      (F₂ := fun s => s = σ₂.setReg .r12 (stackArg σ₂ 0))
      (fun a b h => ⟨by rw [h.1]; exact VG.Proof.MlDsa.Arm.Sample.Ball.ldrSp_ok σ₁ two.p₁.arg, by rw [h.2]; exact VG.Proof.MlDsa.Arm.Sample.Ball.ldrSp_ok σ₂ two.p₂.arg⟩)
      |>.mono (fun _ _ h => h) fun _ _ h => h.2) ?_
  refine taintRel [.r0, .r1, .r2, .r3, .r12] (fun a b h r hr => ?_) (by taint_decide)
  rw [h.1, h.2]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [gpr_setReg_of_ne _ _ (by decide), gpr_setReg_of_ne _ _ (by decide)]; exact two.r0
  · rw [gpr_setReg_of_ne _ _ (by decide), gpr_setReg_of_ne _ _ (by decide)]; exact two.r1
  · rw [gpr_setReg_of_ne _ _ (by decide), gpr_setReg_of_ne _ _ (by decide)]; exact two.r2
  · rw [gpr_setReg_of_ne _ _ (by decide), gpr_setReg_of_ne _ _ (by decide)]; exact two.r3
  · rw [gpr_setReg_self, gpr_setReg_self]; exact two.scr

theorem all_ct : RelCT isa (fun a b => a = σ₁ ∧ b = σ₂) Impl.MlDsa.Arm.Sample.sampleInBall fun _ _ => True := by
  have hP := two.P_eq
  have ok₂ : SpOk (VG.Proof.MlDsa.Arm.Sample.Ball.spOf σ₁) σ₂ := hP ▸ two.p₂.ok
  refine RelCT.seq (VG.Proof.MlDsa.Arm.Sample.Ball.pro_ct two) ?_
  refine RelCT.seq (R := fun a b => J6 136 272 (VG.Proof.MlDsa.Arm.Sample.Ball.spOf σ₁) σ₁ a ∧ J6 136 272 (VG.Proof.MlDsa.Arm.Sample.Ball.spOf σ₂) σ₂ b)
    ((sponge_ct two.p₁.ok ok₂ two.sp (rate := 136) (outlen := 272) (by decide) (by decide) (by decide) (by decide)
      (by taint_decide) (by taint_decide) (by taint_decide)).mono (fun a b h => ⟨h.1, hP ▸ h.2⟩)
      fun a b h => ⟨h.1, hP ▸ h.2⟩) ?_
  refine RelCT.seq (R := fun a b => VG.Proof.MlDsa.Arm.Sample.Ball.ZDone σ₁ a ∧ VG.Proof.MlDsa.Arm.Sample.Ball.ZDone σ₂ b) (relW (taintRel [.r5] (fun a b h r hr => by
      rw [List.mem_singleton] at hr; subst hr; rw [h.1.env.r5, h.2.env.r5, hP]) (by taint_decide))
    fun a b h => ⟨VG.Proof.MlDsa.Arm.Sample.Ball.zero_ok two.p₁.ok h.1, VG.Proof.MlDsa.Arm.Sample.Ball.zero_ok two.p₂.ok h.2⟩) ?_
  have t₁ : VG.Proof.MlDsa.Arm.Sample.Ball.tau σ₁ ≤ 256 := by have := two.p₁.tau_le; omega
  have t₂ : VG.Proof.MlDsa.Arm.Sample.Ball.tau σ₂ ≤ 256 := by have := two.p₂.tau_le; omega
  refine RelCT.seq (RelCT.seq (R := fun a b => VG.Proof.MlDsa.Arm.Sample.Ball.BAt σ₁ 0 a ∧ VG.Proof.MlDsa.Arm.Sample.Ball.BAt σ₂ 0 b) (relW (taintRel [.r6, .r7]
      (fun a b h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h.1.env.r6, h.2.env.r6, hP]
        · rw [h.1.r7, h.2.r7, two.r2]) (by taint_decide))
    fun a b h => ⟨VG.Proof.MlDsa.Arm.Sample.Ball.setup_ok two.p₁.ok t₁ h.1, VG.Proof.MlDsa.Arm.Sample.Ball.setup_ok two.p₂.ok t₂ h.2⟩) (VG.Proof.MlDsa.Arm.Sample.Ball.loop_ct two)) ?_
  exact taintRel [.r6] (fun a b h r hr => by
    rw [List.mem_singleton] at hr; subst hr; rw [h.1.env.r6, h.2.env.r6, hP]) (by taint_decide)

end

/-! ## Verified -/

theorem pre_of {s : State} (h : (Spec.MlDsa.sampleInBallContract Arm.abi 8).pre s) : VG.Proof.MlDsa.Arm.Sample.Ball.Pre s := by
  sig_pre [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h8, -, hrd, hwr, d1, d2, d3, -, -, b1, b2, b3, -, f1, f2, f3, hb⟩ := h
  simp only [Spec.MlDsa.ballParams, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hb
  exact ⟨⟨by rw [hrd]; exact List.mem_cons.mpr (.inl rfl), hwr, d1, d2, d3, b1, b2, b3, f1, (s.gpr .r1).isLt, f2, f3, h8⟩,
    ⟨_, by rw [hrd]; exact List.mem_append_left _ (List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inl rfl)))),
      Region.contains_self _ _⟩, by simp only [VG.Proof.MlDsa.Arm.Sample.Ball.tau]; omega, by simp only [VG.Proof.MlDsa.Arm.Sample.Ball.tau]; omega⟩

theorem post_of {s₀ s : State}
    (h0 : s.gpr .r0 = (if (ballFold (VG.Proof.MlDsa.Arm.Sample.Ball.tau s₀) (VG.Proof.MlDsa.Arm.Sample.Ball.X s₀)).2 = 256 then 1 else 0))
    (hc : (ballFold (VG.Proof.MlDsa.Arm.Sample.Ball.tau s₀) (VG.Proof.MlDsa.Arm.Sample.Ball.X s₀)).2 = 256 →
      PolyIs s.mem (State.addr (s₀.gpr .r3)) (toRq (ballFold (VG.Proof.MlDsa.Arm.Sample.Ball.tau s₀) (VG.Proof.MlDsa.Arm.Sample.Ball.X s₀)).1)) :
    (Spec.MlDsa.sampleInBallContract Arm.abi 8).post s₀ s := by
  sig_post [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val]
  rw [setWidth_append32, h0]
  by_cases hf : (ballFold (VG.Proof.MlDsa.Arm.Sample.Ball.tau s₀) (VG.Proof.MlDsa.Arm.Sample.Ball.X s₀)).2 = 256
  · rw [ifT hf]
    obtain ⟨hred, hpoly⟩ := hc hf
    exact ⟨fun _ => hred, .inl ⟨rfl, { Spec.MlDsa.minBounds with ball := 272 }, by
      show Option.map toRq (Spec.MlDsa.sampleInBall (VG.Proof.MlDsa.Arm.Sample.Ball.tau s₀) 272 (VG.Proof.MlDsa.Arm.Sample.Ball.B s₀)) =
        some (Spec.MlDsa.polyAt s.mem (State.addr (s₀.gpr .r3)))
      rw [sampleInBall_some _ (by decide) hf]
      exact congrArg some hpoly.symm⟩⟩
  · rw [ifF hf]
    exact ⟨fun h1 => absurd h1 (by decide), .inr ⟨rfl, by
      show Option.map toRq (Spec.MlDsa.sampleInBall (VG.Proof.MlDsa.Arm.Sample.Ball.tau s₀) 221 (VG.Proof.MlDsa.Arm.Sample.Ball.B s₀)) = none
      rw [sampleInBall_none _ (B := 272) (by decide) (by decide) hf]; rfl⟩⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 32 | .r2 => 39 | .r3 => 0x2000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x30 else 0
  rd := [⟨0x1000, 32⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

end VG.Proof.MlDsa.Arm.Sample.Ball

namespace VG.Proof.MlDsa.Arm.Sample

open VG VG.Arm
open Ball

theorem sampleInBall_verified :
    Verified Arm.target Impl.MlDsa.Arm.Sample.sampleInBall (Spec.MlDsa.sampleInBallContract Arm.abi 8) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, h0, hc, hpres⟩ := VG.Proof.MlDsa.Arm.Sample.Ball.correct (VG.Proof.MlDsa.Arm.Sample.Ball.pre_of hs)
    exact ⟨t, s', he, hpres, VG.Proof.MlDsa.Arm.Sample.Ball.post_of h0 hc⟩
  · sig_pub [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at hpub
    obtain ⟨hsp, hb, h0, h1, h2, h3, hs⟩ := hpub
    have two : VG.Proof.MlDsa.Arm.Sample.Ball.Two s₁ s₂ := ⟨VG.Proof.MlDsa.Arm.Sample.Ball.pre_of h₁, VG.Proof.MlDsa.Arm.Sample.Ball.pre_of h₂, hsp, h0, h1, h2, h3, hs,
      (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hb⟩
    exact (VG.Proof.MlDsa.Arm.Sample.Ball.all_ct two s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨VG.Proof.MlDsa.Arm.Sample.Ball.satState, ?_⟩
    sig_sat_check [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]

end VG.Proof.MlDsa.Arm.Sample

end
