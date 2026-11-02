module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.Sample.Pro
public import VerifiedGarbage.Proof.MlDsa.Sample.ExpandMask
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.MlKem.RISCV64.Sample
import VerifiedGarbage.Proof.MlKem.RISCV64.Common
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.MlDsa.Sample.LeWord
import VerifiedGarbage.Proof.MlDsa.Sample.LeNat
import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.Contracts
import VerifiedGarbage.Proof.MlDsa.Sample.Ball
import VerifiedGarbage.Proof.MlKem.RISCV64.SampleCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Sample.Pro
meta import VerifiedGarbage.Proof.MlDsa.Sample.ExpandMask
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Sample
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Common
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.MRun
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.MlDsa.Sample.LeWord
meta import VerifiedGarbage.Proof.MlDsa.Sample.LeNat
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.Contracts
meta import VerifiedGarbage.Proof.MlDsa.Sample.Ball
meta import VerifiedGarbage.Proof.MlKem.RISCV64.SampleCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.SigEval
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelCT

/-!
# ML-DSA on RISC-V: `vg_mldsa_sample_in_ball`

As on PPC64LE (`Proof/MlDsa/PPC64LE/Sample/BallLoop.lean`, `Ball.lean`,
`BallCT.lean`). A call is described by `spOf σ` (`c̃`, its length, `scratch`
and `c`), `τ` is the low 32 bits of `a2`, and the XOF output is `X σ`,
`H(c̃, 272)`. The function runs in pieces: the prologue (`J0`, with `s7` =
`a2`, of which only `subw` reads the low 32 bits), the sponge (`J6`), the
zeroing of `c` (`zero_ok`, `ZDone`; `c` is kept as the words of its
coefficients modulo `q`, `CStored`), the setup of the loop, which loads the
sign bits (`setup_ok`, with `readW_leNat`), and the 264 iterations of the
loop. Iteration `t` starts from `BAt σ t`: the polynomial and `i` (in `a2`,
and `a1` at `c[i]`) that `bFold` computes from the first `t` bytes after the
sign bits, and the sign bits not yet used in `a6` (`Sg`). Its pieces are
`pieceA` (`i < 256`?), `tryA` (the byte `j`, and `j ≤ i`?), `setOk`
(`c[i] ← c[j]`, `c[j] ← ±1`) and `pieceC` (the step); afterwards `c` and `i`
are what `ballFold` computes (`correct`).

Constant time but for `c̃` (`all_ct`): two runs whose `c̃` (the declared
leak), `len`, `τ`, pointers and stack pointer agree (`Two`) leak the same:
the prologue, the zeroing and the blocks around the loop by the taint
analysis, the sponge by `sponge_ct`, and the loop, whose branches and
addresses depend on the SHAKE256 output, by relating the two runs iteration
by iteration (`body_ct`). `s7` holds all of `a2`, whose upper bits may
differ between the runs: only the setup reads it, and the setup's addresses
depend only on `s11`. `sampleInBall_verified` is `Verified`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Sample.Ball

open VG VG.RISCV64
open VG.Proof.MlDsa.RISCV64.Sample
open VG.Impl.MlDsa.RISCV64.Sample
open VG.Impl.Sha3.RISCV64.Stream (mov)
open VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.RISCV64 (ptr_add ptr_succ count_sub count_nz wp_loop_nz)
open VG.Proof.MlKem.RISCV64.Sample (toNat_setWidth8)
open VG.Spec.MlDsa (Zq q H IPoly n ofInt toRq)
open VG.Proof.MlDsa (coeffAt PolyIs)
open VG.Spec.Sha3 (bytesAt rates)
open VG.Proof.MlDsa.RISCV64.Pack (relct_noMem)
open VG.Proof.MlKem.RISCV64.Sample (taint_block relct_wp)

/-- The call, from the entry state: `ctilde = a0`, `len = a1`, `c = a3`,
`scratch = a4`. -/
abbrev spOf (σ : State) : Sp := ⟨σ.gpr .a0, (σ.gpr .a1).toNat, σ.gpr .a4, σ.gpr .a3⟩

/-- `τ`, the low 32 bits of `a2`. -/
abbrev tau (σ : State) : Nat := ((σ.gpr .a2).setWidth 32).toNat

/-- `c̃`. -/
abbrev B (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .a0) (σ.gpr .a1).toNat

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
abbrev Sg (σ : State) (i : Nat) (s : State) : Prop := (s.gpr .a6).toNat = Wn σ / 2 ^ (i - i0 σ)

/-- A word of `c` is aligned. -/
theorem c_al {σ : State} (hp : SpOk (spOf σ) σ) (k : Nat) : (coeffAddr (spOf σ).a k).toNat % 4 = 0 :=
  VG.Proof.MlKem.RISCV64.align4_add hp.alA k

/-! ## Zeroing -/

/-- After `k` iterations of the zeroing loop. -/
structure ZAt (σ : State) (k : Nat) (s : State) : Prop where
  env : Env (spOf σ) σ s
  s7 : s.gpr .s7 = σ.gpr .a2
  out : bytesAt s.mem ((spOf σ).at' 840) 272 = X σ
  t2 : s.gpr .t2 = 0
  a1 : s.gpr .a1 = (spOf σ).a + BitVec.ofNat 64 (4 * k)
  a3 : s.gpr .a3 = BitVec.ofNat 64 (256 - k)
  zero : ∀ j < k, coeffAt s.mem (spOf σ).a j = 0

/-- After the zeroing. -/
structure ZDone (σ : State) (s : State) : Prop where
  env : Env (spOf σ) σ s
  s7 : s.gpr .s7 = σ.gpr .a2
  out : bytesAt s.mem ((spOf σ).at' 840) 272 = X σ
  st : CStored s.mem (spOf σ).a (Vector.replicate n 0)

section
variable {σ : State} (hp : SpOk (spOf σ) σ)
include hp

/-- The output is not written by stores to `c`. -/
theorem out_frame {m m' : Mem} (hf : Frame [(spOf σ).aR] m m') :
    bytesAt m' ((spOf σ).at' 840) 272 = bytesAt m ((spOf σ).at' 840) 272 :=
  MlKem.bytesAt_frame hf (fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact (hp.a_scr.sub_right (sub_scr (a := 840) (n := 272) (by decide))).symm) (by decide)

theorem zBody_ok {k : Nat} (hk : k < 256) {s : State} (h : ZAt σ k s) :
    WP isa (.block [.store .w .t2 .a1 0, .addi .a1 .a1 4, .addi .a3 .a3 (-1)]) s fun s' =>
      ZAt σ (k + 1) s' ∧ (s'.gpr .a3 != 0) = decide (k + 1 ≠ 256) := by
  have cA := coeff_contains (spOf σ).a (i := k) hk
  have iA : InRegions s.wr ((spOf σ).a + BitVec.ofNat 64 (4 * k)) 4 :=
    ⟨(spOf σ).aR, by rw [h.env.wr, hp.wr]; simp, cA⟩
  have alA := c_al hp k
  have g1 := h.a1
  have hk' : WP isa (.block [.store .w .t2 .a1 0, .addi .a1 .a1 4, .addi .a3 .a3 (-1)]) s fun t =>
      t.mem = s.mem.writeW ((spOf σ).a + BitVec.ofNat 64 (4 * k)) ((s.gpr .t2).setWidth 32) ∧
      t.gpr .a1 = (spOf σ).a + BitVec.ofNat 64 (4 * k) + BitVec.ofNat 64 4 ∧
      t.gpr .a3 = s.gpr .a3 - BitVec.ofNat 64 1 ∧
      (∀ r, r ≠ .a1 → r ≠ .a3 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
    mrun [g1, iA, alA]
    intro r h1 h3
    simp only [h1, h3, ite_false]
  refine WP.mono hk' fun t ⟨m, r1, r3, rr, rd, wr, sp⟩ => ?_
  have hf : Frame [(spOf σ).aR] s.mem t.mem := by
    rw [m]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ cA
  refine ⟨⟨h.env.step hp hf (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact .inr (.inl fun _ h => h))
    (fun r hr => rr r (by rintro rfl; exact absurd hr (by decide)) (by rintro rfl; exact absurd hr (by decide)))
    rd wr sp, (rr _ (by decide) (by decide)).trans h.s7, ?_, (rr _ (by decide) (by decide)).trans h.t2,
    by rw [r1, ptr_succ], by rw [r3, h.a3]; exact count_sub hk, fun j hj => ?_⟩, ?_⟩
  · rw [out_frame hp hf]; exact h.out
  · rw [m, coeffAt_writeW _ _ (by omega_arith) hk, h.t2]
    by_cases e : k = j
    · rw [ifT e]; rfl
    · rw [ifF e]; exact h.zero j (by omega_arith)
  · rw [r3, h.a3, count_sub hk]; exact count_nz hk (by decide)

/-- The zeroing loop, from what the sponge leaves. -/
theorem zero_ok {s₀ s : State} (h : J6 136 272 (spOf σ) σ s₀ s) (h7 : s₀.gpr .s7 = σ.gpr .a2) :
    WP isa bZero s (ZDone σ) := by
  have g10 := h.j0.env.s10
  have hk : WP isa (.block [.li .t2 0, mov .a1 .s10, .li .a3 256]) s fun t =>
      t.gpr .t2 = 0 ∧ t.gpr .a1 = (spOf σ).a + BitVec.ofNat 64 (4 * 0) ∧
      t.gpr .a3 = BitVec.ofNat 64 (256 - 0) ∧ (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
    mrun [mov, g10, preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]
    rfl
  refine WP.seq (WP.mono hk fun s1 ⟨r12, r4, r6, gp, m, rd, wr, sp⟩ => ?_)
  refine wp_loop_nz (ZAt σ) (N := 256) (by decide) (fun k hk s h => zBody_ok hp hk h)
    (fun s h => ⟨h.env, h.s7, h.out, fun k hk => ?_⟩) ⟨h.j0.env.regs hp m gp rd wr sp,
      by rw [gp _ (by decide), h.gp _ (by decide), h7], by rw [m, h.out]; exact (H_eq _ _).symm, r12, r4, r6,
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

theorem sgn_val' (x : BitVec 64) {b : Bool} (hb : x.toNat % 2 = 1 ↔ b = true) :
    ((x <<< 63 >>> 63) * BitVec.ofNat 64 8380415 + BitVec.ofNat 64 1).setWidth 32 =
      if b then BitVec.ofNat 32 8380416 else 1 := by
  rw [sgn_val]
  by_cases h : x.toNat % 2 = 1
  · rw [ifT h, ifT (hb.mp h)]
  · rw [ifF h, ifF (fun e => h (hb.mpr e))]

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
  a0 : s.gpr .a0 = (spOf σ).scr + BitVec.ofNat 64 (848 + t)
  a1 : s.gpr .a1 = coeffAddr (spOf σ).a (St σ t).2
  a2 : s.gpr .a2 = BitVec.ofNat 64 (St σ t).2
  sg : Sg σ (St σ t).2 s
  a3 : s.gpr .a3 = BitVec.ofNat 64 (264 - t)
  a4 : s.gpr .a4 = BitVec.ofNat 64 8380415
  st : CStored s.mem (spOf σ).a (St σ t).1

section
variable {σ : State} (hp : SpOk (spOf σ) σ)
include hp

/-- `BAt` after code that writes no memory and only `a5`, `a7`, `t1`, `t2`. -/
theorem BAt.keep {t : Nat} {s s' : State} (h : BAt σ t s) (hm : s'.mem = s.mem)
    (g : ∀ r, r ≠ .a5 → r ≠ .a7 → r ≠ .t1 → r ≠ .t2 → s'.gpr r = s.gpr r) (rd : s'.rd = s.rd)
    (wr : s'.wr = s.wr) (sp : s'.sp = s.sp) : BAt σ t s' := by
  have gp : ∀ r ∈ preserved, s'.gpr r = s.gpr r := fun r hr =>
    g r (by rintro rfl; exact absurd hr (by decide)) (by rintro rfl; exact absurd hr (by decide))
      (by rintro rfl; exact absurd hr (by decide)) (by rintro rfl; exact absurd hr (by decide))
  exact ⟨h.env.regs hp hm gp rd wr sp, by rw [hm]; exact h.out,
    (g _ (by decide) (by decide) (by decide) (by decide)).trans h.a0,
    (g _ (by decide) (by decide) (by decide) (by decide)).trans h.a1,
    (g _ (by decide) (by decide) (by decide) (by decide)).trans h.a2,
    by show _ = _; rw [g _ (by decide) (by decide) (by decide) (by decide)]; exact h.sg,
    (g _ (by decide) (by decide) (by decide) (by decide)).trans h.a3,
    (g _ (by decide) (by decide) (by decide) (by decide)).trans h.a4, by rw [hm]; exact h.st⟩

end

/-- After the test of `i`. -/
structure M1 (σ : State) (t : Nat) (s : State) : Prop where
  bat : BAt σ t s
  z : (s.gpr .t2 == 0) = decide (256 ≤ (St σ t).2)

/-- After the test of the byte `j`, if `i < 256`. -/
structure T1 (σ : State) (t : Nat) (s : State) : Prop where
  bat : BAt σ t s
  lt : (St σ t).2 < 256
  a5 : s.gpr .a5 = BitVec.ofNat 64 (Xb σ t).toNat
  z : (s.gpr .t1 == 0) = decide ((Xb σ t).toNat ≤ (St σ t).2)

/-- After the coefficients of iteration `t`. -/
structure M2 (σ : State) (t : Nat) (s : State) : Prop where
  env : Env (spOf σ) σ s
  out : bytesAt s.mem ((spOf σ).at' 840) 272 = X σ
  a0 : s.gpr .a0 = (spOf σ).scr + BitVec.ofNat 64 (848 + t)
  a1 : s.gpr .a1 = coeffAddr (spOf σ).a (St σ (t + 1)).2
  a2 : s.gpr .a2 = BitVec.ofNat 64 (St σ (t + 1)).2
  sg : Sg σ (St σ (t + 1)).2 s
  a3 : s.gpr .a3 = BitVec.ofNat 64 (264 - t)
  a4 : s.gpr .a4 = BitVec.ofNat 64 8380415
  st : CStored s.mem (spOf σ).a (St σ (t + 1)).1

/-- `M2` when iteration `t` changes nothing. -/
theorem M2.of_same {σ : State} {t : Nat} {s : State} (l : BAt σ t s) (hst : St σ (t + 1) = St σ t) : M2 σ t s :=
  ⟨l.env, l.out, l.a0, by rw [hst]; exact l.a1, by rw [hst]; exact l.a2, by rw [hst]; exact l.sg, l.a3, l.a4,
    by rw [hst]; exact l.st⟩

section
variable {σ : State} (hp : SpOk (spOf σ) σ)
include hp

theorem pieceA {t : Nat} {s : State} (h : BAt σ t s) :
    WP isa (.block [.addi .t2 .a2 (-256), .shift .srl .d .t2 .t2 63]) s (M1 σ t) := by
  have hk : WP isa (.block [.addi .t2 .a2 (-256), .shift .srl .d .t2 .t2 63]) s fun t =>
      t.gpr .t2 = (s.gpr .a2 - BitVec.ofNat 64 256) >>> 63 ∧
      (∀ r, r ≠ .t2 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
    mrun []
    intro r h12
    simp only [h12, ite_false]
  refine WP.mono hk fun s' ⟨g12, g, m, rd, wr, sp⟩ => ⟨h.keep hp m (fun r _ _ _ d => g r d) rd wr sp, ?_⟩
  have := St_le σ t
  rw [g12, h.a2, sgn_beq (by omega_arith) (by decide)]

theorem tryA {t : Nat} (ht : t < 264) {s : State} (h : M1 σ t s) (hz : (s.gpr .t2 == 0) = false) :
    WP isa (.block [.load .b .a5 .a0 0, .sub .t1 .a2 .a5, .shift .srl .d .t1 .t1 63]) s (T1 σ t) := by
  have hl : (St σ t).2 < 256 := by
    have := h.z; rw [hz] at this; simp at this; omega_arith
  have l := h.bat
  have iB : InRegions (s.rd ++ s.wr) ((spOf σ).scr + BitVec.ofNat 64 (848 + t)) 1 :=
    inScrRd hp l.env.wr (a := 848 + t) (by omega_arith)
  have hb : s.mem ((spOf σ).scr + BitVec.ofNat 64 (848 + t)) = Xb σ t := by
    have := congrArg (fun L => L.getD (8 + t) 0) l.out
    rw [MlKem.bytesAt_getD _ _ (by omega_arith), ptr_add, show 840 + (8 + t) = 848 + t by omega_arith] at this
    exact this
  have g0 := l.a0
  have hk : WP isa (.block [.load .b .a5 .a0 0, .sub .t1 .a2 .a5, .shift .srl .d .t1 .t1 63]) s fun u =>
      u.gpr .a5 = (s.mem ((spOf σ).scr + BitVec.ofNat 64 (848 + t))).setWidth 64 ∧
      u.gpr .t1 = (s.gpr .a2 - (s.mem ((spOf σ).scr + BitVec.ofNat 64 (848 + t))).setWidth 64) >>> 63 ∧
      (∀ r, r ≠ .a5 → r ≠ .t1 → u.gpr r = s.gpr r) ∧ u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧
      u.sp = s.sp := by
    mrun [g0, iB]
    intro r h8 h11
    simp only [h8, h11, ite_false]
  refine WP.mono hk fun s' ⟨g8, g11, g, m, rd, wr, sp⟩ =>
    ⟨l.keep hp m (fun r a _ c _ => g r a c) rd wr sp, hl, by rw [g8, hb, byte_ofNat], ?_⟩
  have := (Xb σ t).isLt
  rw [g11, hb, byte_ofNat, l.a2, sgn_beq (by omega_arith) (by omega_arith)]

omit hp in
/-- The sign bit of `i`, from the sign bits not yet used. -/
theorem sign_bit {i : Nat} (hτ : tau σ ≤ 256) (hi0 : i0 σ ≤ i) {s : State} (hs : Sg σ i s) :
    ((s.gpr .a6).toNat % 2 = 1) = ((signs (X σ)).getD (i + tau σ - 256) false = true) := by
  have e0 : i0 σ = 256 - tau σ := rfl
  rw [signs_getD, testBit_eq, show i + tau σ - 256 = i - i0 σ by omega_arith, hs, decide_eq_true_iff]

omit hp in
theorem bSet_ok (s : State) {Ai Aj : Addr} (hAi : s.gpr .a1 = Ai) (hAj : s.gpr .s10 + s.gpr .a5 <<< 2 = Aj)
    (iJ : InRegions (s.rd ++ s.wr) Aj 4) (wI : InRegions s.wr Ai 4) (wJ : InRegions s.wr Aj 4)
    (aI : Ai.toNat % 4 = 0) (aJ : Aj.toNat % 4 = 0) :
    WP isa (.block bSet) s fun u =>
      u.mem = (s.mem.writeW Ai (((s.mem.readW Aj 32).setWidth 64).setWidth 32)).writeW Aj
        ((s.gpr .a6 <<< 63 >>> 63 * s.gpr .a4 + BitVec.ofNat 64 1).setWidth 32) ∧
      u.gpr .a6 = s.gpr .a6 >>> 1 ∧ u.gpr .a1 = s.gpr .a1 + BitVec.ofNat 64 4 ∧
      u.gpr .a2 = s.gpr .a2 + BitVec.ofNat 64 1 ∧
      (∀ r, r ≠ .a1 → r ≠ .a2 → r ≠ .a6 → r ≠ .a7 → r ≠ .t1 → r ≠ .t2 → u.gpr r = s.gpr r) ∧
      u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp := by
  mrun [bSet, hAj, hAi, iJ, wI, wJ, aI, aJ]
  intro r a b c d e f
  simp only [a, b, c, d, e, f, ite_false]

/-- `c[i] ← c[j]`, `c[j] ← ±1`, `i` incremented. -/
theorem setOk (hτ : tau σ ≤ 256) {t : Nat} (ht : t < 264) {s : State} (h : T1 σ t s)
    (hz : (s.gpr .t1 == 0) = true) : WP isa (.block bSet) s (M2 σ t) := by
  have l := h.bat
  have hi := h.lt
  have hj : (Xb σ t).toNat ≤ (St σ t).2 := by have := h.z; rw [hz] at this; simpa using this
  have hAj : s.gpr .s10 + s.gpr .a5 <<< 2 = coeffAddr (spOf σ).a (Xb σ t).toNat := by
    rw [l.env.s10, h.a5, shl2 (by have := (Xb σ t).isLt; omega_arith)]
  have inI : (spOf σ).aR.Contains (coeffAddr (spOf σ).a (St σ t).2) 4 := coeff_contains _ hi
  have inJ : (spOf σ).aR.Contains (coeffAddr (spOf σ).a (Xb σ t).toNat) 4 := coeff_contains _ (by omega_arith)
  have wA : (spOf σ).aR ∈ s.wr := by rw [l.env.wr, hp.wr]; simp
  refine WP.mono (bSet_ok s l.a1 hAj ⟨_, List.mem_append_right _ wA, inJ⟩ ⟨_, wA, inI⟩ ⟨_, wA, inJ⟩
    (c_al hp _) (c_al hp _)) fun u ⟨m, g9, g4, g5, g, rd, wr, sp⟩ => ?_
  have hst := St_succ σ ht
  rw [bStep, ifT hi, ifF (show ¬ (Xb σ t).toNat > (St σ t).2 by omega_arith)] at hst
  have hf : Frame [(spOf σ).aR] s.mem u.mem := by
    rw [m]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ inI).writeW (List.mem_singleton_self _) _ inJ
  have gk : ∀ r, r ≠ .a1 → r ≠ .a2 → r ≠ .a6 → r ≠ .a7 → r ≠ .t1 → r ≠ .t2 → u.gpr r = s.gpr r := g
  have ge := St_ge σ t
  refine ⟨l.env.step hp hf (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact .inr (.inl fun _ h => h))
    (fun r hr => gk r (by rintro rfl; exact absurd hr (by decide)) (by rintro rfl; exact absurd hr (by decide))
      (by rintro rfl; exact absurd hr (by decide)) (by rintro rfl; exact absurd hr (by decide))
      (by rintro rfl; exact absurd hr (by decide)) (by rintro rfl; exact absurd hr (by decide)))
    rd wr sp, ?_, (gk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans l.a0,
    ?_, ?_, ?_, (gk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans l.a3,
    (gk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans l.a4, ?_⟩
  · rw [out_frame hp hf]; exact l.out
  · rw [g4, l.a1, hst]; exact ptr_succ _ 4 _
  · rw [g5, l.a2, hst, BitVec.ofNat_add]
  · rw [hst]
    show (u.gpr .a6).toNat = _
    have hs := l.sg
    simp only [Sg] at hs
    rw [g9, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hs, Nat.div_div_eq_div_mul, ← Nat.pow_succ,
      show (St σ t).2 + 1 - i0 σ = (St σ t).2 - i0 σ + 1 by omega_arith]
  · intro k hk
    have hsb := Iff.of_eq (sign_bit hτ ge l.sg)
    rw [hst, m, l.a4, sgn_val' _ hsb, sgn_word, coeffAt_writeW _ _ hk (by omega_arith), coeffAt_writeW _ _ hk hi,
      ipoly_set!_get _ _ (by simp only [n]; omega_arith), ipoly_set!_get _ _ (by simp only [n]; omega_arith)]
    by_cases ejk : (Xb σ t).toNat = k
    · rw [ifT ejk, ifT ejk]
    · rw [ifF ejk, ifF ejk]
      by_cases eik : (St σ t).2 = k
      · subst eik; rw [ifT rfl, ifT rfl, setWidth_32_64_32, ← coeffAt_eq, l.st _ (by omega_arith)]
      · rw [ifF eik, ifF eik]; exact l.st k hk

theorem tryB (hτ : tau σ ≤ 256) {t : Nat} (ht : t < 264) {s : State} (h : T1 σ t s) :
    WP isa (.ite (.zero .t1) (.block bSet) (.block [])) s (M2 σ t) := by
  refine WP.ite _ (Steps.eval_zero _ _) (fun e => setOk hp hτ ht h e) (fun e => ?_)
  have hj : (St σ t).2 < (Xb σ t).toNat := by
    have := h.z; rw [e] at this; exact Nat.lt_of_not_le (of_decide_eq_false this.symm)
  have hst := St_succ σ ht
  rw [bStep, ifT h.lt, ifT hj] at hst
  exact WP.block_nil (M2.of_same h.bat hst)

theorem pieceB (hτ : tau σ ≤ 256) {t : Nat} (ht : t < 264) {s : State} (h : M1 σ t s) :
    WP isa (.ite (.zero .t2) (.block []) bTry) s (M2 σ t) := by
  refine WP.ite _ (Steps.eval_zero _ _) (fun e => ?_)
    (fun e => WP.seq (WP.mono (tryA hp ht h e) fun _ h1 => tryB hp hτ ht h1))
  have hl : (St σ t).2 = 256 := by
    have := h.z; rw [e] at this; simp at this; have := St_le σ t; omega_arith
  exact WP.block_nil (M2.of_same h.bat (by rw [St_succ σ ht, bStep_full hl]))

theorem pieceC {t : Nat} (ht : t < 264) {s : State} (h : M2 σ t s) :
    WP isa (.block [.addi .a0 .a0 1, .addi .a3 .a3 (-1)]) s fun s' =>
      BAt σ (t + 1) s' ∧ (s'.gpr .a3 != 0) = decide (t + 1 ≠ 264) := by
  have hk : WP isa (.block [.addi .a0 .a0 1, .addi .a3 .a3 (-1)]) s fun s' =>
      s'.gpr .a0 = s.gpr .a0 + BitVec.ofNat 64 1 ∧ s'.gpr .a3 = s.gpr .a3 - BitVec.ofNat 64 1 ∧
      (∀ r, r ≠ .a0 → r ≠ .a3 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
    mrun []
    intro r a b
    simp only [a, b, ite_false]
  refine WP.mono hk fun s' ⟨r3, r6, g, m, rd, wr, sp⟩ => ⟨⟨?_, by rw [m]; exact h.out, ?_,
    (g _ (by decide) (by decide)).trans h.a1, (g _ (by decide) (by decide)).trans h.a2,
    by show _ = _; rw [g _ (by decide) (by decide)]; exact h.sg, ?_, (g _ (by decide) (by decide)).trans h.a4,
    by rw [m]; exact h.st⟩, ?_⟩
  · exact h.env.regs hp m (fun r hr => g r (by rintro rfl; exact absurd hr (by decide))
      (by rintro rfl; exact absurd hr (by decide))) rd wr sp
  · rw [r3, h.a0, ptr_add, Nat.add_assoc]
  · rw [r6, h.a3]; exact count_sub ht
  · rw [r6, h.a3, count_sub ht]; exact count_nz ht (by decide)

/-- An iteration. -/
theorem body_ok (hτ : tau σ ≤ 256) {t : Nat} (ht : t < 264) {s : State} (h : BAt σ t s) :
    WP isa bBody s fun s' => BAt σ (t + 1) s' ∧ (s'.gpr .a3 != 0) = decide (t + 1 ≠ 264) :=
  WP.seq (WP.mono (pieceA hp h) fun _ h1 => WP.seq (WP.mono (pieceB hp hτ ht h1) fun _ h2 => pieceC hp ht h2))

end

/-! ## The setup of the loop -/

/-- The first `i`, `256 - τ`, by `subw`. -/
theorem i0_val (x : BitVec 64) (h : (x.setWidth 32).toNat ≤ 256) :
    sext32 ((BitVec.ofNat 64 256).setWidth 32 - x.setWidth 32) =
      BitVec.ofNat 64 (256 - (x.setWidth 32).toNat) := by
  have e : (BitVec.ofNat 64 256).setWidth 32 - x.setWidth 32 = BitVec.ofNat 32 (256 - (x.setWidth 32).toNat) :=
    BitVec.eq_of_toNat_eq (by
      simp only [BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at h ⊢
      omega)
  rw [e]
  apply BitVec.eq_of_toNat_eq
  have hm : (BitVec.ofNat 32 (256 - (x.setWidth 32).toNat)).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt, BitVec.toNat_ofNat]; omega
  rw [sext32, BitVec.signExtend_eq_setWidth_of_msb_false hm, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat]
  omega

/-- `bSetup` before loading `q - 2`. -/
abbrev bSetup₁ : List Instr :=
  [.load .d .a6 .s11 840, .li .a2 256, .subw .a2 .a2 .s7, .shift .sll .d .a1 .a2 2, .add .a1 .s10 .a1,
    .addi .a0 .s11 848, .li .a3 264]

theorem bSetup_eq : bSetup = bSetup₁ ++ VG.Impl.MlDsa.RISCV64.Pack.loadB .a4 8380415 := rfl

section
variable {σ : State} (hp : SpOk (spOf σ) σ) (hτ : tau σ ≤ 256)
include hp hτ

theorem setup_ok {s : State} (h : ZDone σ s) : WP isa (.block bSetup) s (BAt σ 0) := by
  have g10 := h.env.s10
  have g11 := h.env.s11
  have g7 := h.s7
  have i9 : InRegions (s.rd ++ s.wr) ((spOf σ).scr + BitVec.ofNat 64 840) 8 := inScrRd hp h.env.wr (by decide)
  have a9 := scr_al hp (P := spOf σ) (o := 840) (by decide)
  have hk : WP isa (.block bSetup₁) s fun u =>
      u.gpr .a6 = s.mem.readW ((spOf σ).scr + BitVec.ofNat 64 840) 64 ∧
      u.gpr .a2 = sext32 ((BitVec.ofNat 64 256).setWidth 32 - (σ.gpr .a2).setWidth 32) ∧
      u.gpr .a1 = (spOf σ).a + sext32 ((BitVec.ofNat 64 256).setWidth 32 - (σ.gpr .a2).setWidth 32) <<< 2 ∧
      u.gpr .a0 = (spOf σ).scr + BitVec.ofNat 64 848 ∧ u.gpr .a3 = BitVec.ofNat 64 264 ∧
      (∀ r ∈ preserved, u.gpr r = s.gpr r) ∧ u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp := by
    mrun [g10, g11, g7, i9, a9, preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]
  rw [bSetup_eq, WP.block_append_iff]
  refine WP.mono hk fun u ⟨g6, g2, g1, g0, g3, gp, m, rd, wr, sp⟩ => ?_
  refine WP.mono (VG.Proof.MlDsa.RISCV64.Pack.WP.withSp (VG.Proof.MlDsa.RISCV64.Pack.loadB_ok .a4 (B := 8380415) (by decide) u))
    fun v ⟨⟨⟨g4, m'⟩, k⟩, sp'⟩ => ?_
  have kk : ∀ r, r ≠ .a4 → v.gpr r = u.gpr r := fun r hr => k.gpr (by simpa using hr)
  have gp' : ∀ r ∈ preserved, v.gpr r = s.gpr r := fun r hr =>
    (kk r (by rintro rfl; exact absurd hr (by decide))).trans (gp r hr)
  have e0 := i0_val (σ.gpr .a2) hτ
  have hSt : St σ 0 = (Vector.replicate n 0, i0 σ) := rfl
  refine ⟨h.env.regs hp (m'.trans m) gp' (k.2.1.trans rd) (k.2.2.trans wr) (sp'.trans sp),
    by rw [m', m]; exact h.out, by rw [kk _ (by decide)]; exact g0, ?_, ?_, ?_,
    by rw [kk _ (by decide)]; exact g3, g4, by rw [m', m, hSt]; exact h.st⟩
  · rw [kk _ (by decide), g1, e0, hSt, shl2 (by omega)]
  · rw [kk _ (by decide), g2, e0, hSt]
  · show (v.gpr .a6).toNat = _
    rw [kk _ (by decide), hSt, Nat.sub_self, Nat.pow_zero, Nat.div_one, g6, readW_leNat _ _ (X σ) fun k hk => by
      have := congrArg (fun L => L.getD k 0) h.out
      rw [MlKem.bytesAt_getD _ _ (by omega)] at this
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
      s'.gpr .a0 = (if (ballFold (tau σ) (X σ)).2 = 256 then 1 else 0) ∧
      ((ballFold (tau σ) (X σ)).2 = 256 →
        PolyIs s'.mem (σ.gpr .a3) (toRq (ballFold (tau σ) (X σ)).1)) ∧
      abiPreserved σ s' :=
  WP.mono (retEpi_ok hp h.env h.a2 (St_le _ _)) fun s' ⟨h3, hm, ha⟩ => ⟨by rw [h3, St_all], fun _ => by
    rw [hm]
    have hst := h.st
    rw [St_all] at hst
    refine polyIs_of_coeffAt fun i hi => ?_
    rw [hst i hi, getElem!_pos _ i hi, getElem!_pos _ i hi]
    simp only [toRq, Vector.getElem_map], ha⟩

/-- The function, from an entry state whose regions are those of a call. -/
theorem correct {σ : State} (hp : Pre σ) : WP isa Impl.MlDsa.RISCV64.Sample.sampleInBall σ fun s' =>
    s'.gpr .a0 = (if (ballFold (tau σ) (X σ)).2 = 256 then 1 else 0) ∧
      ((ballFold (tau σ) (X σ)).2 = 256 →
        PolyIs s'.mem (σ.gpr .a3) (toRq (ballFold (tau σ) (X σ)).1)) ∧
      abiPreserved σ s' := by
  have hτ : tau σ ≤ 256 := by have := hp.tau_le; omega
  exact WP.seq (WP.mono (pro_ball hp.ok rfl (by simp) rfl rfl) fun s₁ ⟨j1, h7⟩ =>
    WP.seq (WP.mono (sponge_ok hp.ok (rate := 136) (outlen := 272) (by decide) (by decide) j1)
      fun _ h2 => WP.seq (WP.mono (zero_ok hp.ok h2 h7) fun _ h3 => WP.seq (WP.mono (loop_ok hp.ok hτ h3)
        fun _ h4 => end_ok hp.ok h4))))


/-- Any code, by the taint analysis from the registers `rs`. -/
theorem taint_prog {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hsp : ∀ a b, P a b → a.sp = b.sp) (hP : ∀ a b, P a b → ∀ r ∈ rs, a.gpr r = b.gpr r)
    {hc : VG.Taint.Hint VG.RISCV64.taint.T}
    (h : (VG.RISCV64.taint.check (Taint.ofRegs rs) c hc).isSome = true) :
    RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := VG.RISCV64.taint) (Taint.ofRegs rs)
    (fun a b hab => ⟨hsp a b hab, fun r hr => hP a b hab r (Taint.mem_ofRegs.mp hr)⟩) h

/-- Two runs, from entry states that agree on the public data. -/
structure Two (σ₁ σ₂ : State) : Prop where
  p₁ : Pre σ₁
  p₂ : Pre σ₂
  sp : σ₁.sp = σ₂.sp
  a0 : σ₁.gpr .a0 = σ₂.gpr .a0
  a1 : σ₁.gpr .a1 = σ₂.gpr .a1
  a2 : (σ₁.gpr .a2).setWidth 32 = (σ₂.gpr .a2).setWidth 32
  a3 : σ₁.gpr .a3 = σ₂.gpr .a3
  a4 : σ₁.gpr .a4 = σ₂.gpr .a4
  B : B σ₁ = B σ₂

section
variable {σ₁ σ₂ : State} (two : Two σ₁ σ₂)
include two

theorem Two.P_eq : spOf σ₂ = spOf σ₁ := by simp only [spOf, two.a0, two.a1, two.a3, two.a4]
theorem Two.X_eq : X σ₁ = X σ₂ := by simp only [X, two.B]
theorem Two.tau_eq : tau σ₁ = tau σ₂ := by simp only [tau, two.a2]
theorem Two.St_eq (t : Nat) : St σ₁ t = St σ₂ t := by simp only [St, i0, two.X_eq, two.tau_eq]
theorem Two.Xb_eq (t : Nat) : Xb σ₁ t = Xb σ₂ t := by simp only [Xb, two.X_eq]

theorem Two.bsp {t t' : Nat} {a b : State} (ha : BAt σ₁ t a) (hb : BAt σ₂ t' b) : a.sp = b.sp := by
  rw [ha.env.sp, hb.env.sp, two.sp]

/-! ## The loop -/

theorem body_ct {t : Nat} (ht : t < 264) :
    RelCT isa (fun a b => BAt σ₁ t a ∧ BAt σ₂ t b) bBody fun a b =>
      (BAt σ₁ (t + 1) a ∧ (a.gpr .a3 != 0) = decide (t + 1 ≠ 264)) ∧
      (BAt σ₂ (t + 1) b ∧ (b.gpr .a3 != 0) = decide (t + 1 ≠ 264)) := by
  have hp₁ := two.p₁.ok
  have hp₂ := two.p₂.ok
  have hτ₁ : tau σ₁ ≤ 256 := by have := two.p₁.tau_le; omega_arith
  have hτ₂ : tau σ₂ ≤ 256 := by have := two.p₂.tau_le; omega_arith
  have eP := two.P_eq
  refine relct_wp ?_ fun a b hab => ⟨body_ok hp₁ hτ₁ ht hab.1, body_ok hp₂ hτ₂ ht hab.2⟩
  refine RelCT.seq (R := fun a b => M1 σ₁ t a ∧ M1 σ₂ t b) (relct_wp (relct_noMem rfl) fun a b hab =>
    ⟨pieceA hp₁ hab.1, pieceA hp₂ hab.2⟩) ?_
  refine RelCT.seq (R := fun _ _ => True) ?_ (relct_noMem rfl)
  refine RelCT.ite (fun a b h => by rw [Steps.eval_zero, Steps.eval_zero, h.1.z, h.2.z, two.St_eq])
    (relct_noMem rfl) ?_
  have zb : ∀ {a b : State}, M1 σ₁ t a → M1 σ₂ t b → (a.gpr .t2 == 0) = false → (b.gpr .t2 == 0) = false :=
    fun ha hb e => by rw [hb.z, ← two.St_eq, ← ha.z]; exact e
  refine RelCT.seq (R := fun a b => T1 σ₁ t a ∧ T1 σ₂ t b) (relct_wp (taint_block [.a0]
      (fun a b h => two.bsp h.1.1.bat h.1.2.bat) (fun a b h r hr => by
        rw [List.mem_singleton] at hr; subst hr; rw [h.1.1.bat.a0, h.1.2.bat.a0, eP]) (by taint_decide))
    fun a b h => by
      have za : (a.gpr .t2 == 0) = false := by rw [Steps.eval_zero] at h; exact Option.some.inj h.2
      exact ⟨tryA hp₁ ht h.1.1 za, tryA hp₂ ht h.1.2 (zb h.1.1 h.1.2 za)⟩) ?_
  refine RelCT.ite (fun a b h => by rw [Steps.eval_zero, Steps.eval_zero, h.1.z, h.2.z, two.St_eq, two.Xb_eq]) ?_
    (relct_noMem rfl)
  refine taint_block [.a1, .a5, .s10] (fun a b h => two.bsp h.1.1.bat h.1.2.bat) (fun a b h r hr => ?_)
    (by taint_decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h.1.1.bat.a1, h.1.2.bat.a1, eP, two.St_eq]
  · rw [h.1.1.a5, h.1.2.a5, two.Xb_eq]
  · rw [h.1.1.bat.env.s10, h.1.2.bat.env.s10, eP]

theorem loop_ct :
    RelCT isa (fun a b => BAt σ₁ 0 a ∧ BAt σ₂ 0 b) (.loop bBody (.nonzero .a3)) fun a b =>
      BAt σ₁ 264 a ∧ BAt σ₂ 264 b := by
  refine RelCT.mono (RelCT.loop (M := isa) (body := bBody) (c := .nonzero .a3)
    (Q := fun a b => BAt σ₁ 264 a ∧ BAt σ₂ 264 b)
    (fun n a b => ∃ t, t < 264 ∧ n = 264 - t ∧ BAt σ₁ t a ∧ BAt σ₂ t b) (fun n => ?_) 264)
    (fun a b hab => ⟨0, by decide, rfl, hab⟩) (fun _ _ h => h)
  refine RelCT.mono (P := fun a b => ∃ t, t < 264 ∧ n = 264 - t ∧ BAt σ₁ t a ∧ BAt σ₂ t b)
    (RelCT.exists_ fun t => ?_) (fun _ _ hab => hab) (fun _ _ h => h)
  by_cases ht : t < 264
  · by_cases hn : n = 264 - t
    · refine RelCT.mono (P := fun a b => BAt σ₁ t a ∧ BAt σ₂ t b) (body_ct two ht) (fun _ _ hab => hab.2.2)
        fun a b ⟨⟨i₁, z₁⟩, ⟨i₂, z₂⟩⟩ => ⟨?_, fun e => ?_, fun e => ?_⟩
      · rw [Steps.eval_nonzero, Steps.eval_nonzero, z₁, z₂]
      · have : t + 1 = 264 := by
          have e' : (a.gpr .a3 != 0) = false := by rw [Steps.eval_nonzero] at e; exact Option.some.inj e
          rw [z₁] at e'; simpa using e'
        rw [this] at i₁ i₂; exact ⟨i₁, i₂⟩
      · have : t + 1 ≠ 264 := by
          have e' : (a.gpr .a3 != 0) = true := by rw [Steps.eval_nonzero] at e; exact Option.some.inj e
          rw [z₁] at e'; simpa using e'
        exact ⟨264 - (t + 1), by omega_arith, t + 1, by omega_arith, rfl, i₁, i₂⟩
    · exact RelCT.of_false fun _ _ hab => hn hab.2.1
  · exact RelCT.of_false fun _ _ hab => ht hab.1

/-! ## The whole function -/

theorem all_ct : RelCT isa (fun a b => a = σ₁ ∧ b = σ₂) Impl.MlDsa.RISCV64.Sample.sampleInBall fun _ _ => True := by
  have hp₁ := two.p₁.ok
  have hp₂ := two.p₂.ok
  have eP := two.P_eq
  have hp₂' : SpOk (spOf σ₁) σ₂ := eP ▸ hp₂
  have hτ₁ : tau σ₁ ≤ 256 := by have := two.p₁.tau_le; omega_arith
  have hτ₂ : tau σ₂ ≤ 256 := by have := two.p₂.tau_le; omega_arith
  -- the prologue
  refine RelCT.seq (R := fun (a b : State) => (J0 (spOf σ₁) σ₁ a ∧ a.gpr .s7 = σ₁.gpr .a2) ∧
      (J0 (spOf σ₁) σ₂ b ∧ b.gpr .s7 = σ₂.gpr .a2)) (relct_wp (pro_ball_ct
    (fun a b hab => by rw [hab.1, hab.2]; exact two.sp) fun a b hab => by rw [hab.1, hab.2]; exact two.a4)
    fun a b hab => ⟨?_, ?_⟩) ?_
  · rw [hab.1]; exact pro_ball hp₁ rfl (by simp) rfl rfl
  · rw [hab.2]; exact pro_ball hp₂' two.a0.symm (by rw [← two.a1]; simp) two.a3.symm two.a4.symm
  -- the sponge
  refine RelCT.seq (R := fun (a b : State) => (∃ x, J6 136 272 (spOf σ₁) σ₁ x a ∧ x.gpr .s7 = σ₁.gpr .a2) ∧
      (∃ y, J6 136 272 (spOf σ₁) σ₂ y b ∧ y.gpr .s7 = σ₂.gpr .a2))
    (relct_wp (RelCT.mono (sponge_ct hp₁ hp₂' two.sp (by decide) (by decide)) (fun a b h => ⟨h.1.1, h.2.1⟩)
      fun _ _ h => h) fun a b hab =>
      ⟨WP.mono (sponge_ok hp₁ (by decide) (by decide) hab.1.1) fun _ x => ⟨_, x, hab.1.2⟩,
        WP.mono (sponge_ok hp₂' (by decide) (by decide) hab.2.1) fun _ x => ⟨_, x, hab.2.2⟩⟩) ?_
  -- the zeroing
  refine RelCT.seq (R := fun a b => ZDone σ₁ a ∧ ZDone σ₂ b) (relct_wp (taint_prog [.s10]
      (fun a b h => by
        obtain ⟨⟨x, ha, _⟩, ⟨y, hb, _⟩⟩ := h; rw [ha.j0.env.sp, hb.j0.env.sp, two.sp])
      (fun a b h r hr => by
        obtain ⟨⟨x, ha, _⟩, ⟨y, hb, _⟩⟩ := h
        rw [List.mem_singleton] at hr; subst hr; rw [ha.j0.env.s10, hb.j0.env.s10]) (by taint_decide))
    fun a b ⟨⟨x, ha, h₁⟩, ⟨y, hb, h₂⟩⟩ => ⟨zero_ok hp₁ ha h₁, zero_ok hp₂ (by rw [eP]; exact hb) h₂⟩) ?_
  -- the loop
  refine RelCT.seq (R := fun a b => BAt σ₁ 264 a ∧ BAt σ₂ 264 b) (RelCT.seq (R := fun a b => BAt σ₁ 0 a ∧ BAt σ₂ 0 b)
    (relct_wp (taint_block [.s11] (fun a b h => by rw [h.1.env.sp, h.2.env.sp, two.sp])
      (fun a b h r hr => by
        rw [List.mem_singleton] at hr; subst hr; rw [h.1.env.s11, h.2.env.s11, eP]) (by taint_decide))
      fun a b h => ⟨setup_ok hp₁ hτ₁ h.1, setup_ok hp₂ hτ₂ h.2⟩) (loop_ct two)) ?_
  -- the end
  exact retEpi_ct (fun a b hab => two.bsp hab.1 hab.2) fun a b hab => by
    rw [hab.1.env.s11, hab.2.env.s11, eP]

end

/-! ## `Verified` -/

theorem pre_of {s : State} (h : (Proof.MlDsa.sampleInBallContract RISCV64.abi 1168).pre s) : Pre s := by
  sig_pre [Proof.MlDsa.sampleInBallContract, Proof.MlDsa.sampleInBallSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨al, sp, h1, h2, d1, d2, d3, b1, b2, b3, _, f2, f3, hb, alA, alS⟩ := h
  simp only [Proof.MlDsa.ballParams, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hb
  exact ⟨⟨by rw [h1]; exact List.mem_singleton_self _, h2, d1, d2, d3, b1, b2, b3, (s.gpr .a1).isLt, f2, f3, al,
    sp, alA, alS⟩, by simp only [tau]; omega_arith⟩

theorem post_of {s₀ s : State}
    (h0 : s.gpr .a0 = (if (ballFold (tau s₀) (X s₀)).2 = 256 then 1 else 0))
    (hc : (ballFold (tau s₀) (X s₀)).2 = 256 → PolyIs s.mem (s₀.gpr .a3) (toRq (ballFold (tau s₀) (X s₀)).1)) :
    (Proof.MlDsa.sampleInBallContract RISCV64.abi 1168).post s₀ s := by
  sig_post [Proof.MlDsa.sampleInBallContract, Proof.MlDsa.sampleInBallSig, RISCV64.abi, RISCV64.argRegs]
  rw [h0]
  by_cases hf : (ballFold (tau s₀) (X s₀)).2 = 256
  · rw [ifT hf]
    obtain ⟨hred, hpoly⟩ := hc hf
    exact ⟨fun _ => hred, .inl ⟨rfl, { Spec.MlDsa.minBounds with ball := 272 }, by
      show Option.map toRq (Spec.MlDsa.sampleInBall (tau s₀) 272 (B s₀)) =
        some (Proof.MlDsa.polyAt s.mem (s₀.gpr .a3))
      rw [sampleInBall_some _ (by decide) hf]
      exact congrArg some hpoly.symm⟩⟩
  · rw [ifF hf]
    exact ⟨fun h1 => absurd h1 (by decide), .inr ⟨rfl, by
      show Option.map toRq (Spec.MlDsa.sampleInBall (tau s₀) 221 (B s₀)) = none
      rw [sampleInBall_none _ (B := 272) (by decide) (by decide) hf]; rfl⟩⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 32 | .a2 => 39 | .a3 => 0x2000 | .a4 => 0x3000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 32⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

end VG.Proof.MlDsa.RISCV64.Sample.Ball

namespace VG.Proof.MlDsa.RISCV64.Sample

open VG VG.RISCV64
open Ball

theorem sampleInBall_verified :
    Verified RISCV64.target Impl.MlDsa.RISCV64.Sample.sampleInBall
      (Proof.MlDsa.sampleInBallContract RISCV64.abi 1168) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, h3, hc, hpres⟩ := correct (pre_of hs)
    exact ⟨t, s', he, hpres, post_of h3 hc⟩
  · sig_pub [Proof.MlDsa.sampleInBallContract, Proof.MlDsa.sampleInBallSig, RISCV64.abi, RISCV64.argRegs] at hpub
    obtain ⟨hsp, hb, h3, h4, h5, h6, h7⟩ := hpub
    exact (all_ct ⟨pre_of h₁, pre_of h₂, hsp, h3, h4, h5, h6, h7,
      (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hb⟩ s₁ s₂ t₁ t₂ s₁' s₂'
      ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.sampleInBallContract, Proof.MlDsa.sampleInBallSig, RISCV64.abi, RISCV64.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | decide +kernel

end VG.Proof.MlDsa.RISCV64.Sample
