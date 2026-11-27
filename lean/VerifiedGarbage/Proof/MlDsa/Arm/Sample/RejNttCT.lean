module

import VerifiedGarbage.Proof.MlDsa.Arm.Sample.Pro
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlDsa.Arm.Sample.Pro
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
import VerifiedGarbage.Proof.MlDsa.Arm.Arith.AddSub
public import VerifiedGarbage.Proof.MlDsa.Arm.Arith.Saving
public import VerifiedGarbage.Impl.MlDsa.Arm.Arith.Mul
public import VerifiedGarbage.Proof.MlDsa.Arm.Arith.Basic
meta import VerifiedGarbage.Proof.MlDsa.Arm.Arith.AddSub
meta import VerifiedGarbage.Proof.MlDsa.Arm.Arith.Saving
meta import VerifiedGarbage.Impl.MlDsa.Arm.Arith.Mul
meta import VerifiedGarbage.Proof.MlDsa.Arm.Arith.Basic
public import VerifiedGarbage.Proof.MlDsa.Arm.Arith.NttLoop
meta import VerifiedGarbage.Proof.MlDsa.Arm.Arith.NttLoop
public import VerifiedGarbage.Impl.MlDsa.Arm.Sample.RejNtt
public import VerifiedGarbage.Proof.MlDsa.Sample.RejNtt
public import VerifiedGarbage.Proof.MlDsa.Arm.Sample.Sponge
meta import VerifiedGarbage.Impl.MlDsa.Arm.Sample.RejNtt
meta import VerifiedGarbage.Proof.MlDsa.Sample.RejNtt
meta import VerifiedGarbage.Proof.MlDsa.Arm.Sample.Sponge

/-! ### `MlDsa.Arm.Sample.RejNtt`, which only this module used -/

section

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_rej_ntt_poly`, correctness

The function runs in pieces: the prologue (`J0`), the sponge, whose output is
`G(ρ, 1008)` (`J6`), and the loop, iteration `t` of which starts from `LAt σ
t`, with the coefficients `rnFold` samples from the first `3t` bytes of output
stored. An iteration loads the value of its 3 bytes and tests `j ≥ 256`
(`pieceA`), stores it if `j < 256` and it is less than `q` (`pieceB`, what
`rnStep` does), and steps (`pieceC`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Sample.RejNtt

open VG VG.Arm
open VG.Proof.MlKem.Arm
open VG.Proof.MlDsa.Arm.Sample
open VG.Impl.MlDsa.Arm.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q G)
open VG.Proof.MlDsa (PolyIs)
open VG.Spec.Sha3 (bytesAt)

/-- The call, from the entry state: `seed = r0`, `a = r1`, `scratch = r2`. -/
abbrev spOf (σ : State) : Sp := ⟨σ.gpr .r0, 34, σ.gpr .r2, σ.gpr .r1, 0⟩

/-- The seed. -/
abbrev B (σ : State) : List Byte := bytesAt σ.mem (State.addr (σ.gpr .r0)) 34

/-- The XOF output. -/
abbrev X (σ : State) : List Byte := G (B σ) 1008

/-- Byte `i` of the XOF output. -/
abbrev Xb (σ : State) (i : Nat) : Byte := (X σ).getD i 0

/-- The coefficients sampled after `t` iterations. -/
abbrev Lt (σ : State) (t : Nat) : List Zq := rnFold [] ((X σ).take (3 * t))

/-- The value of 3 bytes, as the code computes it. -/
def rnw (b₀ b₁ b₂ : Byte) : BitVec 32 :=
  b₀.setWidth 32 + (b₂.setWidth 32 <<< 25) >>> 9 + b₁.setWidth 32 <<< 8

theorem rnw_toNat (b₀ b₁ b₂ : Byte) : (rnw b₀ b₁ b₂).toNat = rnZ b₀ b₁ b₂ := by
  have h0 := b₀.isLt
  have h1 := b₁.isLt
  have h2 := b₂.isLt
  unfold rnw rnZ
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft,
    setWidth32_toNat, setWidth32_toNat, setWidth32_toNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    Nat.shiftLeft_eq]
  omega_using []

/-- The value of the 3 bytes of iteration `t`. -/
abbrev V (σ : State) (t : Nat) : BitVec 32 := rnw (Xb σ (3 * t)) (Xb σ (3 * t + 1)) (Xb σ (3 * t + 2))

theorem V_lt (σ : State) (t : Nat) : (V σ t).toNat < 2 ^ 23 := by
  rw [rnw_toNat]; unfold rnZ
  have := (Xb σ (3 * t)).isLt; have := (Xb σ (3 * t + 1)).isLt; have := (Xb σ (3 * t + 2)).isLt
  omega_using []

theorem X_length (σ : State) : (X σ).length = 1008 := G_length _ _

theorem take_add_three (L : List Byte) {i : Nat} (h : i + 3 ≤ L.length) :
    L.take (i + 3) = L.take i ++ [L.getD i 0, L.getD (i + 1) 0, L.getD (i + 2) 0] := by
  rw [List.take_add, List.drop_eq_getElem_cons (by omega_using [h]), List.drop_eq_getElem_cons (by omega_using [h]),
    List.drop_eq_getElem_cons (by omega_using [h])]
  simp only [List.take_succ_cons, List.take_zero, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show i < L.length by omega_using [h]), List.getElem?_eq_getElem (show i + 1 < L.length by omega_using [h]),
    List.getElem?_eq_getElem (show i + 2 < L.length by omega_using [h]), Option.getD_some]

theorem Lt_succ (σ : State) {t : Nat} (ht : t < 336) :
    Lt σ (t + 1) = rnStep (Lt σ t) (Xb σ (3 * t)) (Xb σ (3 * t + 1)) (Xb σ (3 * t + 2)) := by
  simp only [Lt]
  rw [show 3 * (t + 1) = 3 * t + 3 by omega_using [], take_add_three _ (by rw [X_length]; omega_using [ht]),
    rnFold_snoc _ (by rw [List.length_take, X_length]; omega_using [])]

theorem Lt_length_le (σ : State) (t : Nat) : (Lt σ t).length ≤ 256 := rnFold_length_le (by simp) _

/-- At the start of iteration `t`. -/
structure LAt (σ : State) (t : Nat) (s : State) : Prop where
  env : Env (spOf σ) σ s
  out : bytesAt s.mem ((spOf σ).at' 840) 1008 = X σ
  r0 : s.gpr .r0 = σ.gpr .r2 + BitVec.ofNat 32 (840 + 3 * t)
  r2 : s.gpr .r2 = BitVec.ofNat 32 (Lt σ t).length
  r3 : s.gpr .r3 = BitVec.ofNat 32 (1 * (336 - t))
  r7 : s.gpr .r7 = BitVec.ofNat 32 8380417
  st : Stored s.mem (spOf σ).A (Lt σ t)

/-- After the value of the 3 bytes and the test of `j`. -/
structure M1 (σ : State) (t : Nat) (s : State) : Prop where
  lat : LAt σ t s
  r10 : s.gpr .r10 = V σ t
  z : s.z = decide (256 ≤ (Lt σ t).length)

/-- After the test of the value, if `j < 256`. -/
structure T1 (σ : State) (t : Nat) (s : State) : Prop where
  lat : LAt σ t s
  r10 : s.gpr .r10 = V σ t
  len : (Lt σ t).length < 256
  z : s.z = decide (8380417 ≤ (V σ t).toNat)

/-- After the coefficient of iteration `t`. -/
structure M2 (σ : State) (t : Nat) (s : State) : Prop where
  env : Env (spOf σ) σ s
  out : bytesAt s.mem ((spOf σ).at' 840) 1008 = X σ
  r0 : s.gpr .r0 = σ.gpr .r2 + BitVec.ofNat 32 (840 + 3 * t)
  r2 : s.gpr .r2 = BitVec.ofNat 32 (Lt σ (t + 1)).length
  r3 : s.gpr .r3 = BitVec.ofNat 32 (1 * (336 - t))
  r7 : s.gpr .r7 = BitVec.ofNat 32 8380417
  st : Stored s.mem (spOf σ).A (Lt σ (t + 1))

/-- `LAt` after a block that writes no memory and keeps `r0`, `r2`, `r3`,
`r5`, `r6` and `r7`. -/
theorem LAt.same {σ s s' : State} {t : Nat} (h : LAt σ t s) (hm : s'.mem = s.mem)
    (g : ∀ r ∈ [Reg.r0, .r2, .r3, .r5, .r6, .r7], s'.gpr r = s.gpr r) (rd : s'.rd = s.rd) (wr : s'.wr = s.wr)
    (sp : s'.sp = s.sp) : LAt σ t s' :=
  ⟨h.env.same hm (g .r5 (by simp)) (g .r6 (by simp)) rd wr sp, by rw [hm]; exact h.out,
    (g .r0 (by simp)).trans h.r0, (g .r2 (by simp)).trans h.r2, (g .r3 (by simp)).trans h.r3,
    (g .r7 (by simp)).trans h.r7, by rw [hm]; exact h.st⟩

section
variable {σ : State} (hp : SpOk (spOf σ) σ)
include hp

/-- Byte `k` of iteration `t`. -/
theorem byte_ok {t : Nat} (ht : t < 336) {s : State} (h : LAt σ t s) {k : Nat} (hk : k < 3) :
    State.addr (s.gpr .r0 + BitVec.ofNat 32 k) = (spOf σ).at' (840 + (3 * t + k)) ∧
      InRegions (s.rd ++ s.wr) ((spOf σ).at' (840 + (3 * t + k))) 1 ∧
      s.mem ((spOf σ).at' (840 + (3 * t + k))) = Xb σ (3 * t + k) := by
  refine ⟨?_, inScrRd hp h.env (by omega_using [ht, hk]), ?_⟩
  · rw [h.r0, ptr_add_add32, show 840 + 3 * t + k = 840 + (3 * t + k) by omega_using []]; exact at_eq hp (by omega_using [ht, hk])
  · have := congrArg (fun L => L.getD (3 * t + k) 0) h.out
    rw [MlKem.bytesAt_getD _ _ (by omega_using [ht, hk]), add_ofNat_add] at this
    exact this

omit hp in
theorem load_ok (s : State) {A₀ A₁ A₂ : Addr} {b₀ b₁ b₂ : Byte}
    (a0 : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = A₀) (a1 : State.addr (s.gpr .r0 + BitVec.ofNat 32 1) = A₁)
    (a2 : State.addr (s.gpr .r0 + BitVec.ofNat 32 2) = A₂) (i0 : InRegions (s.rd ++ s.wr) A₀ 1)
    (i1 : InRegions (s.rd ++ s.wr) A₁ 1) (i2 : InRegions (s.rd ++ s.wr) A₂ 1) (v0 : s.mem A₀ = b₀)
    (v1 : s.mem A₁ = b₁) (v2 : s.mem A₂ = b₂) :
    WP isa (.block rnLoad) s fun s' => s'.gpr .r10 = rnw b₀ b₁ b₂ ∧
      (∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [rnLoad, rnw, a0, a1, a2, i0, i1, i2, v0, v1, v2, and_self, and_true, true_and]
  exact fun r h8 h9 h10 => by simp [h8, h9, h10]

theorem pieceA {t : Nat} (ht : t < 336) {s : State} (h : LAt σ t s) :
    WP isa (.block (rnLoad ++ jFull)) s (M1 σ t) := by
  obtain ⟨a0, i0, v0⟩ := byte_ok hp ht h (k := 0) (by decide)
  obtain ⟨a1, i1, v1⟩ := byte_ok hp ht h (k := 1) (by decide)
  obtain ⟨a2, i2, v2⟩ := byte_ok hp ht h (k := 2) (by decide)
  rw [Nat.add_zero] at v0
  rw [WP.block_append_iff]
  refine WP.mono (load_ok s a0 a1 a2 i0 i1 i2 v0 v1 v2) fun s1 ⟨g10, g1, m1, rd1, wr1, sp1⟩ => ?_
  have l1 : LAt σ t s1 := h.same m1 (fun r hr => g1 r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide) (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) rd1 wr1 sp1
  refine WP.mono (jFull_ok s1 l1.r2 (by have := Lt_length_le σ t; omega_using [this])) fun s2 ⟨z2, g2, m2, rd2, wr2, sp2⟩ =>
    ⟨l1.same m2 (fun r hr => g2 r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
      rd2 wr2 sp2, by rw [g2 _ (by decide), g10], z2⟩

omit hp in
theorem tryA {t : Nat} {s : State} (h : M1 σ t s) (hz : s.z = false) :
    WP isa (.block [.dp .sub .r11 .r10 (.reg .r7), .mov .r11 (.shifted .r11 .lsr 31), .cmp .r11 (.imm 0)]) s
      (T1 σ t) := by
  have hl : (Lt σ t).length < 256 := by
    have := h.z; rw [hz] at this; simp at this; omega_using [this]
  have hv := V_lt σ t
  refine WP.mono (sgn_ok s .r10 (.reg .r7) (y := BitVec.ofNat 32 8380417) (by simp [Op2.eval, h.lat.r7])
    (by rw [h.r10]; omega_using [hv]) (by decide)) fun s' ⟨z, g, m, rd, wr, sp⟩ => ⟨h.lat.same m (fun r hr => g r (by
      simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) rd wr sp,
    by rw [g _ (by decide), h.r10], hl, by rw [z, h.r10]; rfl⟩

omit hp in
theorem zw_V {σ : State} {t : Nat} (hq : (V σ t).toNat < q) : zw (Fin.ofNat q (V σ t).toNat) = V σ t := by
  apply BitVec.eq_of_toNat_eq
  rw [zw_toNat, Fin.val_ofNat, Nat.mod_eq_of_lt hq]

theorem tryB {t : Nat} (ht : t < 336) {s : State} (h : T1 σ t s) :
    WP isa (.ite .eq (.block []) (.block (storeJ .r10))) s (M2 σ t) := by
  have hstep := Lt_succ σ ht
  rw [rnStep, ifT (show (Lt σ t).length < 256 from h.len), ← rnw_toNat] at hstep
  refine WP.ite s.z rfl (fun e => ?_) (fun e => ?_)
  · -- rejected
    have hq : ¬ (V σ t).toNat < q := by
      have := h.z; rw [e] at this; simp at this; show ¬ _ < 8380417; omega_using [this]
    rw [ifF hq] at hstep
    have l := h.lat
    exact WP.block_nil ⟨l.env, l.out, l.r0, by rw [hstep]; exact l.r2, l.r3, l.r7, by rw [hstep]; exact l.st⟩
  · have hq : (V σ t).toNat < q := by
      have := h.z; rw [e] at this; simp at this; show _ < 8380417; omega_using [this]
    rw [ifT hq] at hstep
    have l := h.lat
    refine WP.mono (storeJ_stored hp l.env (by decide) l.r2 h.len l.st (x := Fin.ofNat q (V σ t).toNat)
      (by rw [h.r10, zw_V hq])) fun s' ⟨st, r2, g, _, he, hf⟩ => ⟨he, ?_, by rw [g _ (by decide) (by decide), l.r0],
        by rw [hstep]; exact r2, by rw [g _ (by decide) (by decide), l.r3], by rw [g _ (by decide) (by decide), l.r7],
        by rw [hstep]; exact st⟩
    rw [MlKem.bytesAt_frame hf (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact (hp.a_scr.sub_right (sub_scr (a := 840) (n := 1008) (by omega_using []))).symm) (by omega_using [])]
    exact l.out

theorem pieceB {t : Nat} (ht : t < 336) {s : State} (h : M1 σ t s) :
    WP isa (.ite .eq (.block []) rnTry) s (M2 σ t) := by
  refine WP.ite s.z rfl (fun e => ?_) (fun e => ?_)
  · -- `j = 256`: nothing changes
    have hl : (Lt σ t).length = 256 := by
      have := h.z; rw [e] at this; simp at this; have := Lt_length_le σ t; omega_arith
    have hstep : Lt σ (t + 1) = Lt σ t := by rw [Lt_succ σ ht, rnStep_full hl]
    have l := h.lat
    exact WP.block_nil ⟨l.env, l.out, l.r0, by rw [hstep]; exact l.r2, l.r3, l.r7, by rw [hstep]; exact l.st⟩
  · exact WP.seq (WP.mono (tryA h e) fun _ h1 => tryB hp ht h1)

omit hp in
theorem pieceC {t : Nat} (ht : t < 336) {s : State} (h : M2 σ t s) :
    WP isa (.block (step 3)) s fun s' => LAt σ (t + 1) s' ∧ s'.z = decide (t + 1 = 336) := by
  refine WP.mono (step_ok s (k := 3) (by decide)) fun s' ⟨r0, r3, z, g, m, rd, wr, sp⟩ =>
    ⟨⟨h.env.same m (g _ (by decide) (by decide)) (g _ (by decide) (by decide)) rd wr sp, by rw [m]; exact h.out,
      ?_, by rw [g _ (by decide) (by decide)]; exact h.r2, by rw [r3, h.r3]; exact count_sub (k := 1) ht,
      by rw [g _ (by decide) (by decide)]; exact h.r7, by rw [m]; exact h.st⟩, ?_⟩
  · rw [r0, h.r0, ptr_add_add32, show 840 + 3 * t + 3 = 840 + 3 * (t + 1) by omega_using []]
  · rw [z, h.r3]; exact count_z (k := 1) ht (by decide) (by decide)

/-- An iteration. -/
theorem body_ok {t : Nat} (ht : t < 336) {s : State} (h : LAt σ t s) :
    WP isa rnBody s fun s' => LAt σ (t + 1) s' ∧ s'.z = decide (t + 1 = 336) :=
  WP.seq (WP.mono (pieceA hp ht h) fun _ h1 => WP.seq (WP.mono (pieceB hp ht h1) fun _ h2 => pieceC ht h2))

end


/-! ## The whole function -/

theorem init_ok (s : State) :
    WP isa (.block [.dp .add .r0 .r6 (.imm 840), .mov .r2 (.imm 0), .mov .r3 (.imm 336), .movw .r7 0xE001,
      .movt .r7 0x7F]) s fun s' => s'.gpr .r0 = s.gpr .r6 + BitVec.ofNat 32 840 ∧ s'.gpr .r2 = BitVec.ofNat 32 0 ∧
        s'.gpr .r3 = BitVec.ofNat 32 336 ∧ s'.gpr .r7 = BitVec.ofNat 32 8380417 ∧ s'.gpr .r5 = s.gpr .r5 ∧
        s'.gpr .r6 = s.gpr .r6 ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [and_self, and_true, true_and]
  rfl

section
variable {σ : State} (hp : SpOk (spOf σ) σ)
include hp

omit hp in
theorem lat0 {s : State} (h : J6 168 1008 (spOf σ) σ s) : WP isa (.block [.dp .add .r0 .r6 (.imm 840),
    .mov .r2 (.imm 0), .mov .r3 (.imm 336), .movw .r7 0xE001, .movt .r7 0x7F]) s (LAt σ 0) :=
  WP.mono (init_ok s) fun s' ⟨r0, r2, r3, r7, g5, g6, m, rd, wr, sp⟩ =>
    ⟨h.env.same m g5 g6 rd wr sp, by rw [m, h.out]; exact (G_eq _ _).symm, by rw [r0, h.env.r6],
      by rw [r2]; rfl, by rw [r3], r7, by rw [m]; exact stored_nil _ _⟩

theorem loop_ok {s : State} (h : J6 168 1008 (spOf σ) σ s) : WP isa rnLoop s (LAt σ 336) :=
  WP.seq (WP.mono (lat0 h) fun _ h0 =>
    wp_loop_ne (LAt σ) (N := 336) (by decide) (fun t ht s h => body_ok hp ht h) (fun _ h => h) h0)

omit hp in
theorem Lt_all : Lt σ 336 = rnFold [] (X σ) := by
  simp only [Lt]; rw [List.take_of_length_le (by rw [X_length])]

theorem end_ok {s : State} (h : LAt σ 336 s) :
    WP isa (.block (retJ ++ epi)) s fun s' => s'.gpr .r0 = (if (rnFold [] (X σ)).length = 256 then 1 else 0) ∧
      ((rnFold [] (X σ)).length = 256 → PolyIs s'.mem (State.addr (σ.gpr .r1)) (toPoly (rnFold [] (X σ)))) ∧
      abiPreserved σ s' :=
  WP.mono (retEpi_ok hp h.env h.r2 (Lt_length_le _ _)) fun s' ⟨h0, hm, ha⟩ =>
    ⟨by rw [h0, Lt_all], fun hf => by rw [hm]; exact Lt_all ▸ stored_polyIs h.st (by rw [Lt_all]; exact hf),
      ha⟩

/-- The function, from an entry state whose regions are those of a call. -/
theorem correct : WP isa Impl.MlDsa.Arm.Sample.rejNTT σ fun s' =>
    s'.gpr .r0 = (if (rnFold [] (X σ)).length = 256 then 1 else 0) ∧
      ((rnFold [] (X σ)).length = 256 → PolyIs s'.mem (State.addr (σ.gpr .r1)) (toPoly (rnFold [] (X σ)))) ∧
      abiPreserved σ s' :=
  WP.seq (WP.mono (pro_rn hp rfl rfl rfl rfl rfl) fun _ h1 =>
    WP.seq (WP.mono (sponge_ok hp (rate := 168) (outlen := 1008) (by decide) (by decide) (by decide) (by decide) h1)
      fun _ h2 => WP.seq (WP.mono (loop_ok hp h2) fun _ h3 => end_ok hp h3)))

end

end VG.Proof.MlDsa.Arm.Sample.RejNtt

end

end

/-! ### `MlDsa.Arm.Arith.Mul`, which the modules that import this one used -/

section

/-! ### `MlDsa.Arm.Arith.NttInv`, which the modules that import this one used -/

section

/-! ### `MlDsa.Arm.Arith.Ntt`, which only this module used -/

section

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_ntt`

The table stored and the constants loaded (`pro_ok`); each of the first
seven layers is `layerF` on words (`lay_ok` with `bfly_core`, and `blkL_ok`
or `blkS_ok` for its blocks), which leaves words congruent to the
specification's (`layersF_rel`), and the last is `layerFC`, which leaves its
coefficients (`layerFC_val`, `ntt_split`), all in the frames that save
`r4`–`r10` (`wp_saving`). `LI`, `pro_ok`, `PreE` and `pre_entry` serve `NTT⁻¹`
too.
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Arith.Ntt

open VG VG.Arm VG.Impl.MlDsa.Arm.Arith
open VG.Spec.MlDsa (q n Poly Zq zetas)
open VG.Proof.MlDsa (coeffAt polyAt Reduced PolyIs)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.Arm.Arith.AddSub (reduced_zero)

section
variable (s : State)

abbrev pf : BitVec 32 := s.gpr .r0
abbrev ps : BitVec 32 := s.gpr .r1
abbrev F : Addr := State.addr (pf s)
abbrev S : Addr := State.addr (ps s)

end

/-- The precondition of both transforms, on entry. -/
structure PreE (s : State) : Prop where
  sp : 28 ≤ s.sp.toNat
  rd : s.rd = []
  wr : s.wr = [polyRegion (F s), polyRegion (S s)]
  fs : (polyRegion (F s)).Disjoint (polyRegion (S s))
  sF : (belowA s.sp 28).Disjoint (polyRegion (F s))
  sS : (belowA s.sp 28).Disjoint (polyRegion (S s))
  fitF : (pf s).toNat + 1024 ≤ 2 ^ 32
  fitS : (ps s).toNat + 1024 ≤ 2 ^ 32
  red : Reduced s.mem (F s)

/-- What the transforms need of the state after the pushes. -/
structure PreB (s : State) : Prop where
  wF : polyRegion (F s) ∈ s.wr
  wS : polyRegion (S s) ∈ s.wr
  fs : (polyRegion (F s)).Disjoint (polyRegion (S s))
  fitF : (pf s).toNat + 1024 ≤ 2 ^ 32
  fitS : (ps s).toNat + 1024 ≤ 2 ^ 32
  red : Reduced s.mem (F s)

theorem pre_entry {s s₁ : State} (hp : PreE s) (hE : Entry 28 s s₁) :
    PreB s₁ ∧ polyAt s₁.mem (F s₁) = polyAt s.mem (F s) ∧ F s₁ = F s ∧ S s₁ = S s := by
  have g := hE.gpr
  have eF : F s₁ = F s := by simp only [F, pf, g]
  have eS : S s₁ = S s := by simp only [S, ps, g]
  have dF : ∀ r ∈ [belowA s.sp 28], (polyRegion (F s)).Disjoint r := fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact hp.sF.symm
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, by rw [eF]; exact polyAt_frame hE.frame dF, eF, eS⟩
  · rw [eF]; exact hE.wr _ (by rw [hp.wr]; simp)
  · rw [eS]; exact hE.wr _ (by rw [hp.wr]; simp)
  · rw [eF, eS]; exact hp.fs
  · simp only [pf, g]; exact hp.fitF
  · simp only [ps, g]; exact hp.fitS
  · rw [eF]; exact reduced_frame hE.frame dF hp.red

/-- Between layers: the words `G` at `f`, the table `tab` at `scratch`,
entry `k` of the table at `r1`, `-q` in `r4` and `q` in `r5`, from the state
`s₁` after the pushes. -/
structure LI (tab : Nat → Nat) (s₁ : State) (G : LPoly) (k : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = pf s₁
  r1 : s.gpr .r1 = ps s₁ + BitVec.ofNat 32 (4 * k)
  r4 : s.gpr .r4 = Nw
  r5 : s.gpr .r5 = Qw
  poly : LP s.mem (F s₁) G
  tab : Tab tab s.mem (S s₁)
  frame : Frame [polyRegion (F s₁), polyRegion (S s₁)] s₁.mem s.mem
  keep : Keep [.r11, .lr] s₁ s

theorem LI.step {tab : Nat → Nat} {s₁ : State} {G G' : LPoly} {k k' : Nat} {s s' : State}
    (hI : LI tab s₁ G k s) (hP : LP s'.mem (F s₁) G') (hf : Frame [polyRegion (F s₁)] s.mem s'.mem)
    (h0 : s'.gpr .r0 = pf s₁) (h1 : s'.gpr .r1 = ps s₁ + BitVec.ofNat 32 (4 * k'))
    (hk : Keep [.r4, .r5, .r11, .lr] s s') (hd : (polyRegion (S s₁)).Disjoint (polyRegion (F s₁))) :
    LI tab s₁ G' k' s' :=
  ⟨h0, h1, (hk.gpr .r4 (by decide)).trans hI.r4, (hk.gpr .r5 (by decide)).trans hI.r5, hP,
    hI.tab.frame hf (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hd),
    hI.frame.trans (hf.mono (by simp)), hI.keep.trans (hk.mono (by decide))⟩

/-- The chain of zeta indices of the layers `ls` of `NTT`, from `k`. -/
def Chain : Nat → List Nat → Prop
  | _, [] => True
  | k, len :: ls => k = 128 / len ∧ Chain (256 / len) ls

/-- The zeta index after the layers `ls`, from `k`. -/
def chainEnd : Nat → List Nat → Nat
  | k, [] => k
  | _, len :: ls => chainEnd (256 / len) ls

theorem lens_fwd : ∀ len ∈ nttLens, 128 / len + 128 / len = 256 / len ∧ 256 / len ≤ 256 := by decide

theorem zetaTab_of : TabOf zetaTab zetas := fun k _ => zetaNat_eq k

theorem zetaTab_lt : ∀ k < 256, zetaTab k < q := fun k _ => zetaNat_lt k

/-- A layer of `NTT` whose blocks are `blk`, with the butterfly `op`. -/
theorem layF_ok {s₁ : State} (hp : PreB s₁) {blk : Prog isa} {op : Word → Word → Zq → Word × Word} {len : Nat}
    (hlen : len ∈ nttLens) (hblk : BlockOk blk op zetaTab zetas .add len (pf s₁) (ps s₁)) {G : LPoly}
    {s : State} (hI : LI zetaTab s₁ G (128 / len) s) :
    WP isa (nttLay blk len) s fun s' =>
      LI zetaTab s₁ (Lazy.layF (lblk op zetas) G len (fun c => 128 / len + c) (128 / len)) (256 / len) s' := by
  obtain ⟨h1, h2⟩ := lens_fwd len hlen
  refine WP.mono (lay_ok hblk hlen (fun c => 128 / len + c) (fun c hc => by omega_using [h1, h2, hc])
    (fun c _ => by
      simp only [nextZ, ite_true, BitVec.add_assoc, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl,
        ← BitVec.ofNat_add]
      congr 2)
    G s hI.r0 (by rw [hI.r1]; rfl) hI.r4 hI.r5 hI.poly (by rw [hI.keep.wr]; exact hp.wF)
    (by rw [hI.keep.wr]; exact List.mem_append_right _ hp.wS) hp.fs.symm hI.tab)
    fun s' ⟨hP, hf, h0, h1', hk'⟩ => hI.step hP hf h0 (by rw [h1', ← h1]) hk' hp.fs.symm

theorem lays_ok {s₁ : State} (hp : PreB s₁) (blk : Nat → Prog isa) :
    ∀ (ls : List Nat) (G : LPoly) (k : Nat) (s : State),
      (∀ len ∈ ls, len ∈ nttLens ∧ BlockOk (blk len) opF zetaTab zetas .add len (pf s₁) (ps s₁)) → Chain k ls →
      LI zetaTab s₁ G k s →
      WP isa (lays blk ls) s fun s' => LI zetaTab s₁ (ls.foldl layerF G) (chainEnd k ls) s'
  | [], _, _, _, _, _, hI => WP.block_nil hI
  | len :: ls, G, k, s, hls, ⟨hk, hc⟩, hI => by
    obtain ⟨hlen, hblk⟩ := hls len (List.mem_cons_self ..)
    exact WP.seq (WP.mono (layF_ok hp hlen hblk (hk ▸ hI)) fun s' hI' =>
      lays_ok hp blk ls _ (256 / len) s' (fun l hl => hls l (List.mem_cons_of_mem _ hl)) hc hI')

/-- The table `tab` to `scratch`, `-q` to `r4`, `q` to `r5`, and `r1` at
entry `k`. -/
theorem pro_ok {s : State} (hp : PreB s) (tab : Nat → Nat) (ht : ∀ k < 256, tab k < q) (d : BitVec 32) (k : Nat)
    (hd : BitVec.ofNat 32 (4 * k) = d) (he : encodable d = true) :
    WP isa (.block (storeTab tab 256 ++ loadNQ .r4 ++ loadQ .r5 ++ ([.dp .add .r1 .r1 (.imm d)] : List Instr))) s
      (LI tab s (lift (polyAt s.mem (F s))) k) := by
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (storeTab_ok tab ht s (zB := ps s) rfl hp.fitS hp.wS) fun s₁ ⟨ht₁, hf₁, k₁⟩ => ?_
  have e1 : s₁.gpr .r1 = ps s := k₁.gpr .r1 (by decide)
  have e0 : s₁.gpr .r0 = pf s := k₁.gpr .r0 (by decide)
  run_block [loadNQ, loadQ, e0, e1, he, loadNQ_val, loadQ_val]
  refine ⟨by simp [e0], by simp [hd], by simp, by simp, ?_, ht₁, hf₁.mono (by simp), ?_⟩
  · exact lp_lift (polyIs_frame hf₁ (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.fs)
      ⟨hp.red, rfl⟩)
  · exact ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [k₁.gpr _ (by decide : Reg.r11 ∈ _), k₁.gpr _ (by decide : Reg.lr ∈ _)],
      k₁.rd, k₁.wr, k₁.sp⟩

/-- `NTT`, as the code's three runs of layers. -/
theorem ntt_split (w : Poly) :
    Spec.MlDsa.ntt w = nttLayer ([4, 2].foldl nttLayer ([128, 64, 32, 16, 8].foldl nttLayer w)) 1 := by
  rw [VG.Proof.MlDsa.Arith.ntt_eq_layers]
  simp only [nttLens, List.foldl_cons, List.foldl_nil]

theorem pre_of {s : State} (h : (Proof.MlDsa.nttContract Arm.abi 28).pre s) : PreE s := by
  sig_pre [Proof.MlDsa.nttContract, Proof.MlDsa.inPlaceContract, Proof.MlDsa.inPlaceSig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨h1, -, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- The frames' region is disjoint from the buffers. -/
theorem stack_disj {s : State} (hp : PreE s) :
    ∀ R ∈ [polyRegion (F s), polyRegion (S s)], (belowA s.sp (4 * nttSaved.length)).Disjoint R := by
  intro R hR
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
  rcases hR with rfl | rfl
  exacts [hp.sF, hp.sS]

/-- The callee-saved registers, from those `saving nttSaved` restores. -/
theorem preserved_of {s s' s₂ : State}
    (hg : ∀ r, s'.gpr r = if r ∈ nttSaved then s.gpr r else s₂.gpr r)
    (h11 : s₂.gpr .r11 = s.gpr .r11) (hlr : s₂.gpr .lr = s.gpr .lr) : ∀ r ∈ preserved, s'.gpr r = s.gpr r :=
  preserved_of_saving hg fun r hr hn => by
    simp only [preserved, nttSaved, List.mem_cons, List.not_mem_nil, or_false] at hr hn
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hn
    exacts [h11, hlr]

theorem correct {s : State} (hp : PreE s) :
    WP isa Impl.MlDsa.Arm.Arith.ntt s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      PolyIs s'.mem (F s) (Spec.MlDsa.ntt (polyAt s.mem (F s))) := by
  refine WP.mono (wp_saving nttSaved _ (W := [polyRegion (F s), polyRegion (S s)])
    (fun s₂ => s₂.gpr .r11 = s.gpr .r11 ∧ s₂.gpr .lr = s.gpr .lr ∧
      PolyIs s₂.mem (F s) (Spec.MlDsa.ntt (polyAt s.mem (F s))))
    s hp.sp (stack_disj hp)
    (fun _ _ _ hf ⟨h11, hlr, hq⟩ => ⟨h11, hlr, polyIs_frame hf (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (stack_disj hp _ (List.mem_cons_self ..)).symm) hq⟩) fun s₁ hE => ?_)
    fun s' ⟨s₂, ⟨h11, hlr, hq⟩, hm, _, hsp, _, hg⟩ => ⟨preserved_of hg h11 hlr, hsp, hm ▸ hq⟩
  obtain ⟨hpB, eP, eF, eS⟩ := pre_entry hp hE
  refine WP.seq (WP.mono (pro_ok hpB zetaTab zetaTab_lt 4 1 rfl (by decide)) fun s₂ hI => ?_)
  refine WP.seq (WP.mono (lays_ok hpB (fun len => nttBlkL (Impl.MlDsa.Arm.Arith.bfly len) len .add)
    [128, 64, 32, 16, 8] _ 1 s₂ (fun len hl => ?_) (by simp only [Chain]; decide) hI) fun s₃ hI₃ => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by decide, blkL_ok bfly_core zetaTab_of hpB.fitF hpB.fitS (by decide) .add (.inl rfl) (by decide)
        (by decide)⟩
  refine WP.seq (WP.mono (lays_ok hpB (fun len => nttBlkS (Impl.MlDsa.Arm.Arith.bfly len) len .add)
    [4, 2] _ 32 s₃ (fun len hl => ?_) (by simp only [Chain]; decide) hI₃) fun s₄ hI₄ => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;>
      exact ⟨by decide, blkS_ok bfly_core zetaTab_of hpB.fitF hpB.fitS (by decide) .add (.inl rfl) (by decide)⟩
  refine WP.mono (layF_ok hpB (len := 1) (by decide)
    (blkS_ok bflyC_core zetaTab_of hpB.fitF hpB.fitS (by decide) .add (.inl rfl) (by decide)) hI₄)
    fun s₅ hI₅ => ⟨?_, ?_, ?_, ?_⟩
  · rw [← eF, ← eS]; exact hI₅.frame
  · rw [hI₅.keep.gpr .r11 (by decide)]; exact congrFun hE.gpr _
  · rw [hI₅.keep.gpr .lr (by decide)]; exact congrFun hE.gpr _
  · have hr := layersF_rel [4, 2] _ _ _ (by decide) (by decide)
      (layersF_rel [128, 64, 32, 16, 8] 1 _ _ (by decide) (by decide) (lift_rel (polyAt s₁.mem (F s₁))))
    rw [← eP, ← eF, ntt_split]
    refine polyIs_of_toNat fun j hj => ?_
    rw [hI₅.poly j hj]
    exact layerFC_val (by decide) hr (by decide) (by rw [n_eq] at hj; exact hj)

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 1024⟩, ⟨0x2000, 1024⟩]

theorem verified : Verified Arm.target Impl.MlDsa.Arm.Arith.ntt (Proof.MlDsa.nttContract Arm.abi 28) := by
  refine ⟨fun s hs => ?_, ct_of_saving nttSaved _ [.r0, .r1] (fun s₁ s₂ h => ?_) (by native_taint_decide), ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, h⟩ := correct (pre_of hs)
    refine ⟨t, s', he, ⟨hpres, hsp⟩, ?_⟩
    sig_post [Proof.MlDsa.nttContract, Proof.MlDsa.inPlaceContract, Proof.MlDsa.inPlaceSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    exact h
  · sig_pub [Proof.MlDsa.nttContract, Proof.MlDsa.inPlaceContract, Proof.MlDsa.inPlaceSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    obtain ⟨hsp, h0, h1⟩ := h
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> with_reducible assumption
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.nttContract, Proof.MlDsa.inPlaceContract, Proof.MlDsa.inPlaceSig, Arm.abi,
        Arm.argRegs, Arm.Loc.val]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _

end VG.Proof.MlDsa.Arm.Arith.Ntt

end

end

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_inv_ntt`

As `vg_mldsa_ntt` (`Ntt.lean`), with the negated zetas, from the last, and
`bflyInv_core`: the first seven layers leave words congruent to those of
`NTT⁻¹`'s (`layerI`, `layersI_rel`). The last layer's one block is the loop
over groups of four of `bflyInvS` (`grpLoop_ok` with `bflyInvS_core`), with
`8347681 = 256⁻¹ mod q` and the layer's zeta times it in registers
(`scalePre_ok`): it leaves the last layer's coefficients times `256⁻¹`
(`lastInv_val`), which `nttInv_split` says is `NTT⁻¹`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Arith.NttInv

open VG VG.Arm VG.Impl.MlDsa.Arm.Arith
open VG.Spec.MlDsa (q n Poly Zq zetas)
open VG.Proof.MlDsa (coeffAt polyAt Reduced PolyIs)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.Arm.Arith.Ntt
open VG.Proof.MlKem.Arm (wp_loop_ne count_z count_sub addr_ptr inRegions_of)
open VG.Proof.MlDsa.Arm.Arith.AddSub (reduced_zero)

/-! ## The layers -/

/-- The chain of zeta indices of the layers `ls` of `NTT⁻¹`, from `k`. -/
def ChainInv : Nat → List Nat → Prop
  | _, [] => True
  | k, len :: ls => k = 256 / len - 1 ∧ ChainInv (128 / len - 1) ls

/-- The zeta index after the layers `ls`, from `k`. -/
def chainEndInv : Nat → List Nat → Nat
  | k, [] => k
  | _, len :: ls => chainEndInv (128 / len - 1) ls

theorem lens_inv : ∀ len ∈ nttInvLens, len ∈ nttLens ∧ 128 / len ≤ 256 / len - 1 ∧ 256 / len ≤ 256 ∧
    256 / len = 2 * (128 / len) := by decide

theorem negZetaTab_of : TabOf negZetaTab (fun m => -zetas m) := fun k _ => negZetaNat_eq k

theorem negZetaTab_lt : ∀ k < 256, negZetaTab k < q := fun k _ => negZetaNat_lt k

theorem lays_ok {s₁ : State} (hp : PreB s₁) (blk : Nat → Prog isa) :
    ∀ (ls : List Nat) (G : LPoly) (k : Nat) (s : State),
      (∀ len ∈ ls, len ∈ nttInvLens ∧
        BlockOk (blk len) opI negZetaTab (fun m => -zetas m) .sub len (pf s₁) (ps s₁)) → ChainInv k ls →
      LI negZetaTab s₁ G k s →
      WP isa (lays blk ls) s fun s' => LI negZetaTab s₁ (ls.foldl layerI G) (chainEndInv k ls) s'
  | [], _, _, _, _, _, hI => WP.block_nil hI
  | len :: ls, G, k, s, hls, ⟨hk, hc⟩, hI => by
    obtain ⟨hlen', hblk⟩ := hls len (List.mem_cons_self ..)
    obtain ⟨hlen, h1, h2, h3⟩ := lens_inv len hlen'
    have hl0 := (lens_facts len hlen).2.2.2.1
    refine WP.seq (WP.mono (lay_ok hblk hlen
      (fun c => 256 / len - 1 - c) (fun c hc => by omega_using [h2])
      (fun c hc => by
        simp only [nextZ, reduceCtorEq, ite_false]
        rw [show 4 * (256 / len - 1 - c) = 4 * (256 / len - 1 - (c + 1)) + 4 by omega_using [h1, hc], BitVec.ofNat_add,
          ← BitVec.add_assoc]
        exact BitVec.add_sub_cancel _ _)
      G s hI.r0 (by rw [hI.r1, hk]; rfl) hI.r4 hI.r5 hI.poly (by rw [hI.keep.wr]; exact hp.wF)
      (by rw [hI.keep.wr]; exact List.mem_append_right _ hp.wS) hp.fs.symm hI.tab)
      fun s' ⟨hP, hf, h0, h1', hk'⟩ => ?_)
    exact lays_ok hp blk ls _ (128 / len - 1) s' (fun l hl => hls l (List.mem_cons_of_mem _ hl)) hc
      (hI.step hP hf h0 (by rw [h1']; congr 3; omega_using [h3]) hk' hp.fs.symm)

/-! ## The last layer -/

theorem scaleZeta_eq : scaleZeta = (-zetas 1 * cInv).val := by
  rw [Fin.val_mul, ← negZetaNat_eq]; rfl

theorem scaleZeta_word : (BitVec.ofNat 16 (scaleZeta / 65536) ++
    ((BitVec.ofNat 16 (scaleZeta % 65536)).setWidth 32).extractLsb' 0 16 : BitVec 32) = zb (-zetas 1 * cInv) :=
  (tab_word (t := fun _ => scaleZeta) (fun _ _ => by rw [scaleZeta_eq]; exact Fin.isLt _) 0 (by decide)).trans
    (congrArg (BitVec.ofNat 32) scaleZeta_eq)

theorem cInv_word : ((0x7F : BitVec 16) ++ ((0x6021 : BitVec 16).setWidth 32).extractLsb' 0 16 : BitVec 32) =
    zb cInv := by
  decide

/-- The constants of the last layer, and the count of its groups. -/
theorem scalePre_ok {s : State} (h4 : s.gpr .r4 = Nw) (h5 : s.gpr .r5 = Qw) :
    WP isa (.block scalePre) s fun s' =>
      ScaleIn (-zetas 1) s' ∧ s'.gpr .r3 = BitVec.ofNat 32 (1 * (32 - 0)) ∧ s'.mem = s.mem ∧
        Keep [.r0, .r11, .lr] s s' := by
  run_block [scalePre, quot, bquot, ScaleIn, ZetaIn, h4, h5, scaleZeta_word, cInv_word]
  keep_simp

/-- `NTT⁻¹`, as the code's runs of layers and its last layer. -/
theorem nttInv_split (w : Poly) : Spec.MlDsa.nttInv w =
    (nttInvLayer ([8, 16, 32, 64].foldl nttInvLayer ([1, 2, 4].foldl nttInvLayer w)) 128).map (· * cInv) := by
  rw [VG.Proof.MlDsa.Arith.nttInv_eq_layers]
  simp only [nttInvLens, List.foldl_cons, List.foldl_nil]

theorem pre_of {s : State} (h : (Proof.MlDsa.nttInvContract Arm.abi 28).pre s) : PreE s := by
  sig_pre [Proof.MlDsa.nttInvContract, Proof.MlDsa.inPlaceContract, Proof.MlDsa.inPlaceSig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨h1, -, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem correct {s : State} (hp : PreE s) :
    WP isa Impl.MlDsa.Arm.Arith.nttInv s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      PolyIs s'.mem (F s) (Spec.MlDsa.nttInv (polyAt s.mem (F s))) := by
  refine WP.mono (wp_saving nttSaved _ (W := [polyRegion (F s), polyRegion (S s)])
    (fun s₂ => s₂.gpr .r11 = s.gpr .r11 ∧ s₂.gpr .lr = s.gpr .lr ∧
      PolyIs s₂.mem (F s) (Spec.MlDsa.nttInv (polyAt s.mem (F s))))
    s hp.sp (stack_disj hp)
    (fun _ _ _ hf ⟨h11, hlr, hq⟩ => ⟨h11, hlr, polyIs_frame hf (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (stack_disj hp _ (List.mem_cons_self ..)).symm) hq⟩) fun s₁ hE => ?_)
    fun s' ⟨s₂, ⟨h11, hlr, hq⟩, hm, _, hsp, _, hg⟩ => ⟨preserved_of hg h11 hlr, hsp, hm ▸ hq⟩
  obtain ⟨hpB, eP, eF, eS⟩ := pre_entry hp hE
  refine WP.seq (WP.mono (pro_ok hpB negZetaTab negZetaTab_lt 1020 255 rfl (by decide)) fun s₂ hI => ?_)
  refine WP.seq (WP.mono (lays_ok hpB (fun len => nttBlkS (Impl.MlDsa.Arm.Arith.bflyInv len) len .sub)
    [1, 2, 4] _ 255 s₂ (fun len hl => ?_) (by simp only [ChainInv]; decide) hI) fun s₃ hI₃ => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl <;>
      exact ⟨by decide, blkS_ok bflyInv_core negZetaTab_of hpB.fitF hpB.fitS (by decide) .sub (.inr rfl)
        (by decide)⟩
  refine WP.seq (WP.mono (lays_ok hpB (fun len => nttBlkL (Impl.MlDsa.Arm.Arith.bflyInv len) len .sub)
    [8, 16, 32, 64] _ 31 s₃ (fun len hl => ?_) (by simp only [ChainInv]; decide) hI₃) fun s₄ hI₄ => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl <;>
      exact ⟨by decide, blkL_ok bflyInv_core negZetaTab_of hpB.fitF hpB.fitS (by decide) .sub (.inr rfl)
        (by decide) (by decide)⟩
  refine WP.seq (WP.mono (scalePre_ok hI₄.r4 hI₄.r5) fun s₅ ⟨hz, e3, m₅, k₅⟩ => ?_)
  have hG := hI₄.poly
  rw [← m₅] at hG
  refine WP.mono (grpLoop_ok bflyInvS_core (fun _ _ _ hk h => h.keep hk) hpB.fitF (len := 128) (start := 0)
    (N := 32) (by decide) (by decide) (by decide) (by decide) (by decide) (-zetas 1) _ s₅
    (by rw [k₅.gpr .r0 (by decide), hI₄.r0]; simp) hz hG
    (by rw [k₅.wr, hI₄.keep.wr]; exact hpB.wF) e3) fun s₆ ⟨hP, hf, _, k₆⟩ => ⟨?_, ?_, ?_, ?_⟩
  · rw [← eF, ← eS]; exact hI₄.frame.trans (by rw [← m₅]; exact hf.mono (by simp))
  · rw [k₆.gpr .r11 (by decide), k₅.gpr .r11 (by decide), hI₄.keep.gpr .r11 (by decide)]; exact congrFun hE.gpr _
  · rw [k₆.gpr .lr (by decide), k₅.gpr .lr (by decide), hI₄.keep.gpr .lr (by decide)]; exact congrFun hE.gpr _
  · have h8 : Rel 8 _ _ := layersI_rel [1, 2, 4] 1 _ _ (by decide) (Nat.le_refl 1) (by decide)
      (lift_rel (polyAt s₁.mem (F s₁)))
    have hr : Rel 128 _ _ := layersI_rel [8, 16, 32, 64] 8 _ _ (by decide) (by decide) (by decide) h8
    rw [← eP, ← eF, nttInv_split]
    refine polyIs_of_toNat fun j hj => ?_
    rw [hP j hj]
    exact lastInv_val hr (by rw [n_eq] at hj; exact hj)

theorem verified : Verified Arm.target Impl.MlDsa.Arm.Arith.nttInv (Proof.MlDsa.nttInvContract Arm.abi 28) := by
  refine ⟨fun s hs => ?_, ct_of_saving nttSaved _ [.r0, .r1] (fun s₁ s₂ h => ?_) (by native_taint_decide), ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, h⟩ := correct (pre_of hs)
    refine ⟨t, s', he, ⟨hpres, hsp⟩, ?_⟩
    sig_post [Proof.MlDsa.nttInvContract, Proof.MlDsa.inPlaceContract, Proof.MlDsa.inPlaceSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    exact h
  · sig_pub [Proof.MlDsa.nttInvContract, Proof.MlDsa.inPlaceContract, Proof.MlDsa.inPlaceSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    obtain ⟨hsp, h0, h1⟩ := h
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> with_reducible assumption
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.nttInvContract, Proof.MlDsa.inPlaceContract, Proof.MlDsa.inPlaceSig, Arm.abi,
        Arm.argRegs, Arm.Loc.val]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _

end VG.Proof.MlDsa.Arm.Arith.NttInv

end

end

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_multiply_ntt` and `vg_mldsa_multiply_add_ntt`

The loop body is two blocks, each symbolically executed once for any state:
the loads, `quot` and `mulq` (`headMul`), and the rest (`tail_ok`,
`tailAdd_ok`); the loop invariant says which coefficients of `h` are done
(`Inv`), and `wp_saving` puts the loop in the frames that save `r4`–`r9`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Arith.Mul

open VG VG.Arm VG.Impl.MlDsa.Arm.Arith
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.Arm (wp_loop_ne count_z count_sub addr_ptr inRegions_of)
open VG.Proof.MlDsa.Arm.Arith.AddSub (ptr_succ reduced_zero ctRegs)

/-! ## The loop body -/

/-- The registers the body does not write, of those it must preserve. -/
def Keep (s s' : State) : Prop := s'.gpr .r10 = s.gpr .r10 ∧ s'.gpr .r11 = s.gpr .r11 ∧ s'.gpr .lr = s.gpr .lr

theorem Keep.trans {s₁ s₂ s₃ : State} (h₁ : Keep s₁ s₂) (h₂ : Keep s₂ s₃) : Keep s₁ s₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.trans h₁.2.2⟩

/-- What the rest of an iteration does, but for the value stored. -/
def Step (s : State) (x y w c v : BitVec 32) (s' : State) : Prop :=
  s'.gpr .r0 = x + 4 ∧ s'.gpr .r1 = y + 4 ∧ s'.gpr .r2 = w + 4 ∧ s'.gpr .r3 = c - 1 ∧ s'.z = (c - 1 == 0) ∧
    s'.gpr .r4 = Nw ∧ s'.gpr .r5 = Qw ∧ Keep s s' ∧
    s'.mem = s.mem.writeW (State.addr (x + BitVec.ofNat 32 0)) v ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp

section
variable {s : State} {x y w c p : BitVec 32} (h0 : s.gpr .r0 = x) (h1 : s.gpr .r1 = y) (h2 : s.gpr .r2 = w)
  (h3 : s.gpr .r3 = c) (h4 : s.gpr .r4 = Nw) (h5 : s.gpr .r5 = Qw) (h9 : s.gpr .r9 = p)
  (oH : InRegions s.wr (State.addr (x + BitVec.ofNat 32 0)) 4)
include h0 h1 h2 h3 h4 h5 h9 oH

theorem tail_ok : WP isa (.block mulTail) s (Step s x y w c (bcsub (bred p))) := by
  run_block [mulTail, red, csub, step3, Step, Keep, bcsub, bred, h0, h1, h2, h3, h4, h5, h9, oH]

theorem tailAdd_ok (iH : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4) :
    WP isa (.block (([.ldr .r8 .r0 0, .dp .add .r9 .r9 (.reg .r8)] : List Instr) ++ mulTail)) s
      (Step s x y w c (bcsub (bred (p + s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32)))) := by
  run_block [mulTail, red, csub, step3, Step, Keep, bcsub, bred, h0, h1, h2, h3, h4, h5, h9, oH, iH]

end

/-- The product of the coefficients at `y` and `w`, as `mulHead` leaves it. -/
abbrev prod (m : Mem) (y w : BitVec 32) : BitVec 32 :=
  let g := m.readW (State.addr (w + BitVec.ofNat 32 0)) 32
  bmulq (m.readW (State.addr (y + BitVec.ofNat 32 0)) 32) g (bquot g)

section
variable {s : State} {x y w c : BitVec 32} (h0 : s.gpr .r0 = x) (h1 : s.gpr .r1 = y) (h2 : s.gpr .r2 = w)
  (h3 : s.gpr .r3 = c) (h4 : s.gpr .r4 = Nw) (h5 : s.gpr .r5 = Qw)
  (iF : InRegions (s.rd ++ s.wr) (State.addr (y + BitVec.ofNat 32 0)) 4)
  (iG : InRegions (s.rd ++ s.wr) (State.addr (w + BitVec.ofNat 32 0)) 4)
  (oH : InRegions s.wr (State.addr (x + BitVec.ofNat 32 0)) 4)
include h0 h1 h2 h3 h4 h5 iF iG oH

omit oH in
/-- The loads, `quot` and `mulq`. -/
theorem headMul :
    WP isa (.block mulHead) s fun s' => s'.gpr .r0 = x ∧ s'.gpr .r1 = y ∧ s'.gpr .r2 = w ∧ s'.gpr .r3 = c ∧
      s'.gpr .r4 = Nw ∧ s'.gpr .r5 = Qw ∧ s'.gpr .r9 = prod s.mem y w ∧ Keep s s' ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [mulHead, quot, mulq, bquot, bmulq, Keep, h0, h1, h2, h3, h4, h5, iF, iG]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, rfl, trivial⟩

theorem body_ok : WP isa (.block mulBody) s (Step s x y w c (bcsub (bred (prod s.mem y w)))) := by
  rw [mulBody, WP.block_append_iff]
  refine WP.mono (headMul h0 h1 h2 h3 h4 h5 iF iG) fun s₂ ⟨e0, e1, e2, e3, e4, e5, e9, eo, m, rd, wr, sp⟩ => ?_
  have iH' : InRegions s₂.wr (State.addr (x + BitVec.ofNat 32 0)) 4 := by rw [wr]; exact oH
  refine WP.mono (tail_ok e0 e1 e2 e3 e4 e5 e9 iH') fun s' ⟨r0, r1, r2, r3, z, r4, r5, ro, m', rd', wr', sp'⟩ =>
    ⟨r0, r1, r2, r3, z, r4, r5, eo.trans ro, by rw [m', m], rd'.trans rd, wr'.trans wr, sp'.trans sp⟩

theorem bodyAdd_ok (iH : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4) :
    WP isa (.block mulAddBody) s (Step s x y w c
      (bcsub (bred (prod s.mem y w + s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32)))) := by
  rw [mulAddBody, List.append_assoc, WP.block_append_iff]
  refine WP.mono (headMul h0 h1 h2 h3 h4 h5 iF iG) fun s₂ ⟨e0, e1, e2, e3, e4, e5, e9, eo, m, rd, wr, sp⟩ => ?_
  have iH' : InRegions s₂.wr (State.addr (x + BitVec.ofNat 32 0)) 4 := by rw [wr]; exact oH
  have iH'' : InRegions (s₂.rd ++ s₂.wr) (State.addr (x + BitVec.ofNat 32 0)) 4 := by rw [wr, rd]; exact iH
  refine WP.mono (tailAdd_ok e0 e1 e2 e3 e4 e5 e9 iH' iH'')
    fun s' ⟨r0, r1, r2, r3, z, r4, r5, ro, m', rd', wr', sp'⟩ =>
    ⟨r0, r1, r2, r3, z, r4, r5, eo.trans ro, by rw [m', m], rd'.trans rd, wr'.trans wr, sp'.trans sp⟩

end

/-! ## The loop -/

section
variable (s₀ : State)

abbrev ph : BitVec 32 := s₀.gpr .r0
abbrev pf : BitVec 32 := s₀.gpr .r1
abbrev pg : BitVec 32 := s₀.gpr .r2
abbrev H : Addr := State.addr (ph s₀)
abbrev F : Addr := State.addr (pf s₀)
abbrev G : Addr := State.addr (pg s₀)

end

/-- What the body's loop needs of the state it starts in. -/
structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [polyRegion (F s₀), polyRegion (G s₀)]
  wr : polyRegion (H s₀) ∈ s₀.wr
  hf : (polyRegion (H s₀)).Disjoint (polyRegion (F s₀))
  hg : (polyRegion (H s₀)).Disjoint (polyRegion (G s₀))
  fitH : (ph s₀).toNat + 1024 ≤ 2 ^ 32
  fitF : (pf s₀).toNat + 1024 ≤ 2 ^ 32
  fitG : (pg s₀).toNat + 1024 ≤ 2 ^ 32
  redF : Reduced s₀.mem (F s₀)
  redG : Reduced s₀.mem (G s₀)

/-- After `i` iterations, writing `out j` to coefficient `j` of `h`. -/
structure Inv (out : Nat → BitVec 32) (s₀ : State) (i : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = ph s₀ + BitVec.ofNat 32 (4 * i)
  r1 : s.gpr .r1 = pf s₀ + BitVec.ofNat 32 (4 * i)
  r2 : s.gpr .r2 = pg s₀ + BitVec.ofNat 32 (4 * i)
  r3 : s.gpr .r3 = BitVec.ofNat 32 (1 * (256 - i))
  r4 : s.gpr .r4 = Nw
  r5 : s.gpr .r5 = Qw
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  keep : Keep s₀ s
  frame : Frame [polyRegion (H s₀)] s₀.mem s.mem
  coeff : ∀ j < 256, coeffAt s.mem (H s₀) j = if j < i then out j else coeffAt s₀.mem (H s₀) j

/-- The facts about memory an iteration needs. -/
structure Acc (s₀ : State) (i : Nat) (s : State) : Prop where
  iF : InRegions (s.rd ++ s.wr) (State.addr (pf s₀ + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0)) 4
  iG : InRegions (s.rd ++ s.wr) (State.addr (pg s₀ + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0)) 4
  iH : InRegions (s.rd ++ s.wr) (State.addr (ph s₀ + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0)) 4
  oH : InRegions s.wr (State.addr (ph s₀ + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0)) 4
  vF : s.mem.readW (State.addr (pf s₀ + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0)) 32 = coeffAt s₀.mem (F s₀) i
  vG : s.mem.readW (State.addr (pg s₀ + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0)) 32 = coeffAt s₀.mem (G s₀) i
  vH : s.mem.readW (State.addr (ph s₀ + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0)) 32 = coeffAt s₀.mem (H s₀) i

theorem acc_of {out : Nat → BitVec 32} {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 256) {s : State}
    (h : Inv out s₀ i s) : Acc s₀ i s := by
  have fF := hp.fitF
  have fG := hp.fitG
  have fH := hp.fitH
  have eF : State.addr (pf s₀ + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0) = coeffAddr (F s₀) i :=
    addr_ptr _ _ _ (by omega_arith)
  have eG : State.addr (pg s₀ + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0) = coeffAddr (G s₀) i :=
    addr_ptr _ _ _ (by omega_arith)
  have eH : State.addr (ph s₀ + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0) = coeffAddr (H s₀) i :=
    addr_ptr _ _ _ (by omega_arith)
  have cF := coeff_contains (F s₀) (i := i) hi
  have cG := coeff_contains (G s₀) (i := i) hi
  have cH := coeff_contains (H s₀) (i := i) hi
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eF, h.rd, h.wr, hp.rd]; exact inRegions_of (by simp) cF
  · rw [eG, h.rd, h.wr, hp.rd]; exact inRegions_of (by simp) cG
  · rw [eH, h.rd, h.wr]; exact inRegions_of (List.mem_append_right _ hp.wr) cH
  · rw [eH, h.wr]; exact inRegions_of hp.wr cH
  · rw [eF, ← coeffAt_eq]
    exact coeffAt_frame h.frame (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.hf.symm) hi
  · rw [eG, ← coeffAt_eq]
    exact coeffAt_frame h.frame (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.hg.symm) hi
  · rw [eH, ← coeffAt_eq, h.coeff i hi, ite_eq_right (Nat.lt_irrefl i)]

/-- One iteration, from the value the body stores. -/
theorem inv_step {out : Nat → BitVec 32} {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 256)
    {s : State} (h : Inv out s₀ i s) {body : List Instr}
    (hb : WP isa (.block body) s (Step s (ph s₀ + BitVec.ofNat 32 (4 * i)) (pf s₀ + BitVec.ofNat 32 (4 * i))
      (pg s₀ + BitVec.ofNat 32 (4 * i)) (BitVec.ofNat 32 (1 * (256 - i))) (out i))) :
    WP isa (.block body) s fun s' => Inv out s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = 256) := by
  have fH := hp.fitH
  have eH : State.addr (ph s₀ + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0) = coeffAddr (H s₀) i :=
    addr_ptr _ _ _ (by omega_arith)
  have cH := coeff_contains (H s₀) (i := i) hi
  refine WP.mono hb fun s' ⟨r0, r1, r2, r3, z, r4, r5, ro, m, rd, wr, sp⟩ => ⟨⟨?_, ?_, ?_, ?_, r4, r5,
    rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, h.keep.trans ro, ?_, ?_⟩, ?_⟩
  · rw [r0]; exact ptr_succ _ 4 i
  · rw [r1]; exact ptr_succ _ 4 i
  · rw [r2]; exact ptr_succ _ 4 i
  · rw [r3]; exact count_sub (k := 1) hi
  · rw [m, eH]
    exact h.frame.writeW (List.mem_singleton_self _) _ cH
  · intro j hj
    rw [m, eH, coeffAt_writeW _ _ hj hi, h.coeff j hj]
    by_cases hij : i = j
    · subst hij; simp
    · rw [ite_eq_right hij]
      by_cases hj' : j < i
      · rw [ite_eq_left hj', ite_eq_left (by omega_arith)]
      · rw [ite_eq_right hj', ite_eq_right (by omega_arith)]
  · rw [z]; exact count_z (k := 1) hi (by decide) (by decide)

/-- The loop, after the constants are loaded. -/
theorem loop_ok {out : Nat → BitVec 32} {s₀ : State} {body : List Instr}
    (hb : ∀ i < 256, ∀ s, Inv out s₀ i s → WP isa (.block body) s fun s' =>
      Inv out s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = 256)) :
    WP isa (.seq (.block mulPre) (.loop (.block body) .ne)) s₀ (Inv out s₀ 256) := by
  refine WP.seq (WP.of_runBlock ?_)
  refine ⟨_, by simp only [mulPre, loadNQ, loadQ, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
    exec, Op2.eval, isa]; rfl,
    wp_loop_ne (Inv out s₀) (N := 256) (by decide) hb (fun _ h => h) ?_⟩
  refine ⟨by simp [State.setReg], by simp [State.setReg], by simp [State.setReg], rfl, ?_, ?_, rfl, rfl, rfl,
    ⟨by simp [State.setReg], by simp [State.setReg], by simp [State.setReg]⟩, Frame.refl _ _, fun j _ => rfl⟩
  · simp only [State.setReg]; exact loadNQ_val
  · simp only [State.setReg]; exact loadQ_val

/-- The value stored in coefficient `j` by `vg_mldsa_multiply_ntt`. -/
def mulOut (s₀ : State) (j : Nat) : BitVec 32 :=
  BitVec.ofNat 32 ((multiplyNTT (polyAt s₀.mem (F s₀)) (polyAt s₀.mem (G s₀)))[j]!).val

/-- The value stored in coefficient `j` by `vg_mldsa_multiply_add_ntt`. -/
def mulAddOut (s₀ : State) (j : Nat) : BitVec 32 :=
  BitVec.ofNat 32 ((add (polyAt s₀.mem (H s₀)) (multiplyNTT (polyAt s₀.mem (F s₀)) (polyAt s₀.mem (G s₀))))[j]!).val

/-- The product as `mulHead` leaves it: `mulqN` of the two coefficients. -/
theorem prod_toNat {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 256) {m : Mem} {y w : BitVec 32}
    (hy : m.readW (State.addr (y + BitVec.ofNat 32 0)) 32 = coeffAt s₀.mem (F s₀) i)
    (hw : m.readW (State.addr (w + BitVec.ofNat 32 0)) 32 = coeffAt s₀.mem (G s₀) i) :
    (prod m y w).toNat = mulqN (coeffAt s₀.mem (F s₀) i).toNat (coeffAt s₀.mem (G s₀) i).toNat ∧
      (coeffAt s₀.mem (F s₀) i).toNat ≤ redMax := by
  have hF : (coeffAt s₀.mem (F s₀) i).toNat ≤ redMax :=
    Nat.le_trans (Nat.le_of_lt (hp.redF i hi)) (by decide)
  simp only [prod, hy, hw]
  exact ⟨bmulq_toNat hF (hp.redG i hi), hF⟩

theorem mul_hb {s₀ : State} (hp : Pre s₀) : ∀ i < 256, ∀ s, Inv (mulOut s₀) s₀ i s →
    WP isa (.block mulBody) s fun s' => Inv (mulOut s₀) s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = 256) := by
  intro i hi s h
  have a := acc_of hp hi h
  refine inv_step hp hi h (WP.mono (body_ok h.r0 h.r1 h.r2 h.r3 h.r4 h.r5 a.iF a.iG a.oH) fun s' hs => ?_)
  refine (?_ : _ = mulOut s₀ i) ▸ hs
  refine ofNat_val_eq ?_
  obtain ⟨eP, hF⟩ := prod_toNat hp hi a.vF a.vG
  generalize prod s.mem _ _ = P at eP ⊢
  have hr := red23_le (x := P.toNat) P.isLt
  rw [bcsub_toNat (by rw [bred_toNat]; exact Nat.lt_of_le_of_lt hr redMax_lt), bred_toNat, red23_mod, eP,
    mulqN_mod hF (hp.redG i hi), mul_get _ _ hi, val_mul, polyAt_val hp.redF hi, polyAt_val hp.redG hi]

theorem mulAdd_hb {s₀ : State} (hp : Pre s₀) (hH : Reduced s₀.mem (H s₀)) :
    ∀ i < 256, ∀ s, Inv (mulAddOut s₀) s₀ i s →
    WP isa (.block mulAddBody) s fun s' => Inv (mulAddOut s₀) s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = 256) := by
  intro i hi s h
  have a := acc_of hp hi h
  refine inv_step hp hi h (WP.mono (bodyAdd_ok h.r0 h.r1 h.r2 h.r3 h.r4 h.r5 a.iF a.iG a.oH a.iH) fun s' hs => ?_)
  refine (?_ : _ = mulAddOut s₀ i) ▸ hs
  refine ofNat_val_eq ?_
  obtain ⟨eP, hF⟩ := prod_toNat hp hi a.vF a.vG
  have hb := (mulqN_bounds hF (hp.redG i hi)).2.2
  have hmod := mulqN_mod hF (hp.redG i hi)
  have hHi := hH i hi
  rw [a.vH]
  generalize prod s.mem _ _ = P at eP ⊢
  rw [← eP] at hb hmod
  have hs : (P + coeffAt s₀.mem (H s₀) i).toNat = P.toNat + (coeffAt s₀.mem (H s₀) i).toNat := by
    rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega_using [hb, hHi])
  have hr := red23_le (x := (P + coeffAt s₀.mem (H s₀) i).toNat) (BitVec.isLt _)
  rw [bcsub_toNat (by rw [bred_toNat]; exact Nat.lt_of_le_of_lt hr redMax_lt), bred_toNat, red23_mod, hs,
    add_get _ _ hi, val_add', mul_get _ _ hi, val_mul, polyAt_val hH hi, polyAt_val hp.redF hi,
    polyAt_val hp.redG hi, Nat.add_mod, hmod, Nat.add_comm, Nat.add_mod_mod, Nat.mod_add_mod]
  exact (Nat.add_mod_mod _ _ _).symm

/-! ## Verified -/

/-- The precondition of both functions, on entry. -/
structure PreE (s : State) : Prop where
  sp : 24 ≤ s.sp.toNat
  rd : s.rd = [polyRegion (F s), polyRegion (G s)]
  wr : s.wr = [polyRegion (H s)]
  hf : (polyRegion (H s)).Disjoint (polyRegion (F s))
  hg : (polyRegion (H s)).Disjoint (polyRegion (G s))
  sH : (belowA s.sp 24).Disjoint (polyRegion (H s))
  sF : (belowA s.sp 24).Disjoint (polyRegion (F s))
  sG : (belowA s.sp 24).Disjoint (polyRegion (G s))
  fitH : (ph s).toNat + 1024 ≤ 2 ^ 32
  fitF : (pf s).toNat + 1024 ≤ 2 ^ 32
  fitG : (pg s).toNat + 1024 ≤ 2 ^ 32
  redF : Reduced s.mem (F s)
  redG : Reduced s.mem (G s)

theorem pre_of {s : State} (h : (Proof.MlDsa.mulContract Arm.abi 24).pre s) : PreE s := by
  sig_pre [Proof.MlDsa.mulContract, Proof.MlDsa.mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h1, -, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

theorem preAdd_of {s : State} (h : (Proof.MlDsa.mulAddContract Arm.abi 24).pre s) :
    PreE s ∧ Reduced s.mem (H s) := by
  sig_pre [Proof.MlDsa.mulAddContract, Proof.MlDsa.mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h1, -, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h0, h12, h13⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩, h0⟩

/-- The loop's precondition, in the state after the pushes. -/
theorem pre_entry {s s₁ : State} (hp : PreE s) (hE : Entry 24 s s₁) :
    Pre s₁ ∧ polyAt s₁.mem (F s₁) = polyAt s.mem (F s) ∧ polyAt s₁.mem (G s₁) = polyAt s.mem (G s) ∧
      polyAt s₁.mem (H s₁) = polyAt s.mem (H s) ∧ (Reduced s.mem (H s) → Reduced s₁.mem (H s₁)) := by
  have g := hE.gpr
  have eF : F s₁ = F s := by simp only [F, pf, g]
  have eG : G s₁ = G s := by simp only [G, pg, g]
  have eH : H s₁ = H s := by simp only [H, ph, g]
  have fr := hE.frame
  have dF : ∀ r ∈ [belowA s.sp 24], (polyRegion (F s)).Disjoint r := fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact hp.sF.symm
  have dG : ∀ r ∈ [belowA s.sp 24], (polyRegion (G s)).Disjoint r := fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact hp.sG.symm
  have dH : ∀ r ∈ [belowA s.sp 24], (polyRegion (H s)).Disjoint r := fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact hp.sH.symm
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by rw [eF]; exact polyAt_frame fr dF,
    by rw [eG]; exact polyAt_frame fr dG, by rw [eH]; exact polyAt_frame fr dH,
    fun h => by rw [eH]; exact reduced_frame fr dH h⟩
  · rw [hE.rd, hp.rd, eF, eG]
  · rw [eH]; exact hE.wr _ (by rw [hp.wr]; exact List.mem_singleton_self _)
  · rw [eH, eF]; exact hp.hf
  · rw [eH, eG]; exact hp.hg
  · simp only [ph, g]; exact hp.fitH
  · simp only [pf, g]; exact hp.fitF
  · simp only [pg, g]; exact hp.fitG
  · rw [eF]; exact reduced_frame fr dF hp.redF
  · rw [eG]; exact reduced_frame fr dG hp.redG

theorem correct {s : State} (hp : PreE s) :
    WP isa Impl.MlDsa.Arm.Arith.mul s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      PolyIs s'.mem (H s) (multiplyNTT (polyAt s.mem (F s)) (polyAt s.mem (G s))) := by
  refine WP.mono (wp_saving mulSaved _ (W := [polyRegion (H s)])
    (fun s₂ => Keep s s₂ ∧ PolyIs s₂.mem (H s) (multiplyNTT (polyAt s.mem (F s)) (polyAt s.mem (G s))))
    s hp.sp (fun R hR => by rw [List.mem_singleton] at hR; subst hR; exact hp.sH)
    (fun _ _ _ hf ⟨hk, hq⟩ => ⟨hk, polyIs_frame hf (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hp.sH.symm) hq⟩) fun s₁ hE => ?_)
    fun s' ⟨s₂, ⟨hk, hq⟩, hm, _, hsp, _, hg⟩ => ⟨preserved_of_saving hg fun r hr hn => ?_, hsp, hm ▸ hq⟩
  · obtain ⟨hp₁, eF, eG, eH, -⟩ := pre_entry hp hE
    have eH' : H s₁ = H s := by simp only [H, ph, hE.gpr]
    refine WP.mono (loop_ok (mul_hb hp₁)) fun s₂ h => ⟨?_, ?_, ?_⟩
    · rw [← eH']; exact h.frame
    · have k := h.keep
      simp only [Keep, hE.gpr] at k ⊢
      exact k
    · rw [← eH', ← eF, ← eG]
      exact polyIs_of_toNat fun j hj => by
        rw [h.coeff j hj, ite_eq_left hj, mulOut, toNat_val]
  · simp only [preserved, mulSaved, List.mem_cons, List.not_mem_nil, or_false] at hr hn
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hn
    · exact hk.1
    · exact hk.2.1
    · exact hk.2.2

theorem correctAdd {s : State} (hp : PreE s) (hH : Reduced s.mem (H s)) :
    WP isa Impl.MlDsa.Arm.Arith.mulAdd s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      PolyIs s'.mem (H s) (add (polyAt s.mem (H s)) (multiplyNTT (polyAt s.mem (F s)) (polyAt s.mem (G s)))) := by
  refine WP.mono (wp_saving mulSaved _ (W := [polyRegion (H s)])
    (fun s₂ => Keep s s₂ ∧
      PolyIs s₂.mem (H s) (add (polyAt s.mem (H s)) (multiplyNTT (polyAt s.mem (F s)) (polyAt s.mem (G s)))))
    s hp.sp (fun R hR => by rw [List.mem_singleton] at hR; subst hR; exact hp.sH)
    (fun _ _ _ hf ⟨hk, hq⟩ => ⟨hk, polyIs_frame hf (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hp.sH.symm) hq⟩) fun s₁ hE => ?_)
    fun s' ⟨s₂, ⟨hk, hq⟩, hm, _, hsp, _, hg⟩ => ⟨preserved_of_saving hg fun r hr hn => ?_, hsp, hm ▸ hq⟩
  · obtain ⟨hp₁, eF, eG, eH, rH⟩ := pre_entry hp hE
    have eH' : H s₁ = H s := by simp only [H, ph, hE.gpr]
    refine WP.mono (loop_ok (mulAdd_hb hp₁ (rH hH))) fun s₂ h => ⟨?_, ?_, ?_⟩
    · rw [← eH']; exact h.frame
    · have k := h.keep
      simp only [Keep, hE.gpr] at k ⊢
      exact k
    · rw [← eH, ← eF, ← eG, ← eH']
      exact polyIs_of_toNat fun j hj => by
        rw [h.coeff j hj, ite_eq_left hj, mulAddOut, toNat_val]
  · simp only [preserved, mulSaved, List.mem_cons, List.not_mem_nil, or_false] at hr hn
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hn
    · exact hk.1
    · exact hk.2.1
    · exact hk.2.2

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 1024⟩, ⟨0x3000, 1024⟩]
  wr := [⟨0x1000, 1024⟩]

theorem mul_verified : Verified Arm.target Impl.MlDsa.Arm.Arith.mul (Proof.MlDsa.mulContract Arm.abi 24) := by
  refine ⟨fun s hs => ?_, ct_of_saving mulSaved _ [.r0, .r1, .r2] (fun s₁ s₂ h => ?_) (by native_taint_decide), ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, h⟩ := correct (pre_of hs)
    refine ⟨t, s', he, ⟨hpres, hsp⟩, ?_⟩
    sig_post [Proof.MlDsa.mulContract, Proof.MlDsa.mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val]
    exact h
  · sig_pub [Proof.MlDsa.mulContract, Proof.MlDsa.mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    obtain ⟨hsp, h0, h1, h2⟩ := h
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> with_reducible assumption
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.mulContract, Proof.MlDsa.mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
        Arm.Loc.val]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _

theorem mulAdd_verified :
    Verified Arm.target Impl.MlDsa.Arm.Arith.mulAdd (Proof.MlDsa.mulAddContract Arm.abi 24) := by
  refine ⟨fun s hs => ?_, ct_of_saving mulSaved _ [.r0, .r1, .r2] (fun s₁ s₂ h => ?_) (by native_taint_decide), ?_⟩
  · obtain ⟨hp, hH⟩ := preAdd_of hs
    obtain ⟨t, s', he, hpres, hsp, h⟩ := correctAdd hp hH
    refine ⟨t, s', he, ⟨hpres, hsp⟩, ?_⟩
    sig_post [Proof.MlDsa.mulAddContract, Proof.MlDsa.mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val]
    exact h
  · sig_pub [Proof.MlDsa.mulAddContract, Proof.MlDsa.mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    obtain ⟨hsp, h0, h1, h2⟩ := h
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> with_reducible assumption
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.mulAddContract, Proof.MlDsa.mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
        Arm.Loc.val]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _

end VG.Proof.MlDsa.Arm.Arith.Mul

end

end

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_rej_ntt_poly`, constant time but for the seed, and `Verified`

Two runs from entry states whose seeds (the declared leak), pointers and stack
pointers agree leak the same (`all_ct`): the prologue and the blocks around
the loop by the taint analysis, the sponge by `sponge_ct`, and the loop, whose
branches and stores depend on the XOF output, by relating the two runs
iteration by iteration (`body_ct`): both are at the same iteration with the
same coefficients sampled and the same bytes to read, so each branch goes the
same way and each store goes to the same address.
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Sample.RejNtt

open VG VG.Arm
open VG.Proof.MlKem.Arm
open VG.Proof.MlDsa.Arm.Sample
open VG.Impl.MlDsa.Arm.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q G)
open VG.Proof.MlDsa (PolyIs)
open VG.Spec.Sha3 (bytesAt)

/-- Two runs, from entry states that agree on the public data. -/
structure Two (σ₁ σ₂ : State) : Prop where
  hp₁ : SpOk (spOf σ₁) σ₁
  hp₂ : SpOk (spOf σ₂) σ₂
  sp : σ₁.sp = σ₂.sp
  r0 : σ₁.gpr .r0 = σ₂.gpr .r0
  r1 : σ₁.gpr .r1 = σ₂.gpr .r1
  r2 : σ₁.gpr .r2 = σ₂.gpr .r2
  B : B σ₁ = B σ₂

theorem nil_regs {R : State → State → Prop} : ∀ x y, R x y → ∀ r ∈ ([] : List Reg), x.gpr r = y.gpr r :=
  fun _ _ _ _ h => absurd h List.not_mem_nil

section
variable {σ₁ σ₂ : State} (h : Two σ₁ σ₂)
include h

theorem sp_eq : spOf σ₂ = spOf σ₁ := by simp only [spOf, h.r0, h.r1, h.r2]

theorem X_eq : X σ₁ = X σ₂ := by simp only [X, h.B]

theorem Lt_eq (t : Nat) : Lt σ₁ t = Lt σ₂ t := by simp only [Lt, X_eq h]

theorem V_eq (t : Nat) : V σ₁ t = V σ₂ t := by simp only [V, Xb, X_eq h]

/-! ## The loop -/

theorem try_ct {t : Nat} :
    RelCT isa (fun a b => (M1 σ₁ t a ∧ M1 σ₂ t b) ∧ isa.eval .eq a = some false) rnTry fun _ _ => True := by
  have hz : ∀ a b, (M1 σ₁ t a ∧ M1 σ₂ t b) ∧ isa.eval .eq a = some false → a.z = false ∧ b.z = false :=
    fun a b hab => by
      have e : a.z = false := Option.some.inj hab.2
      refine ⟨e, ?_⟩
      rw [← e, hab.1.1.z, hab.1.2.z, Lt_eq h]
  refine RelCT.seq (R := fun a b => T1 σ₁ t a ∧ T1 σ₂ t b) (relW (taintRel [] nil_regs (by native_taint_decide))
    fun a b hab => ⟨tryA hab.1.1 (hz a b hab).1, tryA hab.1.2 (hz a b hab).2⟩) ?_
  refine RelCT.ite (fun a b hab => by
    show some a.z = some b.z; rw [hab.1.z, hab.2.z, V_eq h]) (taintRel [] nil_regs (by native_taint_decide))
    (taintRel [.r2, .r5] (fun a b hab r hr => ?_) (by native_taint_decide))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [hab.1.1.lat.r2, hab.1.2.lat.r2, Lt_eq h]
  · rw [hab.1.1.lat.env.r5, hab.1.2.lat.env.r5, sp_eq h]

theorem body_ct {t : Nat} (ht : t < 336) :
    RelCT isa (fun a b => LAt σ₁ t a ∧ LAt σ₂ t b) rnBody fun a b =>
      (LAt σ₁ (t + 1) a ∧ a.z = decide (t + 1 = 336)) ∧ (LAt σ₂ (t + 1) b ∧ b.z = decide (t + 1 = 336)) := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  refine relW ?_ fun a b hab => ⟨body_ok hp₁ ht hab.1, body_ok hp₂ ht hab.2⟩
  refine RelCT.seq (R := fun a b => M1 σ₁ t a ∧ M1 σ₂ t b) (relW (taintRel [.r0, .r2] (fun a b hab r hr => ?_)
    (by native_taint_decide)) fun a b hab => ⟨pieceA hp₁ ht hab.1, pieceA hp₂ ht hab.2⟩) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hab.1.r0, hab.2.r0, h.r2]
    · rw [hab.1.r2, hab.2.r2, Lt_eq h]
  refine RelCT.seq (R := fun a b => M2 σ₁ t a ∧ M2 σ₂ t b) (relW ?_
    fun a b hab => ⟨pieceB hp₁ ht hab.1, pieceB hp₂ ht hab.2⟩) (taintRel [] nil_regs (by native_taint_decide))
  exact RelCT.ite (fun a b hab => by show some a.z = some b.z; rw [hab.1.z, hab.2.z, Lt_eq h])
    (taintRel [] nil_regs (by native_taint_decide)) (try_ct h)

theorem loop_ct :
    RelCT isa (fun a b => LAt σ₁ 0 a ∧ LAt σ₂ 0 b) (.loop rnBody .ne) fun a b =>
      LAt σ₁ 336 a ∧ LAt σ₂ 336 b := by
  refine RelCT.mono (RelCT.loop (M := isa) (body := rnBody) (c := .ne)
    (Q := fun a b => LAt σ₁ 336 a ∧ LAt σ₂ 336 b)
    (fun n a b => ∃ t, t < 336 ∧ n = 336 - t ∧ LAt σ₁ t a ∧ LAt σ₂ t b) (fun n => ?_) 336)
    (fun a b hab => ⟨0, by decide, rfl, hab⟩) (fun _ _ h => h)
  refine RelCT.mono (P := fun a b => ∃ t, t < 336 ∧ n = 336 - t ∧ LAt σ₁ t a ∧ LAt σ₂ t b)
    (RelCT.exists_ fun t => ?_) (fun _ _ hab => hab) (fun _ _ h => h)
  by_cases ht : t < 336
  · by_cases hn : n = 336 - t
    · refine RelCT.mono (P := fun a b => LAt σ₁ t a ∧ LAt σ₂ t b) (body_ct h ht) (fun _ _ hab => hab.2.2)
        fun a b ⟨⟨i₁, z₁⟩, ⟨i₂, z₂⟩⟩ => ⟨?_, fun e => ?_, fun e => ?_⟩
      · show some (!a.z) = some (!b.z); rw [z₁, z₂]
      · have : t + 1 = 336 := by
          have e' : (!a.z) = false := Option.some.inj e
          rw [z₁] at e'; simpa using e'
        rw [this] at i₁ i₂; exact ⟨i₁, i₂⟩
      · have : t + 1 ≠ 336 := by
          have e' : (!a.z) = true := Option.some.inj e
          rw [z₁] at e'; simpa using e'
        exact ⟨336 - (t + 1), by omega_using [ht, hn], t + 1, by omega_using [ht, this], rfl, i₁, i₂⟩
    · exact RelCT.of_false fun _ _ hab => hn hab.2.1
  · exact RelCT.of_false fun _ _ hab => ht hab.1

/-! ## The whole function -/

theorem all_ct : RelCT isa (fun a b => a = σ₁ ∧ b = σ₂) Impl.MlDsa.Arm.Sample.rejNTT fun _ _ => True := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  have eP := sp_eq h
  have hp₂' : SpOk (spOf σ₁) σ₂ := eP ▸ hp₂
  refine RelCT.seq (R := fun a b => J0 (spOf σ₁) σ₁ a ∧ J0 (spOf σ₁) σ₂ b) (relW (taintRel [.r0, .r1, .r2]
    (fun a b hab r hr => ?_) (by native_taint_decide)) fun a b hab => ⟨?_, ?_⟩) ?_
  · rw [hab.1, hab.2]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [h.r0, h.r1, h.r2]
  · rw [hab.1]; exact pro_rn hp₁ rfl rfl rfl rfl rfl
  · rw [hab.2]; exact pro_rn hp₂' h.r0.symm h.r1.symm h.r2.symm rfl rfl
  refine RelCT.seq (sponge_ct hp₁ hp₂' h.sp (rate := 168) (outlen := 1008) (by decide) (by decide) (by decide)
    (by decide) (by native_taint_decide) (by native_taint_decide) (by native_taint_decide)) ?_
  refine RelCT.seq (R := fun a b => LAt σ₁ 336 a ∧ LAt σ₂ 336 b) (RelCT.seq (R := fun a b => LAt σ₁ 0 a ∧ LAt σ₂ 0 b)
    (relW (taintRel [] nil_regs (by native_taint_decide)) fun a b hab => ⟨lat0 hab.1, lat0 (eP ▸ hab.2)⟩) (loop_ct h)) ?_
  exact taintRel [.r6] (fun a b hab r hr => by
    rw [List.mem_singleton] at hr; subst hr; rw [hab.1.env.r6, hab.2.env.r6, sp_eq h]) (by native_taint_decide)

end

/-! ## `Verified` -/

theorem spOk_of {s : State} (h : (Proof.MlDsa.rejNTTContract Arm.abi 8).pre s) : SpOk (spOf s) s := by
  sig_pre [Proof.MlDsa.rejNTTContract, Proof.MlDsa.rejNTTSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h8, -, hrd, hwr, d1, d2, d3, b1, b2, b3, f0, f1, f2⟩ := h
  exact ⟨by rw [hrd]; exact List.mem_singleton_self _, hwr, d1, d2, d3, b1, b2, b3, f0,
    show (34 : Nat) < 2 ^ 32 by decide, f1, f2, h8⟩

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
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 34⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

end VG.Proof.MlDsa.Arm.Sample.RejNtt

namespace VG.Proof.MlDsa.Arm.Sample

open VG VG.Arm
open VG.Proof.MlKem.Arm
open VG.Proof.MlDsa.Sample
open RejNtt

theorem rejNTT_verified :
    Verified Arm.target Impl.MlDsa.Arm.Sample.rejNTT (Proof.MlDsa.rejNTTContract Arm.abi 8) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, h0, hpoly, ha⟩ := correct (spOk_of hs)
    refine ⟨t, s', he, ha, ?_⟩
    sig_post [Proof.MlDsa.rejNTTContract, Proof.MlDsa.rejNTTSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val]
    rw [setWidth_append32, h0]
    by_cases hf : (rnFold [] (X s)).length = 256
    · rw [ifT hf]
      have hpi := hpoly hf
      exact ⟨fun _ => hpi.1, .inl ⟨rfl, { Spec.MlDsa.minBounds with rejNTT := 1008 }, by
        show Spec.MlDsa.rejNTTPoly 1008 _ = _
        exact (rejNTT_some hf).trans (congrArg some hpi.2.symm)⟩⟩
    · rw [ifF hf]
      exact ⟨fun e => absurd e (by decide), .inr ⟨rfl, rejNTT_none (B := 1008) (by decide) (by decide) hf⟩⟩
  · sig_pub [Proof.MlDsa.rejNTTContract, Proof.MlDsa.rejNTTSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at hpub
    obtain ⟨hsp, hb, h0, h1, h2⟩ := hpub
    exact (all_ct ⟨spOk_of h₁, spOk_of h₂, hsp, h0, h1, h2, leakBytes_inj hb⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩
      e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_sat_check [Proof.MlDsa.rejNTTContract, Proof.MlDsa.rejNTTSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]

end VG.Proof.MlDsa.Arm.Sample
