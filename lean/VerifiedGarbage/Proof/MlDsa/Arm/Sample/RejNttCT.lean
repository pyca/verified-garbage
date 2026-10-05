import VerifiedGarbage.Proof.MlDsa.Arm.Sample.ExpandMask
import VerifiedGarbage.Impl.MlDsa.Arm.Sample.RejNtt
import VerifiedGarbage.Proof.MlDsa.Sample.Signs
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Spec.MlDsa.Poly

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Sample.RejNtt`. -/
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

namespace VG.Proof.MlDsa.Arm.Sample.RejNtt

open VG VG.Arm
open VG.Proof.MlKem.Arm
open VG.Proof.MlDsa.Arm.Sample
open VG.Impl.MlDsa.Arm.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q G PolyIs)
open VG.Spec.Sha3 (bytesAt)

/-- The call, from the entry state: `seed = r0`, `a = r1`, `scratch = r2`. -/
abbrev spOf (σ : State) : Sp := ⟨σ.gpr .r0, 34, σ.gpr .r2, σ.gpr .r1, 0⟩

/-- The seed. -/
abbrev B (σ : State) : List Byte := bytesAt σ.mem (State.addr (σ.gpr .r0)) 34

/-- The XOF output. -/
abbrev X (σ : State) : List Byte := VG.Spec.MlDsa.G (VG.Proof.MlDsa.Arm.Sample.RejNtt.B σ) 1008

/-- Byte `i` of the XOF output. -/
abbrev Xb (σ : State) (i : Nat) : Byte := (VG.Proof.MlDsa.Arm.Sample.RejNtt.X σ).getD i 0

/-- The coefficients sampled after `t` iterations. -/
abbrev Lt (σ : State) (t : Nat) : List Zq := rnFold [] ((VG.Proof.MlDsa.Arm.Sample.RejNtt.X σ).take (3 * t))

/-- The value of 3 bytes, as the code computes it. -/
def rnw (b₀ b₁ b₂ : Byte) : BitVec 32 :=
  b₀.setWidth 32 + (b₂.setWidth 32 <<< 25) >>> 9 + b₁.setWidth 32 <<< 8

theorem rnw_toNat (b₀ b₁ b₂ : Byte) : (VG.Proof.MlDsa.Arm.Sample.RejNtt.rnw b₀ b₁ b₂).toNat = rnZ b₀ b₁ b₂ := by
  have h0 := b₀.isLt
  have h1 := b₁.isLt
  have h2 := b₂.isLt
  unfold VG.Proof.MlDsa.Arm.Sample.RejNtt.rnw rnZ
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft,
    setWidth32_toNat, setWidth32_toNat, setWidth32_toNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    Nat.shiftLeft_eq]
  omega

/-- The value of the 3 bytes of iteration `t`. -/
abbrev V (σ : State) (t : Nat) : BitVec 32 := VG.Proof.MlDsa.Arm.Sample.RejNtt.rnw (VG.Proof.MlDsa.Arm.Sample.RejNtt.Xb σ (3 * t)) (VG.Proof.MlDsa.Arm.Sample.RejNtt.Xb σ (3 * t + 1)) (VG.Proof.MlDsa.Arm.Sample.RejNtt.Xb σ (3 * t + 2))

theorem V_lt (σ : State) (t : Nat) : (VG.Proof.MlDsa.Arm.Sample.RejNtt.V σ t).toNat < 2 ^ 23 := by
  rw [VG.Proof.MlDsa.Arm.Sample.RejNtt.rnw_toNat]; unfold rnZ
  have := (VG.Proof.MlDsa.Arm.Sample.RejNtt.Xb σ (3 * t)).isLt; have := (VG.Proof.MlDsa.Arm.Sample.RejNtt.Xb σ (3 * t + 1)).isLt; have := (VG.Proof.MlDsa.Arm.Sample.RejNtt.Xb σ (3 * t + 2)).isLt
  omega

theorem X_length (σ : State) : (VG.Proof.MlDsa.Arm.Sample.RejNtt.X σ).length = 1008 := VG.Proof.MlDsa.Sample.G_length _ _

theorem take_add_three (L : List Byte) {i : Nat} (h : i + 3 ≤ L.length) :
    L.take (i + 3) = L.take i ++ [L.getD i 0, L.getD (i + 1) 0, L.getD (i + 2) 0] := by
  rw [List.take_add, List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
    List.drop_eq_getElem_cons (by omega)]
  simp only [List.take_succ_cons, List.take_zero, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show i < L.length by omega), List.getElem?_eq_getElem (show i + 1 < L.length by omega),
    List.getElem?_eq_getElem (show i + 2 < L.length by omega), Option.getD_some]

theorem Lt_succ (σ : State) {t : Nat} (ht : t < 336) :
    VG.Proof.MlDsa.Arm.Sample.RejNtt.Lt σ (t + 1) = rnStep (VG.Proof.MlDsa.Arm.Sample.RejNtt.Lt σ t) (VG.Proof.MlDsa.Arm.Sample.RejNtt.Xb σ (3 * t)) (VG.Proof.MlDsa.Arm.Sample.RejNtt.Xb σ (3 * t + 1)) (VG.Proof.MlDsa.Arm.Sample.RejNtt.Xb σ (3 * t + 2)) := by
  simp only [VG.Proof.MlDsa.Arm.Sample.RejNtt.Lt]
  rw [show 3 * (t + 1) = 3 * t + 3 by omega, VG.Proof.MlDsa.Arm.Sample.RejNtt.take_add_three _ (by rw [VG.Proof.MlDsa.Arm.Sample.RejNtt.X_length]; omega),
    rnFold_snoc _ (by rw [List.length_take, VG.Proof.MlDsa.Arm.Sample.RejNtt.X_length]; omega)]

theorem Lt_length_le (σ : State) (t : Nat) : (VG.Proof.MlDsa.Arm.Sample.RejNtt.Lt σ t).length ≤ 256 := rnFold_length_le (by simp) _

/-- At the start of iteration `t`. -/
structure LAt (σ : State) (t : Nat) (s : State) : Prop where
  env : Env (VG.Proof.MlDsa.Arm.Sample.RejNtt.spOf σ) σ s
  out : bytesAt s.mem ((VG.Proof.MlDsa.Arm.Sample.RejNtt.spOf σ).at' 840) 1008 = VG.Proof.MlDsa.Arm.Sample.RejNtt.X σ
  r0 : s.gpr .r0 = σ.gpr .r2 + BitVec.ofNat 32 (840 + 3 * t)
  r2 : s.gpr .r2 = BitVec.ofNat 32 (VG.Proof.MlDsa.Arm.Sample.RejNtt.Lt σ t).length
  r3 : s.gpr .r3 = BitVec.ofNat 32 (1 * (336 - t))
  r7 : s.gpr .r7 = BitVec.ofNat 32 8380417
  st : Stored s.mem (VG.Proof.MlDsa.Arm.Sample.RejNtt.spOf σ).A (VG.Proof.MlDsa.Arm.Sample.RejNtt.Lt σ t)

/-- After the value of the 3 bytes and the test of `j`. -/
structure M1 (σ : State) (t : Nat) (s : State) : Prop where
  lat : VG.Proof.MlDsa.Arm.Sample.RejNtt.LAt σ t s
  r10 : s.gpr .r10 = VG.Proof.MlDsa.Arm.Sample.RejNtt.V σ t
  z : s.z = decide (256 ≤ (VG.Proof.MlDsa.Arm.Sample.RejNtt.Lt σ t).length)

/-- After the test of the value, if `j < 256`. -/
structure T1 (σ : State) (t : Nat) (s : State) : Prop where
  lat : VG.Proof.MlDsa.Arm.Sample.RejNtt.LAt σ t s
  r10 : s.gpr .r10 = VG.Proof.MlDsa.Arm.Sample.RejNtt.V σ t
  len : (VG.Proof.MlDsa.Arm.Sample.RejNtt.Lt σ t).length < 256
  z : s.z = decide (8380417 ≤ (VG.Proof.MlDsa.Arm.Sample.RejNtt.V σ t).toNat)

/-- After the coefficient of iteration `t`. -/
structure M2 (σ : State) (t : Nat) (s : State) : Prop where
  env : Env (VG.Proof.MlDsa.Arm.Sample.RejNtt.spOf σ) σ s
  out : bytesAt s.mem ((VG.Proof.MlDsa.Arm.Sample.RejNtt.spOf σ).at' 840) 1008 = VG.Proof.MlDsa.Arm.Sample.RejNtt.X σ
  r0 : s.gpr .r0 = σ.gpr .r2 + BitVec.ofNat 32 (840 + 3 * t)
  r2 : s.gpr .r2 = BitVec.ofNat 32 (VG.Proof.MlDsa.Arm.Sample.RejNtt.Lt σ (t + 1)).length
  r3 : s.gpr .r3 = BitVec.ofNat 32 (1 * (336 - t))
  r7 : s.gpr .r7 = BitVec.ofNat 32 8380417
  st : Stored s.mem (VG.Proof.MlDsa.Arm.Sample.RejNtt.spOf σ).A (VG.Proof.MlDsa.Arm.Sample.RejNtt.Lt σ (t + 1))

/-- `LAt` after a block that writes no memory and keeps `r0`, `r2`, `r3`,
`r5`, `r6` and `r7`. -/
theorem LAt.same {σ s s' : State} {t : Nat} (h : VG.Proof.MlDsa.Arm.Sample.RejNtt.LAt σ t s) (hm : s'.mem = s.mem)
    (g : ∀ r ∈ [Reg.r0, .r2, .r3, .r5, .r6, .r7], s'.gpr r = s.gpr r) (rd : s'.rd = s.rd) (wr : s'.wr = s.wr)
    (sp : s'.sp = s.sp) : VG.Proof.MlDsa.Arm.Sample.RejNtt.LAt σ t s' :=
  ⟨h.env.same hm (g .r5 (by simp)) (g .r6 (by simp)) rd wr sp, by rw [hm]; exact h.out,
    (g .r0 (by simp)).trans h.r0, (g .r2 (by simp)).trans h.r2, (g .r3 (by simp)).trans h.r3,
    (g .r7 (by simp)).trans h.r7, by rw [hm]; exact h.st⟩

section
variable {σ : State} (hp : SpOk (VG.Proof.MlDsa.Arm.Sample.RejNtt.spOf σ) σ)
include hp

/-- Byte `k` of iteration `t`. -/
theorem byte_ok {t : Nat} (ht : t < 336) {s : State} (h : VG.Proof.MlDsa.Arm.Sample.RejNtt.LAt σ t s) {k : Nat} (hk : k < 3) :
    State.addr (s.gpr .r0 + BitVec.ofNat 32 k) = (VG.Proof.MlDsa.Arm.Sample.RejNtt.spOf σ).at' (840 + (3 * t + k)) ∧
      InRegions (s.rd ++ s.wr) ((VG.Proof.MlDsa.Arm.Sample.RejNtt.spOf σ).at' (840 + (3 * t + k))) 1 ∧
      s.mem ((VG.Proof.MlDsa.Arm.Sample.RejNtt.spOf σ).at' (840 + (3 * t + k))) = VG.Proof.MlDsa.Arm.Sample.RejNtt.Xb σ (3 * t + k) := by
  refine ⟨?_, inScrRd hp h.env (by omega), ?_⟩
  · rw [h.r0, ptr_add_add32, show 840 + 3 * t + k = 840 + (3 * t + k) by omega]; exact at_eq hp (by omega)
  · have := congrArg (fun L => L.getD (3 * t + k) 0) h.out
    rw [MlKem.bytesAt_getD _ _ (by omega), add_ofNat_add] at this
    exact this

omit hp in
theorem load_ok (s : State) {A₀ A₁ A₂ : Addr} {b₀ b₁ b₂ : Byte}
    (a0 : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = A₀) (a1 : State.addr (s.gpr .r0 + BitVec.ofNat 32 1) = A₁)
    (a2 : State.addr (s.gpr .r0 + BitVec.ofNat 32 2) = A₂) (i0 : InRegions (s.rd ++ s.wr) A₀ 1)
    (i1 : InRegions (s.rd ++ s.wr) A₁ 1) (i2 : InRegions (s.rd ++ s.wr) A₂ 1) (v0 : s.mem A₀ = b₀)
    (v1 : s.mem A₁ = b₁) (v2 : s.mem A₂ = b₂) :
    WP isa (.block rnLoad) s fun s' => s'.gpr .r10 = VG.Proof.MlDsa.Arm.Sample.RejNtt.rnw b₀ b₁ b₂ ∧
      (∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [rnLoad, VG.Proof.MlDsa.Arm.Sample.RejNtt.rnw, a0, a1, a2, i0, i1, i2, v0, v1, v2, and_self, and_true, true_and]
  exact fun r h8 h9 h10 => by simp [h8, h9, h10]

theorem pieceA {t : Nat} (ht : t < 336) {s : State} (h : VG.Proof.MlDsa.Arm.Sample.RejNtt.LAt σ t s) :
    WP isa (.block (rnLoad ++ jFull)) s (VG.Proof.MlDsa.Arm.Sample.RejNtt.M1 σ t) := by
  obtain ⟨a0, i0, v0⟩ := VG.Proof.MlDsa.Arm.Sample.RejNtt.byte_ok hp ht h (k := 0) (by decide)
  obtain ⟨a1, i1, v1⟩ := VG.Proof.MlDsa.Arm.Sample.RejNtt.byte_ok hp ht h (k := 1) (by decide)
  obtain ⟨a2, i2, v2⟩ := VG.Proof.MlDsa.Arm.Sample.RejNtt.byte_ok hp ht h (k := 2) (by decide)
  rw [Nat.add_zero] at v0
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.Arm.Sample.RejNtt.load_ok s a0 a1 a2 i0 i1 i2 v0 v1 v2) fun s1 ⟨g10, g1, m1, rd1, wr1, sp1⟩ => ?_
  have l1 : VG.Proof.MlDsa.Arm.Sample.RejNtt.LAt σ t s1 := h.same m1 (fun r hr => g1 r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
                                     decide) (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) rd1 wr1 sp1
  refine WP.mono (jFull_ok s1 l1.r2 (by have := VG.Proof.MlDsa.Arm.Sample.RejNtt.Lt_length_le σ t; omega)) fun s2 ⟨z2, g2, m2, rd2, wr2, sp2⟩ =>
    ⟨l1.same m2 (fun r hr => g2 r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
      rd2 wr2 sp2, by rw [g2 _ (by decide), g10], z2⟩

omit hp in
theorem tryA {t : Nat} {s : State} (h : VG.Proof.MlDsa.Arm.Sample.RejNtt.M1 σ t s) (hz : s.z = false) :
    WP isa (.block [.dp .sub .r11 .r10 (.reg .r7), .mov .r11 (.shifted .r11 .lsr 31), .cmp .r11 (.imm 0)]) s
      (VG.Proof.MlDsa.Arm.Sample.RejNtt.T1 σ t) := by
  have hl : (VG.Proof.MlDsa.Arm.Sample.RejNtt.Lt σ t).length < 256 := by
    have := h.z; rw [hz] at this; simp at this; omega
  have hv := VG.Proof.MlDsa.Arm.Sample.RejNtt.V_lt σ t
  refine WP.mono (sgn_ok s .r10 (.reg .r7) (y := BitVec.ofNat 32 8380417) (by simp [Op2.eval, h.lat.r7])
    (by rw [h.r10]; omega) (by decide)) fun s' ⟨z, g, m, rd, wr, sp⟩ => ⟨h.lat.same m (fun r hr => g r (by
      simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) rd wr sp,
    by rw [g _ (by decide), h.r10], hl, by rw [z, h.r10]; rfl⟩

omit hp in
theorem zw_V {σ : State} {t : Nat} (hq : (VG.Proof.MlDsa.Arm.Sample.RejNtt.V σ t).toNat < VG.Spec.MlDsa.q) : zw (Fin.ofNat VG.Spec.MlDsa.q (VG.Proof.MlDsa.Arm.Sample.RejNtt.V σ t).toNat) = VG.Proof.MlDsa.Arm.Sample.RejNtt.V σ t := by
  apply BitVec.eq_of_toNat_eq
  rw [zw_toNat, Fin.val_ofNat, Nat.mod_eq_of_lt hq]

theorem tryB {t : Nat} (ht : t < 336) {s : State} (h : VG.Proof.MlDsa.Arm.Sample.RejNtt.T1 σ t s) :
    WP isa (.ite .eq (.block []) (.block (storeJ .r10))) s (VG.Proof.MlDsa.Arm.Sample.RejNtt.M2 σ t) := by
  have hstep := VG.Proof.MlDsa.Arm.Sample.RejNtt.Lt_succ σ ht
  rw [rnStep, ifT (show (VG.Proof.MlDsa.Arm.Sample.RejNtt.Lt σ t).length < 256 from h.len), ← VG.Proof.MlDsa.Arm.Sample.RejNtt.rnw_toNat] at hstep
  refine WP.ite s.z rfl (fun e => ?_) (fun e => ?_)
  · -- rejected
    have hq : ¬ (VG.Proof.MlDsa.Arm.Sample.RejNtt.V σ t).toNat < VG.Spec.MlDsa.q := by
      have := h.z; rw [e] at this; simp at this; show ¬ _ < 8380417; omega
    rw [ifF hq] at hstep
    have l := h.lat
    exact WP.block_nil ⟨l.env, l.out, l.r0, by rw [hstep]; exact l.r2, l.r3, l.r7, by rw [hstep]; exact l.st⟩
  · have hq : (VG.Proof.MlDsa.Arm.Sample.RejNtt.V σ t).toNat < VG.Spec.MlDsa.q := by
      have := h.z; rw [e] at this; simp at this; show _ < 8380417; omega
    rw [ifT hq] at hstep
    have l := h.lat
    refine WP.mono (storeJ_stored hp l.env (by decide) l.r2 h.len l.st (x := Fin.ofNat VG.Spec.MlDsa.q (VG.Proof.MlDsa.Arm.Sample.RejNtt.V σ t).toNat)
      (by rw [h.r10, VG.Proof.MlDsa.Arm.Sample.RejNtt.zw_V hq])) fun s' ⟨st, r2, g, _, he, hf⟩ => ⟨he, ?_, by rw [g _ (by decide) (by decide), l.r0],
        by rw [hstep]; exact r2, by rw [g _ (by decide) (by decide), l.r3], by rw [g _ (by decide) (by decide), l.r7],
        by rw [hstep]; exact st⟩
    rw [MlKem.bytesAt_frame hf (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact (hp.a_scr.sub_right (sub_scr (a := 840) (n := 1008) (by omega))).symm) (by omega)]
    exact l.out

theorem pieceB {t : Nat} (ht : t < 336) {s : State} (h : VG.Proof.MlDsa.Arm.Sample.RejNtt.M1 σ t s) :
    WP isa (.ite .eq (.block []) rnTry) s (VG.Proof.MlDsa.Arm.Sample.RejNtt.M2 σ t) := by
  refine WP.ite s.z rfl (fun e => ?_) (fun e => ?_)
  · -- `j = 256`: nothing changes
    have hl : (VG.Proof.MlDsa.Arm.Sample.RejNtt.Lt σ t).length = 256 := by
      have := h.z; rw [e] at this; simp at this; have := VG.Proof.MlDsa.Arm.Sample.RejNtt.Lt_length_le σ t; omega
    have hstep : VG.Proof.MlDsa.Arm.Sample.RejNtt.Lt σ (t + 1) = VG.Proof.MlDsa.Arm.Sample.RejNtt.Lt σ t := by rw [VG.Proof.MlDsa.Arm.Sample.RejNtt.Lt_succ σ ht, rnStep_full hl]
    have l := h.lat
    exact WP.block_nil ⟨l.env, l.out, l.r0, by rw [hstep]; exact l.r2, l.r3, l.r7, by rw [hstep]; exact l.st⟩
  · exact WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sample.RejNtt.tryA h e) fun _ h1 => VG.Proof.MlDsa.Arm.Sample.RejNtt.tryB hp ht h1)

omit hp in
theorem pieceC {t : Nat} (ht : t < 336) {s : State} (h : VG.Proof.MlDsa.Arm.Sample.RejNtt.M2 σ t s) :
    WP isa (.block (VG.Impl.MlDsa.Arm.Sample.step 3)) s fun s' => VG.Proof.MlDsa.Arm.Sample.RejNtt.LAt σ (t + 1) s' ∧ s'.z = decide (t + 1 = 336) := by
  refine WP.mono (step_ok s (k := 3) (by decide)) fun s' ⟨r0, r3, z, g, m, rd, wr, sp⟩ =>
    ⟨⟨h.env.same m (g _ (by decide) (by decide)) (g _ (by decide) (by decide)) rd wr sp, by rw [m]; exact h.out,
      ?_, by rw [g _ (by decide) (by decide)]; exact h.r2, by rw [r3, h.r3]; exact count_sub (k := 1) ht,
      by rw [g _ (by decide) (by decide)]; exact h.r7, by rw [m]; exact h.st⟩, ?_⟩
  · rw [r0, h.r0, ptr_add_add32, show 840 + 3 * t + 3 = 840 + 3 * (t + 1) by omega]
  · rw [z, h.r3]; exact count_z (k := 1) ht (by decide) (by decide)

/-- An iteration. -/
theorem body_ok {t : Nat} (ht : t < 336) {s : State} (h : VG.Proof.MlDsa.Arm.Sample.RejNtt.LAt σ t s) :
    WP isa rnBody s fun s' => VG.Proof.MlDsa.Arm.Sample.RejNtt.LAt σ (t + 1) s' ∧ s'.z = decide (t + 1 = 336) :=
  WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sample.RejNtt.pieceA hp ht h) fun _ h1 => WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sample.RejNtt.pieceB hp ht h1) fun _ h2 => VG.Proof.MlDsa.Arm.Sample.RejNtt.pieceC ht h2))

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
variable {σ : State} (hp : SpOk (VG.Proof.MlDsa.Arm.Sample.RejNtt.spOf σ) σ)
include hp

omit hp in
theorem lat0 {s : State} (h : J6 168 1008 (VG.Proof.MlDsa.Arm.Sample.RejNtt.spOf σ) σ s) : WP isa (.block [.dp .add .r0 .r6 (.imm 840),
    .mov .r2 (.imm 0), .mov .r3 (.imm 336), .movw .r7 0xE001, .movt .r7 0x7F]) s (VG.Proof.MlDsa.Arm.Sample.RejNtt.LAt σ 0) :=
  WP.mono (VG.Proof.MlDsa.Arm.Sample.RejNtt.init_ok s) fun s' ⟨r0, r2, r3, r7, g5, g6, m, rd, wr, sp⟩ =>
    ⟨h.env.same m g5 g6 rd wr sp, by rw [m, h.out]; exact (VG.Proof.MlDsa.Sample.G_eq _ _).symm, by rw [r0, h.env.r6],
      by rw [r2]; rfl, by rw [r3], r7, by rw [m]; exact stored_nil _ _⟩

theorem loop_ok {s : State} (h : J6 168 1008 (VG.Proof.MlDsa.Arm.Sample.RejNtt.spOf σ) σ s) : WP isa rnLoop s (VG.Proof.MlDsa.Arm.Sample.RejNtt.LAt σ 336) :=
  WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sample.RejNtt.lat0 h) fun _ h0 =>
    wp_loop_ne (VG.Proof.MlDsa.Arm.Sample.RejNtt.LAt σ) (N := 336) (by decide) (fun t ht s h => VG.Proof.MlDsa.Arm.Sample.RejNtt.body_ok hp ht h) (fun _ h => h) h0)

omit hp in
theorem Lt_all : VG.Proof.MlDsa.Arm.Sample.RejNtt.Lt σ 336 = rnFold [] (VG.Proof.MlDsa.Arm.Sample.RejNtt.X σ) := by
  simp only [VG.Proof.MlDsa.Arm.Sample.RejNtt.Lt]; rw [List.take_of_length_le (by rw [VG.Proof.MlDsa.Arm.Sample.RejNtt.X_length])]

theorem end_ok {s : State} (h : VG.Proof.MlDsa.Arm.Sample.RejNtt.LAt σ 336 s) :
    WP isa (.block (retJ ++ epi)) s fun s' => s'.gpr .r0 = (if (rnFold [] (VG.Proof.MlDsa.Arm.Sample.RejNtt.X σ)).length = 256 then 1 else 0) ∧
      ((rnFold [] (VG.Proof.MlDsa.Arm.Sample.RejNtt.X σ)).length = 256 → PolyIs s'.mem (State.addr (σ.gpr .r1)) (toPoly (rnFold [] (VG.Proof.MlDsa.Arm.Sample.RejNtt.X σ)))) ∧
      abiPreserved σ s' :=
  WP.mono (retEpi_ok hp h.env h.r2 (VG.Proof.MlDsa.Arm.Sample.RejNtt.Lt_length_le _ _)) fun s' ⟨h0, hm, ha⟩ =>
    ⟨by rw [h0, VG.Proof.MlDsa.Arm.Sample.RejNtt.Lt_all], fun hf => by rw [hm]; exact VG.Proof.MlDsa.Arm.Sample.RejNtt.Lt_all ▸ stored_polyIs h.st (by rw [VG.Proof.MlDsa.Arm.Sample.RejNtt.Lt_all]; exact hf),
      ha⟩

/-- The function, from an entry state whose regions are those of a call. -/
theorem correct : WP isa Impl.MlDsa.Arm.Sample.rejNTT σ fun s' =>
    s'.gpr .r0 = (if (rnFold [] (VG.Proof.MlDsa.Arm.Sample.RejNtt.X σ)).length = 256 then 1 else 0) ∧
      ((rnFold [] (VG.Proof.MlDsa.Arm.Sample.RejNtt.X σ)).length = 256 → PolyIs s'.mem (State.addr (σ.gpr .r1)) (toPoly (rnFold [] (VG.Proof.MlDsa.Arm.Sample.RejNtt.X σ)))) ∧
      abiPreserved σ s' :=
  WP.seq (WP.mono (pro_rn hp rfl rfl rfl rfl rfl) fun _ h1 =>
    WP.seq (WP.mono (sponge_ok hp (rate := 168) (outlen := 1008) (by decide) (by decide) (by decide) (by decide) h1)
      fun _ h2 => WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sample.RejNtt.loop_ok hp h2) fun _ h3 => VG.Proof.MlDsa.Arm.Sample.RejNtt.end_ok hp h3)))

end

end VG.Proof.MlDsa.Arm.Sample.RejNtt

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Sample.RejNttCT`. -/
section

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

namespace VG.Proof.MlDsa.Arm.Sample.RejNtt

open VG VG.Arm
open VG.Proof.MlKem.Arm
open VG.Proof.MlDsa.Arm.Sample
open VG.Impl.MlDsa.Arm.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q G PolyIs)
open VG.Spec.Sha3 (bytesAt)

/-- Two runs, from entry states that agree on the public data. -/
structure Two (σ₁ σ₂ : State) : Prop where
  hp₁ : SpOk (VG.Proof.MlDsa.Arm.Sample.RejNtt.spOf σ₁) σ₁
  hp₂ : SpOk (VG.Proof.MlDsa.Arm.Sample.RejNtt.spOf σ₂) σ₂
  sp : σ₁.sp = σ₂.sp
  r0 : σ₁.gpr .r0 = σ₂.gpr .r0
  r1 : σ₁.gpr .r1 = σ₂.gpr .r1
  r2 : σ₁.gpr .r2 = σ₂.gpr .r2
  B : VG.Proof.MlDsa.Arm.Sample.RejNtt.B σ₁ = VG.Proof.MlDsa.Arm.Sample.RejNtt.B σ₂

theorem nil_regs {R : State → State → Prop} : ∀ x y, R x y → ∀ r ∈ ([] : List Reg), x.gpr r = y.gpr r :=
  fun _ _ _ _ h => absurd h List.not_mem_nil

section
variable {σ₁ σ₂ : State} (h : VG.Proof.MlDsa.Arm.Sample.RejNtt.Two σ₁ σ₂)
include h

theorem sp_eq : VG.Proof.MlDsa.Arm.Sample.RejNtt.spOf σ₂ = VG.Proof.MlDsa.Arm.Sample.RejNtt.spOf σ₁ := by simp only [VG.Proof.MlDsa.Arm.Sample.RejNtt.spOf, h.r0, h.r1, h.r2]

theorem X_eq : VG.Proof.MlDsa.Arm.Sample.RejNtt.X σ₁ = VG.Proof.MlDsa.Arm.Sample.RejNtt.X σ₂ := by simp only [VG.Proof.MlDsa.Arm.Sample.RejNtt.X, h.B]

theorem Lt_eq (t : Nat) : VG.Proof.MlDsa.Arm.Sample.RejNtt.Lt σ₁ t = VG.Proof.MlDsa.Arm.Sample.RejNtt.Lt σ₂ t := by simp only [VG.Proof.MlDsa.Arm.Sample.RejNtt.Lt, VG.Proof.MlDsa.Arm.Sample.RejNtt.X_eq h]

theorem V_eq (t : Nat) : VG.Proof.MlDsa.Arm.Sample.RejNtt.V σ₁ t = VG.Proof.MlDsa.Arm.Sample.RejNtt.V σ₂ t := by simp only [VG.Proof.MlDsa.Arm.Sample.RejNtt.V, VG.Proof.MlDsa.Arm.Sample.RejNtt.Xb, VG.Proof.MlDsa.Arm.Sample.RejNtt.X_eq h]

/-! ## The loop -/

theorem try_ct {t : Nat} :
    RelCT isa (fun a b => (VG.Proof.MlDsa.Arm.Sample.RejNtt.M1 σ₁ t a ∧ VG.Proof.MlDsa.Arm.Sample.RejNtt.M1 σ₂ t b) ∧ isa.eval .eq a = some false) rnTry fun _ _ => True := by
  have hz : ∀ a b, (VG.Proof.MlDsa.Arm.Sample.RejNtt.M1 σ₁ t a ∧ VG.Proof.MlDsa.Arm.Sample.RejNtt.M1 σ₂ t b) ∧ isa.eval .eq a = some false → a.z = false ∧ b.z = false :=
    fun a b hab => by
      have e : a.z = false := Option.some.inj hab.2
      refine ⟨e, ?_⟩
      rw [← e, hab.1.1.z, hab.1.2.z, VG.Proof.MlDsa.Arm.Sample.RejNtt.Lt_eq h]
  refine RelCT.seq (R := fun a b => VG.Proof.MlDsa.Arm.Sample.RejNtt.T1 σ₁ t a ∧ VG.Proof.MlDsa.Arm.Sample.RejNtt.T1 σ₂ t b) (relW (taintRel [] VG.Proof.MlDsa.Arm.Sample.RejNtt.nil_regs (by taint_decide))
    fun a b hab => ⟨VG.Proof.MlDsa.Arm.Sample.RejNtt.tryA hab.1.1 (hz a b hab).1, VG.Proof.MlDsa.Arm.Sample.RejNtt.tryA hab.1.2 (hz a b hab).2⟩) ?_
  refine RelCT.ite (fun a b hab => by
    show some a.z = some b.z; rw [hab.1.z, hab.2.z, VG.Proof.MlDsa.Arm.Sample.RejNtt.V_eq h]) (taintRel [] VG.Proof.MlDsa.Arm.Sample.RejNtt.nil_regs (by taint_decide))
    (taintRel [.r2, .r5] (fun a b hab r hr => ?_) (by taint_decide))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [hab.1.1.lat.r2, hab.1.2.lat.r2, VG.Proof.MlDsa.Arm.Sample.RejNtt.Lt_eq h]
  · rw [hab.1.1.lat.env.r5, hab.1.2.lat.env.r5, VG.Proof.MlDsa.Arm.Sample.RejNtt.sp_eq h]

theorem body_ct {t : Nat} (ht : t < 336) :
    RelCT isa (fun a b => VG.Proof.MlDsa.Arm.Sample.RejNtt.LAt σ₁ t a ∧ VG.Proof.MlDsa.Arm.Sample.RejNtt.LAt σ₂ t b) rnBody fun a b =>
      (VG.Proof.MlDsa.Arm.Sample.RejNtt.LAt σ₁ (t + 1) a ∧ a.z = decide (t + 1 = 336)) ∧ (VG.Proof.MlDsa.Arm.Sample.RejNtt.LAt σ₂ (t + 1) b ∧ b.z = decide (t + 1 = 336)) := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  refine relW ?_ fun a b hab => ⟨VG.Proof.MlDsa.Arm.Sample.RejNtt.body_ok hp₁ ht hab.1, VG.Proof.MlDsa.Arm.Sample.RejNtt.body_ok hp₂ ht hab.2⟩
  refine RelCT.seq (R := fun a b => VG.Proof.MlDsa.Arm.Sample.RejNtt.M1 σ₁ t a ∧ VG.Proof.MlDsa.Arm.Sample.RejNtt.M1 σ₂ t b) (relW (taintRel [.r0, .r2] (fun a b hab r hr => ?_)
    (by taint_decide)) fun a b hab => ⟨VG.Proof.MlDsa.Arm.Sample.RejNtt.pieceA hp₁ ht hab.1, VG.Proof.MlDsa.Arm.Sample.RejNtt.pieceA hp₂ ht hab.2⟩) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hab.1.r0, hab.2.r0, h.r2]
    · rw [hab.1.r2, hab.2.r2, VG.Proof.MlDsa.Arm.Sample.RejNtt.Lt_eq h]
  refine RelCT.seq (R := fun a b => VG.Proof.MlDsa.Arm.Sample.RejNtt.M2 σ₁ t a ∧ VG.Proof.MlDsa.Arm.Sample.RejNtt.M2 σ₂ t b) (relW ?_
    fun a b hab => ⟨VG.Proof.MlDsa.Arm.Sample.RejNtt.pieceB hp₁ ht hab.1, VG.Proof.MlDsa.Arm.Sample.RejNtt.pieceB hp₂ ht hab.2⟩) (taintRel [] VG.Proof.MlDsa.Arm.Sample.RejNtt.nil_regs (by taint_decide))
  exact RelCT.ite (fun a b hab => by show some a.z = some b.z; rw [hab.1.z, hab.2.z, VG.Proof.MlDsa.Arm.Sample.RejNtt.Lt_eq h])
    (taintRel [] VG.Proof.MlDsa.Arm.Sample.RejNtt.nil_regs (by taint_decide)) (VG.Proof.MlDsa.Arm.Sample.RejNtt.try_ct h)

theorem loop_ct :
    RelCT isa (fun a b => VG.Proof.MlDsa.Arm.Sample.RejNtt.LAt σ₁ 0 a ∧ VG.Proof.MlDsa.Arm.Sample.RejNtt.LAt σ₂ 0 b) (.loop rnBody .ne) fun a b =>
      VG.Proof.MlDsa.Arm.Sample.RejNtt.LAt σ₁ 336 a ∧ VG.Proof.MlDsa.Arm.Sample.RejNtt.LAt σ₂ 336 b := by
  refine RelCT.mono (RelCT.loop (M := isa) (body := rnBody) (c := .ne)
    (Q := fun a b => VG.Proof.MlDsa.Arm.Sample.RejNtt.LAt σ₁ 336 a ∧ VG.Proof.MlDsa.Arm.Sample.RejNtt.LAt σ₂ 336 b)
    (fun n a b => ∃ t, t < 336 ∧ n = 336 - t ∧ VG.Proof.MlDsa.Arm.Sample.RejNtt.LAt σ₁ t a ∧ VG.Proof.MlDsa.Arm.Sample.RejNtt.LAt σ₂ t b) (fun n => ?_) 336)
    (fun a b hab => ⟨0, by decide, rfl, hab⟩) (fun _ _ h => h)
  refine RelCT.mono (P := fun a b => ∃ t, t < 336 ∧ n = 336 - t ∧ VG.Proof.MlDsa.Arm.Sample.RejNtt.LAt σ₁ t a ∧ VG.Proof.MlDsa.Arm.Sample.RejNtt.LAt σ₂ t b)
    (RelCT.exists_ fun t => ?_) (fun _ _ hab => hab) (fun _ _ h => h)
  by_cases ht : t < 336
  · by_cases hn : n = 336 - t
    · refine RelCT.mono (P := fun a b => VG.Proof.MlDsa.Arm.Sample.RejNtt.LAt σ₁ t a ∧ VG.Proof.MlDsa.Arm.Sample.RejNtt.LAt σ₂ t b) (VG.Proof.MlDsa.Arm.Sample.RejNtt.body_ct h ht) (fun _ _ hab => hab.2.2)
        fun a b ⟨⟨i₁, z₁⟩, ⟨i₂, z₂⟩⟩ => ⟨?_, fun e => ?_, fun e => ?_⟩
      · show some (!a.z) = some (!b.z); rw [z₁, z₂]
      · have : t + 1 = 336 := by
          have e' : (!a.z) = false := Option.some.inj e
          rw [z₁] at e'; simpa using e'
        rw [this] at i₁ i₂; exact ⟨i₁, i₂⟩
      · have : t + 1 ≠ 336 := by
          have e' : (!a.z) = true := Option.some.inj e
          rw [z₁] at e'; simpa using e'
        exact ⟨336 - (t + 1), by omega, t + 1, by omega, rfl, i₁, i₂⟩
    · exact RelCT.of_false fun _ _ hab => hn hab.2.1
  · exact RelCT.of_false fun _ _ hab => ht hab.1

/-! ## The whole function -/

theorem all_ct : RelCT isa (fun a b => a = σ₁ ∧ b = σ₂) Impl.MlDsa.Arm.Sample.rejNTT fun _ _ => True := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  have eP := VG.Proof.MlDsa.Arm.Sample.RejNtt.sp_eq h
  have hp₂' : SpOk (VG.Proof.MlDsa.Arm.Sample.RejNtt.spOf σ₁) σ₂ := eP ▸ hp₂
  refine RelCT.seq (R := fun a b => J0 (VG.Proof.MlDsa.Arm.Sample.RejNtt.spOf σ₁) σ₁ a ∧ J0 (VG.Proof.MlDsa.Arm.Sample.RejNtt.spOf σ₁) σ₂ b) (relW (taintRel [.r0, .r1, .r2]
    (fun a b hab r hr => ?_) (by taint_decide)) fun a b hab => ⟨?_, ?_⟩) ?_
  · rw [hab.1, hab.2]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [h.r0, h.r1, h.r2]
  · rw [hab.1]; exact pro_rn hp₁ rfl rfl rfl rfl rfl
  · rw [hab.2]; exact pro_rn hp₂' h.r0.symm h.r1.symm h.r2.symm rfl rfl
  refine RelCT.seq (sponge_ct hp₁ hp₂' h.sp (rate := 168) (outlen := 1008) (by decide) (by decide) (by decide)
    (by decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine RelCT.seq (R := fun a b => VG.Proof.MlDsa.Arm.Sample.RejNtt.LAt σ₁ 336 a ∧ VG.Proof.MlDsa.Arm.Sample.RejNtt.LAt σ₂ 336 b) (RelCT.seq (R := fun a b => VG.Proof.MlDsa.Arm.Sample.RejNtt.LAt σ₁ 0 a ∧ VG.Proof.MlDsa.Arm.Sample.RejNtt.LAt σ₂ 0 b)
    (relW (taintRel [] VG.Proof.MlDsa.Arm.Sample.RejNtt.nil_regs (by taint_decide)) fun a b hab => ⟨VG.Proof.MlDsa.Arm.Sample.RejNtt.lat0 hab.1, VG.Proof.MlDsa.Arm.Sample.RejNtt.lat0 (eP ▸ hab.2)⟩) (VG.Proof.MlDsa.Arm.Sample.RejNtt.loop_ct h)) ?_
  exact taintRel [.r6] (fun a b hab r hr => by
    rw [List.mem_singleton] at hr; subst hr; rw [hab.1.env.r6, hab.2.env.r6, VG.Proof.MlDsa.Arm.Sample.RejNtt.sp_eq h]) (by taint_decide)

end

/-! ## `Verified` -/

theorem spOk_of {s : State} (h : (Spec.MlDsa.rejNTTContract Arm.abi 8).pre s) : SpOk (VG.Proof.MlDsa.Arm.Sample.RejNtt.spOf s) s := by
  sig_pre [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h8, -, hrd, hwr, d1, d2, d3, b1, b2, b3, f0, f1, f2⟩ := h
  exact ⟨by rw [hrd]; exact List.mem_singleton_self _, hwr, d1, d2, d3, b1, b2, b3, f0,
    show (34 : Nat) < 2 ^ 32 by decide, f1, f2, h8⟩

theorem leakBytes_inj : ∀ {a b : List Byte}, a.map (fun x => x.toNat) = b.map (fun x => x.toNat) → a = b
  | [], [], _ => rfl
  | x :: a, y :: b, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, VG.Proof.MlDsa.Arm.Sample.RejNtt.leakBytes_inj h.2]
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
    Verified Arm.target Impl.MlDsa.Arm.Sample.rejNTT (Spec.MlDsa.rejNTTContract Arm.abi 8) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, h0, hpoly, ha⟩ := VG.Proof.MlDsa.Arm.Sample.RejNtt.correct (VG.Proof.MlDsa.Arm.Sample.RejNtt.spOk_of hs)
    refine ⟨t, s', he, ha, ?_⟩
    sig_post [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val]
    rw [setWidth_append32, h0]
    by_cases hf : (rnFold [] (VG.Proof.MlDsa.Arm.Sample.RejNtt.X s)).length = 256
    · rw [ifT hf]
      have hpi := hpoly hf
      exact ⟨fun _ => hpi.1, .inl ⟨rfl, { Spec.MlDsa.minBounds with rejNTT := 1008 }, by
        show Spec.MlDsa.rejNTTPoly 1008 _ = _
        exact (rejNTT_some hf).trans (congrArg some hpi.2.symm)⟩⟩
    · rw [ifF hf]
      exact ⟨fun e => absurd e (by decide), .inr ⟨rfl, rejNTT_none (B := 1008) (by decide) (by decide) hf⟩⟩
  · sig_pub [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at hpub
    obtain ⟨hsp, hb, h0, h1, h2⟩ := hpub
    exact (VG.Proof.MlDsa.Arm.Sample.RejNtt.all_ct ⟨VG.Proof.MlDsa.Arm.Sample.RejNtt.spOk_of h₁, VG.Proof.MlDsa.Arm.Sample.RejNtt.spOk_of h₂, hsp, h0, h1, h2, VG.Proof.MlDsa.Arm.Sample.RejNtt.leakBytes_inj hb⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩
      e₁ e₂).1
  · refine ⟨VG.Proof.MlDsa.Arm.Sample.RejNtt.satState, ?_⟩
    sig_sat_check [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]

end VG.Proof.MlDsa.Arm.Sample

end
