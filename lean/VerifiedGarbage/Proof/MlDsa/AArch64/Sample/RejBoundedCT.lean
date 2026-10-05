import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejNttCT
import VerifiedGarbage.Proof.MlDsa.Sample.Signs
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejBounded
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Ball

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejBoundedLoop`. -/
section

/-!
# ML-DSA on AArch64: the loop of `vg_mldsa_rej_bounded_poly`

The coefficient of a half-byte, computed without a branch (`rbVal`), is the
one of `CoeffFromHalfByte`, modulo `q`, for every half-byte it accepts
(`rbF_eq`, by evaluation); so a try does what `hbTry` does (`try_ok`), storing
a coefficient either way and counting it only if it is accepted, and an
iteration what `rbStep` does (`step_ok`). The loop reads only the output, and
writes only `a`.
-/

namespace VG.Proof.MlDsa.AArch64.Sample.RejBounded

open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_mov wp_movz wp_addImm wp_subImm wp_strw wp_ldrb wp_sub
  wp_add wp_lsr wp_lsl wp_and wp_madd ptr_zero ptr_add toNat_sub_n toNat_add_n toNat_lsl_n toNat_and_mask
  toNat_byte toNat_lsr count_loop eval_zero eq_zero_iff)
open VG.Impl.MlDsa.AArch64.Sample
open VG.Impl.MlKem.AArch64 (mov csub)
open VG.Proof.MlDsa.Sample
open VG.Proof.MlDsa.AArch64.Sample.RejNtt (lt_bit movQ_ok q_eq stored_past)
open VG.Spec.MlDsa (coeffAt Zq q ofInt)

/-! ## The coefficient of a half-byte -/

/-- `x - k`, plus `k` if that is negative, as `csub` computes it. -/
def csubF (k x : BitVec 64) : BitVec 64 := (x - k) + ((x - k) >>> 63) * k

/-- `(η - x) mod q`, as the end of `rbVal` computes it. -/
def etaF (η x : BitVec 64) : BitVec 64 := (η - x) + ((η - x) >>> 63) * BitVec.ofNat 64 q

/-- What `rbVal η` computes of the half-byte `x`. -/
def rbF : Nat → BitVec 64 → BitVec 64
  | 2, x => VG.Proof.MlDsa.AArch64.Sample.RejBounded.etaF 2 (VG.Proof.MlDsa.AArch64.Sample.RejBounded.csubF 5 (VG.Proof.MlDsa.AArch64.Sample.RejBounded.csubF 10 x))
  | _, x => VG.Proof.MlDsa.AArch64.Sample.RejBounded.etaF 4 x

theorem rbF_eq2 : ∀ b < 15, (VG.Proof.MlDsa.AArch64.Sample.RejBounded.rbF 2 (BitVec.ofNat 64 b)).setWidth 32 = zw (ofInt (rbC 2 b)) := by decide

theorem rbF_eq4 : ∀ b < 9, (VG.Proof.MlDsa.AArch64.Sample.RejBounded.rbF 4 (BitVec.ofNat 64 b)).setWidth 32 = zw (ofInt (rbC 4 b)) := by decide

theorem rbF_eq {η : Nat} (hη : η = 2 ∨ η = 4) {b : Nat} (hb : b < rbB η) :
    (VG.Proof.MlDsa.AArch64.Sample.RejBounded.rbF η (BitVec.ofNat 64 b)).setWidth 32 = zw (ofInt (rbC η b)) := by
  rcases hη with rfl | rfl
  · exact VG.Proof.MlDsa.AArch64.Sample.RejBounded.rbF_eq2 b hb
  · exact VG.Proof.MlDsa.AArch64.Sample.RejBounded.rbF_eq4 b hb

/-- The constants the loop keeps in registers. -/
structure Consts (η : Nat) (u : State) : Prop where
  x9 : u.gpr .x9 = BitVec.ofNat 64 q
  x10 : u.gpr .x10 = BitVec.ofNat 64 η
  x11 : u.gpr .x11 = BitVec.ofNat 64 15
  x15 : u.gpr .x15 = BitVec.ofNat 64 (rbB η)
  x16 : u.gpr .x16 = BitVec.ofNat 64 10
  x17 : u.gpr .x17 = BitVec.ofNat 64 5

theorem Consts.keep {η : Nat} {u u' : State} (h : VG.Proof.MlDsa.AArch64.Sample.RejBounded.Consts η u) {rs : List Reg} (hk : Keep rs u u')
    (hr : ∀ r ∈ rs, r ∉ [Reg.x9, .x10, .x11, .x15, .x16, .x17] := by decide) : VG.Proof.MlDsa.AArch64.Sample.RejBounded.Consts η u' :=
  ⟨by rw [hk.gpr _ fun h' => hr _ h' (by simp), h.x9], by rw [hk.gpr _ fun h' => hr _ h' (by simp), h.x10],
    by rw [hk.gpr _ fun h' => hr _ h' (by simp), h.x11], by rw [hk.gpr _ fun h' => hr _ h' (by simp), h.x15],
    by rw [hk.gpr _ fun h' => hr _ h' (by simp), h.x16], by rw [hk.gpr _ fun h' => hr _ h' (by simp), h.x17]⟩

theorem val_ok {η : Nat} (hη : η = 2 ∨ η = 4) {u : State} (hc : VG.Proof.MlDsa.AArch64.Sample.RejBounded.Consts η u) :
    WP isa (.block (rbVal η)) u fun u' => Only [.x13, .x14] u u' ∧ u'.gpr .x13 = VG.Proof.MlDsa.AArch64.Sample.RejBounded.rbF η (u.gpr .x7) := by
  rcases hη with rfl | rfl
  · simp only [rbVal, csub, List.cons_append, List.nil_append]
    refine wp_mov fun u₁ o₁ e₁ => wp_sub fun u₂ o₂ e₂ => wp_lsr (by decide) fun u₃ o₃ e₃ =>
      wp_madd fun u₄ o₄ e₄ => wp_sub fun u₅ o₅ e₅ => wp_lsr (by decide) fun u₆ o₆ e₆ =>
      wp_madd fun u₇ o₇ e₇ => wp_sub fun u₈ o₈ e₈ => wp_lsr (by decide) fun u₉ o₉ e₉ =>
      wp_madd fun u₁₀ o₁₀ e₁₀ => wp_nil ⟨(((((((((o₁.trans o₂).trans o₃).trans o₄).trans o₅).trans o₆).trans
        o₇).trans o₈).trans o₉).trans o₁₀).mono, ?_⟩
    have a2 : u₂.gpr .x13 = u.gpr .x7 - BitVec.ofNat 64 10 := by rw [e₂, e₁, o₁.get .x16, hc.x16]
    have a4 : u₄.gpr .x13 = VG.Proof.MlDsa.AArch64.Sample.RejBounded.csubF (BitVec.ofNat 64 10) (u.gpr .x7) := by
      rw [e₄, o₃.get .x13, e₃, a2, o₃.get .x16, o₂.get .x16, o₁.get .x16, hc.x16]; rfl
    have a5 : u₅.gpr .x13 = VG.Proof.MlDsa.AArch64.Sample.RejBounded.csubF (BitVec.ofNat 64 10) (u.gpr .x7) - BitVec.ofNat 64 5 := by
      rw [e₅, a4, o₄.get .x17, o₃.get .x17, o₂.get .x17, o₁.get .x17, hc.x17]
    have a7 : u₇.gpr .x13 = VG.Proof.MlDsa.AArch64.Sample.RejBounded.csubF (BitVec.ofNat 64 5) (VG.Proof.MlDsa.AArch64.Sample.RejBounded.csubF (BitVec.ofNat 64 10) (u.gpr .x7)) := by
      rw [e₇, o₆.get .x13, e₆, a5, o₆.get .x17, o₅.get .x17, o₄.get .x17, o₃.get .x17, o₂.get .x17,
        o₁.get .x17, hc.x17]; rfl
    have a8 : u₈.gpr .x13 = BitVec.ofNat 64 2 - VG.Proof.MlDsa.AArch64.Sample.RejBounded.csubF (BitVec.ofNat 64 5) (VG.Proof.MlDsa.AArch64.Sample.RejBounded.csubF (BitVec.ofNat 64 10) (u.gpr .x7)) := by
      rw [e₈, a7, o₇.get .x10, o₆.get .x10, o₅.get .x10, o₄.get .x10, o₃.get .x10, o₂.get .x10, o₁.get .x10,
        hc.x10]
    rw [e₁₀, o₉.get .x13, e₉, a8, o₉.get .x9, o₈.get .x9, o₇.get .x9, o₆.get .x9, o₅.get .x9, o₄.get .x9,
      o₃.get .x9, o₂.get .x9, o₁.get .x9, hc.x9]; rfl
  · simp only [rbVal]
    refine wp_sub fun u₁ o₁ e₁ => wp_lsr (by decide) fun u₂ o₂ e₂ => wp_madd fun u₃ o₃ e₃ =>
      wp_nil ⟨((o₁.trans o₂).trans o₃).mono, ?_⟩
    rw [e₃, o₂.get .x13, e₂, e₁, o₂.get .x9, o₁.get .x9, hc.x9, hc.x10]; rfl

theorem rbB_le {η : Nat} : rbB η ≤ 15 := by unfold rbB; split <;> omega

theorem hbTry_length' {η : Nat} (hη : η = 2 ∨ η = 4) (L : List Zq) (b : Nat) :
    (hbTry η L b).length = L.length + if b < rbB η then 1 else 0 := by
  rw [hbTry_eq hη]; split <;> simp

/-- A try of the half-byte `b` in `x7`: what `hbTry` does, the coefficient
stored as coefficient `j` either way. -/
theorem try_ok {η : Nat} (hη : η = 2 ∨ η = 4) {aP : Addr} {L : List Zq} {b : Nat} (hb : b < 16) {u : State}
    (hc : VG.Proof.MlDsa.AArch64.Sample.RejBounded.Consts η u) (h7 : u.gpr .x7 = BitVec.ofNat 64 b) (h3 : u.gpr .x3 = coeffAddr aP L.length)
    (h4 : (u.gpr .x4).toNat = 256 - L.length) (hl : L.length < 256) (hst : Stored u.mem aP L)
    (hw : InRegions u.wr (coeffAddr aP L.length) 4) :
    WP isa (.block (rbTry η)) u fun u' => Keep [.x3, .x4, .x8, .x12, .x13, .x14] u u' ∧
      Frame [polyR aP] u.mem u'.mem ∧ u'.gpr .x3 = coeffAddr aP (hbTry η L b).length ∧
      (u'.gpr .x4).toNat = 256 - (hbTry η L b).length ∧ Stored u'.mem aP (hbTry η L b) := by
  unfold rbTry
  refine wp_sub fun u₁ o₁ e₁ => wp_lsr (by decide) fun u₂ o₂ e₂ => ?_
  have v12 : (u₂.gpr .x12).toNat = if b < rbB η then 1 else 0 := by
    rw [e₂, e₁]
    exact lt_bit (by rw [h7, BitVec.toNat_ofNat]; omega) (by rw [hc.x15, BitVec.toNat_ofNat]; have := @VG.Proof.MlDsa.AArch64.Sample.RejBounded.rbB_le η; omega)
      (by omega) (by have := @VG.Proof.MlDsa.AArch64.Sample.RejBounded.rbB_le η; omega)
  have hc₂ : VG.Proof.MlDsa.AArch64.Sample.RejBounded.Consts η u₂ := hc.keep (o₁.keep.trans o₂.keep)
  rw [List.append_eq, List.append_eq, List.nil_append, WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.RejBounded.val_ok hη hc₂) fun u₃ ⟨o₃, e₃⟩ => ?_
  have x7 : u₂.gpr .x7 = BitVec.ofNat 64 b := by rw [o₂.get .x7, o₁.get .x7, h7]
  rw [x7] at e₃
  refine wp_strw (a := coeffAddr aP L.length) (by decide)
    (by rw [o₃.get .x3, o₂.get .x3, o₁.get .x3, h3, ptr_zero]) (by rw [o₃.wr, o₂.wr, o₁.wr]; exact hw)
    fun u₄ o₄ => wp_lsl (by decide) fun u₅ o₅ e₅ => wp_add fun u₆ o₆ e₆ => wp_sub fun u₇ o₇ e₇ => wp_nil ?_
  have k₇ := (((((o₁.keep.trans o₂.keep).trans o₃.keep).trans o₄.keep).trans o₅.keep).trans o₆.keep).trans
    o₇.keep
  have m₇ : u₇.mem = u.mem.writeW (coeffAddr aP L.length) ((VG.Proof.MlDsa.AArch64.Sample.RejBounded.rbF η (BitVec.ofNat 64 b)).setWidth 32) := by
    rw [o₇.mem, o₆.mem, o₅.mem, o₄.mem, e₃, o₃.mem, o₂.mem, o₁.mem]
  have x12 : (u₆.gpr .x12).toNat = if b < rbB η then 1 else 0 := by
    rw [o₆.get .x12, o₅.get .x12, o₄.gpr, o₃.get .x12, v12]
  have x14 : u₅.gpr .x14 = BitVec.ofNat 64 (4 * if b < rbB η then 1 else 0) := by
    apply BitVec.eq_of_toNat_eq
    have c12 : (u₄.gpr .x12).toNat = if b < rbB η then 1 else 0 := by rw [o₄.gpr, o₃.get .x12, v12]
    have hl' : (u₄.gpr .x12).toNat * 2 ^ 2 < 2 ^ 64 := by rw [c12]; split <;> decide
    rw [e₅, toNat_lsl_n hl', c12, BitVec.toNat_ofNat]
    split <;> decide
  have c4 : (u₆.gpr .x4).toNat = 256 - L.length := by
    rw [o₆.get .x4, o₅.get .x4, o₄.gpr, o₃.get .x4, o₂.get .x4, o₁.get .x4, h4]
  refine ⟨k₇.mono, ?_, ?_, ?_, ?_⟩
  · rw [m₇]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hl)
  · rw [o₇.get .x3, e₆, x14, o₅.get .x3, o₄.gpr, o₃.get .x3, o₂.get .x3, o₁.get .x3, h3, coeffAddr, coeffAddr,
      ptr_add, VG.Proof.MlDsa.AArch64.Sample.RejBounded.hbTry_length' hη, Nat.mul_add]
  · have hx : (u₆.gpr .x12).toNat ≤ (u₆.gpr .x4).toNat := by rw [x12, c4]; split <;> omega
    rw [e₇, toNat_sub_n hx, c4, x12, VG.Proof.MlDsa.AArch64.Sample.RejBounded.hbTry_length' hη]
    omega
  · rw [m₇, hbTry_eq hη]
    split
    · rename_i hr
      rw [VG.Proof.MlDsa.AArch64.Sample.RejBounded.rbF_eq hη hr]; exact stored_snoc hst hl _
    · exact stored_past hst (Nat.le_refl _) hl _

end VG.Proof.MlDsa.AArch64.Sample.RejBounded

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejBounded`. -/
section

/-!
# ML-DSA on AArch64: `vg_mldsa_rej_bounded_poly`, correctness

The function runs in pieces: the prologue, the sponge (544 bytes of SHAKE256
of the seed), the branch on `η` to its loop, and the end. Iteration `t` of the
loop starts from `LAt t`, with the coefficients `rbFold` samples from the
first `t` bytes of output stored; it loads byte `t` (`LB`), tries its low
half-byte if `j < 256` (`LM`), and then its high half-byte if still `j < 256`.
The pieces are separate lemmas, which the proof of constant time
(`RejBoundedCT.lean`) uses too.
-/

namespace VG.Proof.MlDsa.AArch64.Sample

open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep only_write wp_nil wp_mov wp_movz wp_subImm wp_addImm wp_ldrb wp_and wp_lsr
  wp_lsl ptr_add ptr_zero toNat_lsr toNat_sub_n toNat_byte eval_zero eq_zero_iff count_loop)
open VG.Impl.MlDsa.AArch64.Sample
open VG.Impl.MlKem.AArch64 (mov)
open VG.Proof.MlDsa.Sample
open VG.Proof.MlDsa.AArch64.Sample.RejBounded (Consts try_ok)
open VG.Spec.MlDsa (Zq q H PolyIs coeffAt rejBoundedLeak n)
open VG.Spec.Sha3 (bytesAt)

/-- `η`, the `u32` argument in `w1`. -/
abbrev etaOf (s : State) : Nat := ((s.gpr .x1).setWidth 32).toNat

/-- `vg_mldsa_rej_bounded_poly(seed = x0, eta = w1, a = x2, scratch = x3) -> w0`,
with 16 bytes of stack below `sp`. -/
def rbK : Contract isa where
  pre s :=
    let seed : Region := ⟨s.gpr .x0, 66⟩
    let a : Region := ⟨s.gpr .x2, 1024⟩
    let scratch : Region := ⟨s.gpr .x3, 2048⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [seed] ∧ s.wr = [a, scratch] ∧ seed.Disjoint a ∧ seed.Disjoint scratch ∧
    a.Disjoint scratch ∧ 16 ≤ s.sp.toNat ∧ stack.Disjoint seed ∧ stack.Disjoint a ∧
    stack.Disjoint scratch ∧ (VG.Proof.MlDsa.AArch64.Sample.etaOf s = 2 ∨ VG.Proof.MlDsa.AArch64.Sample.etaOf s = 4)
  post s s' :=
    (s'.gpr .x0).setWidth 32 =
        (if (rbFold (VG.Proof.MlDsa.AArch64.Sample.etaOf s) [] (H (bytesAt s.mem (s.gpr .x0) 66) 544)).length = 256 then 1 else 0) ∧
      ((rbFold (VG.Proof.MlDsa.AArch64.Sample.etaOf s) [] (H (bytesAt s.mem (s.gpr .x0) 66) 544)).length = 256 →
        PolyIs s'.mem (s.gpr .x2) (toPoly (rbFold (VG.Proof.MlDsa.AArch64.Sample.etaOf s) [] (H (bytesAt s.mem (s.gpr .x0) 66) 544))))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ (s₁.gpr .x1).setWidth 32 = (s₂.gpr .x1).setWidth 32 ∧
    s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp ∧
    rejBoundedLeak (VG.Proof.MlDsa.AArch64.Sample.etaOf s₁) (bytesAt s₁.mem (s₁.gpr .x0) 66) =
      rejBoundedLeak (VG.Proof.MlDsa.AArch64.Sample.etaOf s₂) (bytesAt s₂.mem (s₂.gpr .x0) 66)

namespace RejBounded

/-- The call. -/
abbrev spOf (σ : State) : Sp :=
  ⟨σ.gpr .x0, 66, σ.gpr .x3, σ.gpr .x2, ((σ.gpr .x1).setWidth 32).setWidth 64⟩

/-- The XOF output. -/
abbrev X (σ : State) : List Byte := H ((VG.Proof.MlDsa.AArch64.Sample.RejBounded.spOf σ).msg σ) 544

theorem X_length (σ : State) : (VG.Proof.MlDsa.AArch64.Sample.RejBounded.X σ).length = 544 := VG.Proof.MlDsa.Sample.H_length _ _

/-- The coefficients sampled from the first `t` bytes. -/
abbrev Lt (σ : State) (t : Nat) : List Zq := rbFold (VG.Proof.MlDsa.AArch64.Sample.etaOf σ) [] ((VG.Proof.MlDsa.AArch64.Sample.RejBounded.X σ).take t)

/-- Byte `t` of the output. -/
abbrev Z (σ : State) (t : Nat) : Byte := (VG.Proof.MlDsa.AArch64.Sample.RejBounded.X σ).getD t 0

/-- After the low half-byte of byte `t`. -/
abbrev Lm (σ : State) (t : Nat) : List Zq := hbTry (VG.Proof.MlDsa.AArch64.Sample.etaOf σ) (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt σ t) ((VG.Proof.MlDsa.AArch64.Sample.RejBounded.Z σ t).toNat % 16)

theorem Lt_le (σ : State) (t : Nat) : (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt σ t).length ≤ 256 := rbFold_length_le (by simp) _

theorem Lt_succ {σ : State} {t : Nat} (ht : t < 544) :
    VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt σ (t + 1) = rbStep (VG.Proof.MlDsa.AArch64.Sample.etaOf σ) (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt σ t) (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Z σ t) := by
  simp only [VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt]
  rw [Ball.take_succ'' _ (by rw [VG.Proof.MlDsa.AArch64.Sample.RejBounded.X_length]; omega), rbFold_snoc]

/-- What the loop keeps, and the bytes of the output and the coefficients
stored, from the prologue on. -/
structure Base (σ s : State) : Prop where
  env : Env (VG.Proof.MlDsa.AArch64.Sample.RejBounded.spOf σ) σ s
  out : bytesAt s.mem ((VG.Proof.MlDsa.AArch64.Sample.RejBounded.spOf σ).at' 840) 544 = VG.Proof.MlDsa.AArch64.Sample.RejBounded.X σ
  cs : VG.Proof.MlDsa.AArch64.Sample.RejBounded.Consts (VG.Proof.MlDsa.AArch64.Sample.etaOf σ) s

/-- At the start of iteration `t`. -/
structure LAt (σ : State) (t : Nat) (s : State) : Prop where
  base : VG.Proof.MlDsa.AArch64.Sample.RejBounded.Base σ s
  x2 : s.gpr .x2 = (VG.Proof.MlDsa.AArch64.Sample.RejBounded.spOf σ).at' (840 + t)
  x3 : s.gpr .x3 = coeffAddr (σ.gpr .x2) (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt σ t).length
  x4 : (s.gpr .x4).toNat = 256 - (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt σ t).length
  x5 : (s.gpr .x5).toNat = 544 - t
  st : Stored s.mem (σ.gpr .x2) (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt σ t)

/-- After loading byte `t`. -/
structure LB (σ : State) (t : Nat) (s : State) : Prop where
  base : VG.Proof.MlDsa.AArch64.Sample.RejBounded.Base σ s
  x2 : s.gpr .x2 = (VG.Proof.MlDsa.AArch64.Sample.RejBounded.spOf σ).at' (840 + (t + 1))
  x3 : s.gpr .x3 = coeffAddr (σ.gpr .x2) (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt σ t).length
  x4 : (s.gpr .x4).toNat = 256 - (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt σ t).length
  x5 : (s.gpr .x5).toNat = 544 - (t + 1)
  x6 : s.gpr .x6 = (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Z σ t).setWidth 64
  x7 : s.gpr .x7 = BitVec.ofNat 64 ((VG.Proof.MlDsa.AArch64.Sample.RejBounded.Z σ t).toNat % 16)
  st : Stored s.mem (σ.gpr .x2) (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt σ t)

/-- After trying the low half-byte of byte `t`. -/
structure LM (σ : State) (t : Nat) (s : State) : Prop where
  base : VG.Proof.MlDsa.AArch64.Sample.RejBounded.Base σ s
  x2 : s.gpr .x2 = (VG.Proof.MlDsa.AArch64.Sample.RejBounded.spOf σ).at' (840 + (t + 1))
  x3 : s.gpr .x3 = coeffAddr (σ.gpr .x2) (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lm σ t).length
  x4 : (s.gpr .x4).toNat = 256 - (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lm σ t).length
  x5 : (s.gpr .x5).toNat = 544 - (t + 1)
  x7 : s.gpr .x7 = BitVec.ofNat 64 ((VG.Proof.MlDsa.AArch64.Sample.RejBounded.Z σ t).toNat / 16)
  st : Stored s.mem (σ.gpr .x2) (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lm σ t)

section
variable {σ : State} (hp : rbK.pre σ)
include hp

theorem spOk : SpOk (VG.Proof.MlDsa.AArch64.Sample.RejBounded.spOf σ) σ :=
  ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1,
    hp.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.1, by show (66 : Nat) < 2 ^ 64; decide⟩

theorem eta : VG.Proof.MlDsa.AArch64.Sample.etaOf σ = 2 ∨ VG.Proof.MlDsa.AArch64.Sample.etaOf σ = 4 := hp.2.2.2.2.2.2.2.2.2

theorem Base.keepA {s s' : State} (h : VG.Proof.MlDsa.AArch64.Sample.RejBounded.Base σ s) {regs : List Reg} (hk : Keep regs s s')
    (hf : Frame [polyR (σ.gpr .x2)] s.mem s'.mem) (hr : ∀ r ∈ regs, r ∉ preserved := by decide)
    (hc : ∀ r ∈ regs, r ∉ [Reg.x9, .x10, .x11, .x15, .x16, .x17] := by decide) : VG.Proof.MlDsa.AArch64.Sample.RejBounded.Base σ s' :=
  ⟨h.env.keepA (VG.Proof.MlDsa.AArch64.Sample.RejBounded.spOk hp) hk hf hr, by
    rw [MlKem.bytesAt_frame hf (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (a_scr' (VG.Proof.MlDsa.AArch64.Sample.RejBounded.spOk hp) (by omega)).symm) (by omega)]; exact h.out,
    h.cs.keep hk hc⟩

omit hp in
theorem Base.byte {s : State} (h : VG.Proof.MlDsa.AArch64.Sample.RejBounded.Base σ s) {p : Nat} (hp' : p < 544) :
    s.mem ((VG.Proof.MlDsa.AArch64.Sample.RejBounded.spOf σ).at' (840 + p)) = VG.Proof.MlDsa.AArch64.Sample.RejBounded.Z σ p := by
  rw [← at_add, ← MlKem.bytesAt_getD s.mem _ hp', h.out]

theorem inA' {s : State} (h : VG.Proof.MlDsa.AArch64.Sample.RejBounded.Base σ s) {i : Nat} (hi : i < 256) :
    InRegions s.wr (coeffAddr (σ.gpr .x2) i) 4 := inA (VG.Proof.MlDsa.AArch64.Sample.RejBounded.spOk hp) h.env.wr hi

/-- The load of byte `t`. -/
theorem load_ok {t : Nat} (ht : t < 544) {s : State} (h : VG.Proof.MlDsa.AArch64.Sample.RejBounded.LAt σ t s) : WP isa (.block rbLoad) s (VG.Proof.MlDsa.AArch64.Sample.RejBounded.LB σ t) := by
  refine wp_ldrb (a := (VG.Proof.MlDsa.AArch64.Sample.RejBounded.spOf σ).at' (840 + t)) (by decide) (by rw [h.x2, ptr_zero])
    (inScrRd (VG.Proof.MlDsa.AArch64.Sample.RejBounded.spOk hp) h.base.env.rd h.base.env.wr (by omega)) fun s₁ o₁ e₁ => ?_
  refine wp_addImm (by decide) fun s₂ o₂ e₂ => wp_subImm (by decide) fun s₃ o₃ e₃ => wp_and fun s₄ o₄ e₄ =>
    wp_nil ?_
  have k := ((o₁.keep.trans o₂.keep).trans o₃.keep).trans o₄.keep
  have m : s₄.mem = s.mem := by rw [o₄.mem, o₃.mem, o₂.mem, o₁.mem]
  have x6 : s₄.gpr .x6 = (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Z σ t).setWidth 64 := by
    rw [o₄.get .x6, o₃.get .x6, o₂.get .x6, e₁, h.base.byte ht]
  refine ⟨h.base.keepA hp k (by rw [m]; exact Frame.refl _ _), ?_, by rw [k.get .x3, h.x3],
    by rw [k.get .x4, h.x4], ?_, x6, ?_, by rw [m]; exact h.st⟩
  · rw [o₄.get .x2, o₃.get .x2, e₂, o₁.get .x2, h.x2, at_add, Nat.add_assoc]
  · rw [o₄.get .x5, e₃, o₂.get .x5, o₁.get .x5, toNat_sub_n (by rw [h.x5]; simp; omega), h.x5]; simp; omega
  · apply BitVec.eq_of_toNat_eq
    rw [e₄, Proof.MlKem.AArch64.toNat_and_mask _ _ (k := 4) (by
        rw [o₃.get .x11, o₂.get .x11, o₁.get .x11, h.base.cs.x11]; rfl),
      o₃.get .x6, o₂.get .x6, e₁, toNat_byte, h.base.byte ht, BitVec.toNat_ofNat]
    have := (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Z σ t).isLt
    omega

/-- The try of the low half-byte of byte `t`, when `j < 256`. -/
theorem lo_ok {t : Nat} {s : State} (h : VG.Proof.MlDsa.AArch64.Sample.RejBounded.LB σ t s) (hl : (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt σ t).length < 256) :
    WP isa (.block (rbTry (VG.Proof.MlDsa.AArch64.Sample.etaOf σ) ++ ([.lsr .x .x7 .x6 4] : List Instr))) s (VG.Proof.MlDsa.AArch64.Sample.RejBounded.LM σ t) := by
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.RejBounded.try_ok (VG.Proof.MlDsa.AArch64.Sample.RejBounded.eta hp) (L := VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt σ t) (by omega) h.base.cs h.x7 h.x3 h.x4 hl h.st
    (VG.Proof.MlDsa.AArch64.Sample.RejBounded.inA' hp h.base hl)) fun s₁ ⟨k₁, f₁, x3, x4, st⟩ => wp_lsr (by decide) fun s₂ o₂ e₂ => wp_nil ?_
  refine ⟨(h.base.keepA hp k₁ f₁).keepA hp o₂.keep (by rw [o₂.mem]; exact Frame.refl _ _),
    by rw [o₂.get .x2, k₁.get .x2, h.x2], by rw [o₂.get .x3, x3], by rw [o₂.get .x4, x4],
    by rw [o₂.get .x5, k₁.get .x5, h.x5], ?_, by rw [o₂.mem]; exact st⟩
  apply BitVec.eq_of_toNat_eq
  rw [e₂, toNat_lsr, k₁.get .x6, h.x6, toNat_byte, BitVec.toNat_ofNat]
  have := (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Z σ t).isLt
  omega

/-- The try of the high half-byte of byte `t`, when `j < 256` still. -/
theorem hi_ok {t : Nat} (ht : t < 544) {s : State} (h : VG.Proof.MlDsa.AArch64.Sample.RejBounded.LM σ t s) (hl : (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lm σ t).length < 256) :
    WP isa (.block (rbTry (VG.Proof.MlDsa.AArch64.Sample.etaOf σ))) s (VG.Proof.MlDsa.AArch64.Sample.RejBounded.LAt σ (t + 1)) := by
  have hl0 : (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt σ t).length < n := by
    have := hbTry_length (VG.Proof.MlDsa.AArch64.Sample.etaOf σ) (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt σ t) ((VG.Proof.MlDsa.AArch64.Sample.RejBounded.Z σ t).toNat % 16)
    simp only [VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lm, n] at hl ⊢
    omega
  have e : VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt σ (t + 1) = hbTry (VG.Proof.MlDsa.AArch64.Sample.etaOf σ) (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lm σ t) ((VG.Proof.MlDsa.AArch64.Sample.RejBounded.Z σ t).toNat / 16) := by
    rw [VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt_succ ht, rbStep, ifT hl0, ifT (show (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lm σ t).length < n from hl)]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.RejBounded.try_ok (VG.Proof.MlDsa.AArch64.Sample.RejBounded.eta hp) (L := VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lm σ t) (by have := (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Z σ t).isLt; omega) h.base.cs h.x7 h.x3 h.x4 hl
    h.st (VG.Proof.MlDsa.AArch64.Sample.RejBounded.inA' hp h.base hl)) fun s₁ ⟨k₁, f₁, x3, x4, st⟩ => ?_
  rw [← e] at x3 x4 st
  exact ⟨h.base.keepA hp k₁ f₁, by rw [k₁.get .x2, h.x2], x3, x4, by rw [k₁.get .x5, h.x5], st⟩

omit hp in
/-- `j = 256` after the low half-byte: the iteration is done. -/
theorem lo_full {t : Nat} (ht : t < 544) {s : State} (h : VG.Proof.MlDsa.AArch64.Sample.RejBounded.LM σ t s) (hl' : (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt σ t).length < 256)
    (hl : (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lm σ t).length = 256) : VG.Proof.MlDsa.AArch64.Sample.RejBounded.LAt σ (t + 1) s := by
  have e : VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt σ (t + 1) = VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lm σ t := by
    rw [VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt_succ ht, rbStep, ifT (show (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt σ t).length < n from hl'),
      ifF (show ¬ (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lm σ t).length < n by simp only [n]; omega)]
  exact ⟨h.base, h.x2, by rw [e, h.x3], by rw [e, h.x4], h.x5, by rw [e]; exact h.st⟩

omit hp in
/-- `j = 256` before byte `t`: the iteration does nothing but its load. -/
theorem full {t : Nat} (ht : t < 544) {s : State} (h : VG.Proof.MlDsa.AArch64.Sample.RejBounded.LB σ t s) (hl : (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt σ t).length = 256) :
    VG.Proof.MlDsa.AArch64.Sample.RejBounded.LAt σ (t + 1) s := by
  have e : VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt σ (t + 1) = VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt σ t := by rw [VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt_succ ht, rbStep, ifF (by simp only [n]; omega)]
  exact ⟨h.base, h.x2, by rw [e, h.x3], by rw [e, h.x4], h.x5, by rw [e]; exact h.st⟩

omit hp in
theorem eval_x4 {s : State} {L : List Zq} (h : (s.gpr .x4).toNat = 256 - L.length) (hl : L.length ≤ 256) :
    isa.eval (.zero .x .x4) s = some (decide (L.length = 256)) := by
  rw [VG.Proof.MlKem.AArch64.eval_zero, eq_zero_iff, h]
  congr 1
  exact decide_eq_decide.mpr (by omega)

/-- An iteration. -/
theorem step_ok {t : Nat} (ht : t < 544) {s : State} (h : VG.Proof.MlDsa.AArch64.Sample.RejBounded.LAt σ t s) :
    WP isa (rbBody (VG.Proof.MlDsa.AArch64.Sample.etaOf σ)) s fun s' => VG.Proof.MlDsa.AArch64.Sample.RejBounded.LAt σ (t + 1) s' ∧ ((s'.gpr .x5).toNat ≠ 0 ↔ t + 1 ≠ 544) := by
  have c5 : ∀ {u : State}, (u.gpr .x5).toNat = 544 - (t + 1) → ((u.gpr .x5).toNat ≠ 0 ↔ t + 1 ≠ 544) :=
    fun h5 => by rw [h5]; omega
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sample.RejBounded.load_ok hp ht h) fun s₁ h₁ => ?_)
  by_cases hf : (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt σ t).length = 256
  · exact WP.ite true (by rw [VG.Proof.MlDsa.AArch64.Sample.RejBounded.eval_x4 h₁.x4 (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt_le σ t), decide_eq_true hf]) (fun _ =>
      wp_nil ⟨VG.Proof.MlDsa.AArch64.Sample.RejBounded.full ht h₁ hf, c5 h₁.x5⟩) (fun h => nomatch h)
  refine WP.ite false (by rw [VG.Proof.MlDsa.AArch64.Sample.RejBounded.eval_x4 h₁.x4 (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt_le σ t), decide_eq_false hf]) (fun h => nomatch h) fun _ => ?_
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sample.RejBounded.lo_ok hp h₁ (by have := VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt_le σ t; omega)) fun s₂ h₂ => ?_)
  have hml : (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lm σ t).length ≤ 256 := by
    have := hbTry_length (VG.Proof.MlDsa.AArch64.Sample.etaOf σ) (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt σ t) ((VG.Proof.MlDsa.AArch64.Sample.RejBounded.Z σ t).toNat % 16)
    have := VG.Proof.MlDsa.Sample.halfByteOk_le (VG.Proof.MlDsa.AArch64.Sample.etaOf σ) ((VG.Proof.MlDsa.AArch64.Sample.RejBounded.Z σ t).toNat % 16)
    have := VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt_le σ t
    simp only [VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lm]; omega
  by_cases hf' : (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lm σ t).length = 256
  · exact WP.ite true (by rw [VG.Proof.MlDsa.AArch64.Sample.RejBounded.eval_x4 h₂.x4 hml, decide_eq_true hf']) (fun _ =>
      wp_nil ⟨VG.Proof.MlDsa.AArch64.Sample.RejBounded.lo_full ht h₂ (by have := VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt_le σ t; omega) hf', c5 h₂.x5⟩) (fun h => nomatch h)
  · exact WP.ite false (by rw [VG.Proof.MlDsa.AArch64.Sample.RejBounded.eval_x4 h₂.x4 hml, decide_eq_false hf']) (fun h => nomatch h) fun _ =>
      WP.mono (VG.Proof.MlDsa.AArch64.Sample.RejBounded.hi_ok hp ht h₂ (by omega)) fun s₃ h₃ => ⟨h₃, c5 (by rw [h₃.x5])⟩

theorem movz_rbBound : ((BitVec.ofNat 16 (rbBound (VG.Proof.MlDsa.AArch64.Sample.etaOf σ))).setWidth 64) = BitVec.ofNat 64 (rbB (VG.Proof.MlDsa.AArch64.Sample.etaOf σ)) := by
  rcases VG.Proof.MlDsa.AArch64.Sample.RejBounded.eta hp with h | h <;> rw [h] <;> rfl

omit hp in
theorem x27_eq {s : State} (he : Env (VG.Proof.MlDsa.AArch64.Sample.RejBounded.spOf σ) σ s) : s.gpr .x27 = BitVec.ofNat 64 (VG.Proof.MlDsa.AArch64.Sample.etaOf σ) := by
  rw [he.x27]
  apply BitVec.eq_of_toNat_eq
  simp

/-- After the sponge. -/
theorem setup_ok {s : State} (h : J6 136 544 (VG.Proof.MlDsa.AArch64.Sample.RejBounded.spOf σ) σ s) :
    WP isa (.block (rbSetup (VG.Proof.MlDsa.AArch64.Sample.etaOf σ))) s (VG.Proof.MlDsa.AArch64.Sample.RejBounded.LAt σ 0) := by
  unfold rbSetup movQ
  refine wp_addImm (by decide) fun s₁ o₁ e₁ => wp_mov fun s₂ o₂ e₂ => wp_movz fun s₃ o₃ e₃ =>
    wp_movz fun s₄ o₄ e₄ => RejNtt.movQ_ok fun s₅ o₅ e₅ => wp_mov fun s₆ o₆ e₆ => wp_movz fun s₇ o₇ e₇ =>
    wp_movz fun s₈ o₈ e₈ => wp_movz fun s₉ o₉ e₉ => wp_movz fun s₁₀ o₁₀ e₁₀ => wp_nil ?_
  have k := (((((((((o₁.keep.trans o₂.keep).trans o₃.keep).trans o₄.keep).trans o₅.keep).trans o₆.keep).trans
    o₇.keep).trans o₈.keep).trans o₉.keep).trans o₁₀.keep)
  have m : s₁₀.mem = s.mem := by
    rw [o₁₀.mem, o₉.mem, o₈.mem, o₇.mem, o₆.mem, o₅.mem, o₄.mem, o₃.mem, o₂.mem, o₁.mem]
  have hL : VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt σ 0 = [] := rfl
  refine ⟨⟨h.env.keep k m, by rw [m, h.out, VG.Proof.MlDsa.AArch64.Sample.RejBounded.X, VG.Proof.MlDsa.Sample.H_eq], ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [o₁₀.get .x9, o₉.get .x9, o₈.get .x9, o₇.get .x9, o₆.get .x9]
    exact BitVec.eq_of_toNat_eq (by rw [e₅, BitVec.toNat_ofNat]; rfl)
  · rw [o₁₀.get .x10, o₉.get .x10, o₈.get .x10, o₇.get .x10, e₆, o₅.get .x27, o₄.get .x27, o₃.get .x27,
      o₂.get .x27, o₁.get .x27, VG.Proof.MlDsa.AArch64.Sample.RejBounded.x27_eq h.env]
  · rw [o₁₀.get .x11, o₉.get .x11, o₈.get .x11, e₇]; rfl
  · rw [o₁₀.get .x15, o₉.get .x15, e₈, VG.Proof.MlDsa.AArch64.Sample.RejBounded.movz_rbBound hp]
  · rw [o₁₀.get .x16, e₉]; rfl
  · rw [e₁₀]; rfl
  · rw [o₁₀.get .x2, o₉.get .x2, o₈.get .x2, o₇.get .x2, o₆.get .x2, o₅.get .x2, o₄.get .x2, o₃.get .x2,
      o₂.get .x2, e₁, h.env.x25]
  · rw [o₁₀.get .x3, o₉.get .x3, o₈.get .x3, o₇.get .x3, o₆.get .x3, o₅.get .x3, o₄.get .x3, o₃.get .x3, e₂,
      o₁.get .x26, h.env.x26, hL]; simp [coeffAddr]
  · rw [o₁₀.get .x4, o₉.get .x4, o₈.get .x4, o₇.get .x4, o₆.get .x4, o₅.get .x4, o₄.get .x4, e₃, hL]; rfl
  · rw [o₁₀.get .x5, o₉.get .x5, o₈.get .x5, o₇.get .x5, o₆.get .x5, o₅.get .x5, e₄]; rfl
  · rw [m, hL]; exact stored_nil _ _

theorem loop_ok {s : State} (h : J6 136 544 (VG.Proof.MlDsa.AArch64.Sample.RejBounded.spOf σ) σ s) :
    WP isa (rbLoop (VG.Proof.MlDsa.AArch64.Sample.etaOf σ)) s (VG.Proof.MlDsa.AArch64.Sample.RejBounded.LAt σ 544) :=
  WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sample.RejBounded.setup_ok hp h) fun _ h0 =>
    count_loop (by decide) (VG.Proof.MlDsa.AArch64.Sample.RejBounded.LAt σ) (fun t ht s hs => VG.Proof.MlDsa.AArch64.Sample.RejBounded.step_ok hp ht hs) h0)

/-- The loop, chosen by `η`. -/
theorem branch_ok {s : State} (h : J6 136 544 (VG.Proof.MlDsa.AArch64.Sample.RejBounded.spOf σ) σ s) :
    WP isa (.seq (.block [.subImm .x .x9 .x27 2]) (.ite (.zero .x .x9) (rbLoop 2) (rbLoop 4))) s
      (VG.Proof.MlDsa.AArch64.Sample.RejBounded.LAt σ 544) := by
  refine WP.seq (wp_subImm (by decide) fun s₁ o₁ e₁ => wp_nil ?_)
  have h6 : J6 136 544 (VG.Proof.MlDsa.AArch64.Sample.RejBounded.spOf σ) σ s₁ := ⟨h.env.keep o₁.keep o₁.mem, by rw [o₁.mem]; exact h.out⟩
  rcases VG.Proof.MlDsa.AArch64.Sample.RejBounded.eta hp with he | he
  · refine WP.ite true (by rw [VG.Proof.MlKem.AArch64.eval_zero, eq_zero_iff, e₁, VG.Proof.MlDsa.AArch64.Sample.RejBounded.x27_eq h.env, he]; rfl) (fun _ => ?_) (fun h => nomatch h)
    have := VG.Proof.MlDsa.AArch64.Sample.RejBounded.loop_ok hp h6; rw [he] at this; exact this
  · refine WP.ite false (by rw [VG.Proof.MlKem.AArch64.eval_zero, eq_zero_iff, e₁, VG.Proof.MlDsa.AArch64.Sample.RejBounded.x27_eq h.env, he]; rfl) (fun h => nomatch h) (fun _ => ?_)
    have := VG.Proof.MlDsa.AArch64.Sample.RejBounded.loop_ok hp h6; rw [he] at this; exact this

omit hp in
/-- After the loop. -/
theorem Lt_544 : VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt σ 544 = rbFold (VG.Proof.MlDsa.AArch64.Sample.etaOf σ) [] (VG.Proof.MlDsa.AArch64.Sample.RejBounded.X σ) := by
  simp only [VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt]; rw [List.take_of_length_le (by rw [VG.Proof.MlDsa.AArch64.Sample.RejBounded.X_length])]

/-- The end: the postcondition, and the calling convention. -/
theorem end_ok {s : State} (h : VG.Proof.MlDsa.AArch64.Sample.RejBounded.LAt σ 544 s) :
    WP isa (.block (retZ ++ epi)) s fun s' => abiPreserved σ s' ∧ rbK.post σ s' := by
  rw [retZ, List.cons_append, List.cons_append, List.nil_append]
  refine wp_subImm (by decide) fun s₁ h₁ e₁ => wp_lsr (by decide) fun s₂ h₂ e₂ => ?_
  have hl := VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt_le σ 544
  have x4 := h.x4
  have st := h.st
  rw [VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt_544] at hl x4 st
  have v0 : (s₂.gpr .x0).toNat = if (rbFold (VG.Proof.MlDsa.AArch64.Sample.etaOf σ) [] (VG.Proof.MlDsa.AArch64.Sample.RejBounded.X σ)).length = 256 then 1 else 0 := by
    have one : (1#64 : BitVec 64).toNat = 1 := rfl
    rw [e₂, toNat_lsr, e₁, BitVec.toNat_sub, x4, one]
    simp only [Nat.reducePow]
    split <;> omega
  refine WP.mono (epi_ok (VG.Proof.MlDsa.AArch64.Sample.RejBounded.spOk hp) (h.base.env.keep (h₁.keep.trans h₂.keep) (by rw [h₂.mem, h₁.mem])))
    fun s' ⟨abi, m, k⟩ => ⟨abi, ?_, fun hf => ?_⟩
  · rw [k.get .x0]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, v0]
    split <;> rfl
  · rw [m, h₂.mem, h₁.mem]
    exact stored_polyIs st hf

theorem pro_ok : WP isa (.block (pro .x3 .x2 (.addImm .w .x27 .x1 0) (.movz .x .x4 66 0))) σ (J0 (VG.Proof.MlDsa.AArch64.Sample.RejBounded.spOf σ) σ) :=
  Sample.pro_ok (VG.Proof.MlDsa.AArch64.Sample.RejBounded.spOk hp) rfl rfl (by decide) rfl
    (fun s hs => ⟨_, rfl, only_write _ _ _ _, by
      simp only [State.write, State.read, ite_true, hs .x1 (by decide) (by decide)]
      congr 1
      exact BitVec.add_zero _⟩)
    (fun s _ => ⟨_, rfl, only_write _ _ _ _, by rfl⟩)

end

theorem correctWith (v : Proof.Sha3.AArch64.Permutation) (σ : State) (hp : rbK.pre σ) :
    ∃ t s', Exec isa (rejBoundedWith v.callee) σ t s' ∧ abiPreserved σ s' ∧ rbK.post σ s' :=
  WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sample.RejBounded.pro_ok hp) fun _ h1 =>
    WP.seq (WP.mono (spongeWith_ok (v := v) (VG.Proof.MlDsa.AArch64.Sample.RejBounded.spOk hp) (rate := 136) (outlen := 544) (by decide) (by decide) h1)
      fun _ h2 => WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sample.RejBounded.branch_ok hp h2) fun _ h3 => VG.Proof.MlDsa.AArch64.Sample.RejBounded.end_ok hp h3)))

theorem correct (σ : State) (hp : rbK.pre σ) :
    ∃ t s', Exec isa rejBounded σ t s' ∧ abiPreserved σ s' ∧ rbK.post σ s' :=
  VG.Proof.MlDsa.AArch64.Sample.RejBounded.correctWith .scalar σ hp

end RejBounded

end VG.Proof.MlDsa.AArch64.Sample

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejBoundedCT`. -/
section

/-!
# ML-DSA on AArch64: `vg_mldsa_rej_bounded_poly`, constant time but for which half-bytes it accepts

Two runs whose leaks agree (which half-bytes of the first 1088 bytes of output
are accepted, `rejBoundedLeak`) and whose pointers and `η` agree leak the
same, piece by piece (`Rel.lean`): the prologue, the sponge and the end by the
taint analysis, and the loop iteration by iteration. At iteration `t`, both
runs have sampled as many coefficients (`rbFold_length_congr`, from
`leak_hbOks`), so `x3` and `x4` agree, and so does whether each half-byte of
byte `t` is accepted: each branch goes the same way, and each store to the
same address. Each piece between the branches is proved constant time by the
taint analysis from `x2` or `x3`, and correctness then describes where both
runs are (`relTaintStep`).
-/

namespace VG.Proof.MlDsa.AArch64.Sample

open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (wp_nil wp_subImm eval_zero eval_nonzero eq_zero_iff ne_zero_iff)
open VG.Impl.MlDsa.AArch64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q H halfByteOk maxBounds n)
open VG.Spec.Sha3 (bytesAt)

namespace RejBounded

section
variable {σ₁ σ₂ : State} (hq : rbK.pub σ₁ σ₂)
include hq

theorem pub_eq : VG.Proof.MlDsa.AArch64.Sample.RejBounded.spOf σ₁ = VG.Proof.MlDsa.AArch64.Sample.RejBounded.spOf σ₂ := by
  rw [VG.Proof.MlDsa.AArch64.Sample.RejBounded.spOf, VG.Proof.MlDsa.AArch64.Sample.RejBounded.spOf, hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1]

theorem eta_eq : VG.Proof.MlDsa.AArch64.Sample.etaOf σ₁ = VG.Proof.MlDsa.AArch64.Sample.etaOf σ₂ := by simp only [VG.Proof.MlDsa.AArch64.Sample.etaOf, hq.2.1]

/-- The two outputs are accepted alike. -/
theorem oks_eq : (VG.Proof.MlDsa.AArch64.Sample.RejBounded.X σ₁).map (hbOks (VG.Proof.MlDsa.AArch64.Sample.etaOf σ₁)) = (VG.Proof.MlDsa.AArch64.Sample.RejBounded.X σ₂).map (hbOks (VG.Proof.MlDsa.AArch64.Sample.etaOf σ₂)) := by
  have h := hq.2.2.2.2.2
  rw [VG.Proof.MlDsa.AArch64.Sample.RejBounded.eta_eq hq] at h ⊢
  exact leak_hbOks h (by decide)

theorem len_eq (t : Nat) : (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt σ₁ t).length = (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt σ₂ t).length := by
  have h := VG.Proof.MlDsa.AArch64.Sample.RejBounded.oks_eq hq
  rw [VG.Proof.MlDsa.AArch64.Sample.RejBounded.eta_eq hq] at h
  simp only [VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt]
  rw [VG.Proof.MlDsa.AArch64.Sample.RejBounded.eta_eq hq]
  exact rbFold_length_congr rfl (by rw [List.map_take, List.map_take, h])

theorem hb_eq {t : Nat} (ht : t < 544) : hbOks (VG.Proof.MlDsa.AArch64.Sample.etaOf σ₁) (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Z σ₁ t) = hbOks (VG.Proof.MlDsa.AArch64.Sample.etaOf σ₂) (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Z σ₂ t) := by
  have := congrArg (fun L => L.getD t (0, 0)) (VG.Proof.MlDsa.AArch64.Sample.RejBounded.oks_eq hq)
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, VG.Proof.MlDsa.AArch64.Sample.RejBounded.Z] at this ⊢
  rw [List.getElem?_eq_getElem (by rw [VG.Proof.MlDsa.AArch64.Sample.RejBounded.X_length]; exact ht), List.getElem?_eq_getElem (by rw [VG.Proof.MlDsa.AArch64.Sample.RejBounded.X_length]; exact ht)]
    at this ⊢
  simpa using this

theorem lm_eq {t : Nat} (ht : t < 544) : (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lm σ₁ t).length = (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lm σ₂ t).length := by
  simp only [VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lm]
  rw [hbTry_length, hbTry_length, VG.Proof.MlDsa.AArch64.Sample.RejBounded.len_eq hq]
  have := congrArg Prod.fst (VG.Proof.MlDsa.AArch64.Sample.RejBounded.hb_eq hq ht)
  simp only [hbOks] at this
  rw [this]

end

theorem taint_load : ∃ h, (taint.check (Taint.ofRegs [.x2]) (.block rbLoad) h).isSome = true := ⟨_, by taint_decide⟩

theorem taint_nil : ∃ h, (taint.check (Taint.ofRegs []) (.block ([] : List Instr)) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem taint_lo {η : Nat} (hη : η = 2 ∨ η = 4) :
    ∃ h, (taint.check (Taint.ofRegs [.x3]) (.block (rbTry η ++ ([.lsr .x .x7 .x6 4] : List Instr))) h).isSome = true := by
  rcases hη with rfl | rfl
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩

theorem taint_hi {η : Nat} (hη : η = 2 ∨ η = 4) :
    ∃ h, (taint.check (Taint.ofRegs [.x3]) (.block (rbTry η)) h).isSome = true := by
  rcases hη with rfl | rfl
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩

section
variable {η : Nat} (hη : η = 2 ∨ η = 4) {t : Nat} (ht : t < 544)
include hη ht

/-- An iteration, in two runs. -/
theorem body_ct : RelCT isa (Rel2 rbK.pre rbK.pub fun σ s => VG.Proof.MlDsa.AArch64.Sample.etaOf σ = η ∧ VG.Proof.MlDsa.AArch64.Sample.RejBounded.LAt σ t s) (rbBody η)
    (Rel2 rbK.pre rbK.pub fun σ s => VG.Proof.MlDsa.AArch64.Sample.etaOf σ = η ∧ VG.Proof.MlDsa.AArch64.Sample.RejBounded.LAt σ (t + 1) s) := by
  obtain ⟨_, tl⟩ := VG.Proof.MlDsa.AArch64.Sample.RejBounded.taint_load
  obtain ⟨_, tn⟩ := VG.Proof.MlDsa.AArch64.Sample.RejBounded.taint_nil
  obtain ⟨_, tlo⟩ := VG.Proof.MlDsa.AArch64.Sample.RejBounded.taint_lo hη
  obtain ⟨_, thi⟩ := VG.Proof.MlDsa.AArch64.Sample.RejBounded.taint_hi hη
  refine RelCT.seq (relTaintStep (J' := fun σ s => VG.Proof.MlDsa.AArch64.Sample.etaOf σ = η ∧ VG.Proof.MlDsa.AArch64.Sample.RejBounded.LB σ t s) [.x2]
    (fun σ s hp ⟨he, h⟩ => WP.mono (VG.Proof.MlDsa.AArch64.Sample.RejBounded.load_ok hp ht h) fun s' h' => ⟨he, h'⟩)
    (fun σ₁ σ₂ s₁ s₂ _ _ hq ⟨_, h₁⟩ ⟨_, h₂⟩ => ⟨by rw [h₁.base.env.sp, h₂.base.env.sp, hq.2.2.2.2.1],
      fun r hr => by rw [List.mem_singleton.mp hr, h₁.x2, h₂.x2, VG.Proof.MlDsa.AArch64.Sample.RejBounded.pub_eq hq]⟩) tl) ?_
  refine RelCT.ite (fun s₁ s₂ ⟨σ₁, σ₂, _, _, hq, ⟨_, h₁⟩, ⟨_, h₂⟩⟩ => by
      rw [VG.Proof.MlDsa.AArch64.Sample.RejBounded.eval_x4 h₁.x4 (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt_le σ₁ t), VG.Proof.MlDsa.AArch64.Sample.RejBounded.eval_x4 h₂.x4 (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt_le σ₂ t), VG.Proof.MlDsa.AArch64.Sample.RejBounded.len_eq hq])
    (RelCT.mono (P := Rel2 rbK.pre rbK.pub fun σ s => (VG.Proof.MlDsa.AArch64.Sample.etaOf σ = η ∧ VG.Proof.MlDsa.AArch64.Sample.RejBounded.LB σ t s) ∧ (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt σ t).length = 256)
      (relTaintStep [] (fun σ s hp ⟨⟨he, h⟩, hl⟩ => wp_nil ⟨he, VG.Proof.MlDsa.AArch64.Sample.RejBounded.full ht h hl⟩)
        (fun σ₁ σ₂ s₁ s₂ _ _ hq ⟨⟨_, h₁⟩, _⟩ ⟨⟨_, h₂⟩, _⟩ =>
          ⟨by rw [h₁.base.env.sp, h₂.base.env.sp, hq.2.2.2.2.1], fun r hr => absurd hr List.not_mem_nil⟩) tn)
      (fun s₁ s₂ ⟨⟨σ₁, σ₂, p₁, p₂, hq, ⟨e₁, h₁⟩, ⟨e₂, h₂⟩⟩, hc⟩ => by
        rw [VG.Proof.MlDsa.AArch64.Sample.RejBounded.eval_x4 h₁.x4 (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt_le σ₁ t)] at hc
        have hl : (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt σ₁ t).length = 256 := by simpa using hc
        exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨⟨e₁, h₁⟩, hl⟩, ⟨⟨e₂, h₂⟩, by rw [← VG.Proof.MlDsa.AArch64.Sample.RejBounded.len_eq hq]; exact hl⟩⟩)
      fun _ _ h => h) ?_
  refine RelCT.mono (P := Rel2 rbK.pre rbK.pub fun σ s => (VG.Proof.MlDsa.AArch64.Sample.etaOf σ = η ∧ VG.Proof.MlDsa.AArch64.Sample.RejBounded.LB σ t s) ∧ (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt σ t).length < 256)
    ?_ (fun s₁ s₂ ⟨⟨σ₁, σ₂, p₁, p₂, hq, ⟨e₁, h₁⟩, ⟨e₂, h₂⟩⟩, hc⟩ => by
      rw [VG.Proof.MlDsa.AArch64.Sample.RejBounded.eval_x4 h₁.x4 (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt_le σ₁ t)] at hc
      have hl : (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt σ₁ t).length ≠ 256 := by simpa using hc
      have := VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt_le σ₁ t
      exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨⟨e₁, h₁⟩, by omega⟩, ⟨⟨e₂, h₂⟩, by rw [← VG.Proof.MlDsa.AArch64.Sample.RejBounded.len_eq hq]; omega⟩⟩)
    fun _ _ h => h
  refine RelCT.seq (relTaintStep (J' := fun σ s => VG.Proof.MlDsa.AArch64.Sample.etaOf σ = η ∧ (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt σ t).length < 256 ∧ VG.Proof.MlDsa.AArch64.Sample.RejBounded.LM σ t s) [.x3]
    (fun σ s hp ⟨⟨he, h⟩, hl⟩ => by
      subst he; exact WP.mono (VG.Proof.MlDsa.AArch64.Sample.RejBounded.lo_ok hp h hl) fun s' h' => ⟨rfl, hl, h'⟩)
    (fun σ₁ σ₂ s₁ s₂ _ _ hq ⟨⟨_, h₁⟩, _⟩ ⟨⟨_, h₂⟩, _⟩ => ⟨by rw [h₁.base.env.sp, h₂.base.env.sp, hq.2.2.2.2.1],
      fun r hr => by rw [List.mem_singleton.mp hr, h₁.x3, h₂.x3, VG.Proof.MlDsa.AArch64.Sample.RejBounded.len_eq hq, hq.2.2.1]⟩) tlo) ?_
  have hml : ∀ σ, (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt σ t).length < 256 → (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lm σ t).length ≤ 256 := fun σ hl => by
    have := hbTry_length (VG.Proof.MlDsa.AArch64.Sample.etaOf σ) (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt σ t) ((VG.Proof.MlDsa.AArch64.Sample.RejBounded.Z σ t).toNat % 16)
    have := VG.Proof.MlDsa.Sample.halfByteOk_le (VG.Proof.MlDsa.AArch64.Sample.etaOf σ) ((VG.Proof.MlDsa.AArch64.Sample.RejBounded.Z σ t).toNat % 16)
    simp only [VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lm]
    omega
  refine RelCT.ite (fun s₁ s₂ ⟨σ₁, σ₂, _, _, hq, ⟨_, l₁, h₁⟩, ⟨_, l₂, h₂⟩⟩ => by
      rw [VG.Proof.MlDsa.AArch64.Sample.RejBounded.eval_x4 h₁.x4 (hml σ₁ l₁), VG.Proof.MlDsa.AArch64.Sample.RejBounded.eval_x4 h₂.x4 (hml σ₂ l₂), VG.Proof.MlDsa.AArch64.Sample.RejBounded.lm_eq hq ht])
    (RelCT.mono (P := Rel2 rbK.pre rbK.pub fun σ s =>
        (VG.Proof.MlDsa.AArch64.Sample.etaOf σ = η ∧ (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt σ t).length < 256 ∧ VG.Proof.MlDsa.AArch64.Sample.RejBounded.LM σ t s) ∧ (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lm σ t).length = 256)
      (relTaintStep [] (fun σ s hp ⟨⟨he, hl, h⟩, hm⟩ => wp_nil ⟨he, VG.Proof.MlDsa.AArch64.Sample.RejBounded.lo_full ht h hl hm⟩)
        (fun σ₁ σ₂ s₁ s₂ _ _ hq ⟨⟨_, _, h₁⟩, _⟩ ⟨⟨_, _, h₂⟩, _⟩ =>
          ⟨by rw [h₁.base.env.sp, h₂.base.env.sp, hq.2.2.2.2.1], fun r hr => absurd hr List.not_mem_nil⟩) tn)
      (fun s₁ s₂ ⟨⟨σ₁, σ₂, p₁, p₂, hq, ⟨e₁, l₁, h₁⟩, ⟨e₂, l₂, h₂⟩⟩, hc⟩ => by
        rw [VG.Proof.MlDsa.AArch64.Sample.RejBounded.eval_x4 h₁.x4 (hml σ₁ l₁)] at hc
        have hm : (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lm σ₁ t).length = 256 := by simpa using hc
        exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨⟨e₁, l₁, h₁⟩, hm⟩, ⟨⟨e₂, l₂, h₂⟩, by rw [← VG.Proof.MlDsa.AArch64.Sample.RejBounded.lm_eq hq ht]; exact hm⟩⟩)
      fun _ _ h => h)
    (RelCT.mono (P := Rel2 rbK.pre rbK.pub fun σ s =>
        (VG.Proof.MlDsa.AArch64.Sample.etaOf σ = η ∧ (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lt σ t).length < 256 ∧ VG.Proof.MlDsa.AArch64.Sample.RejBounded.LM σ t s) ∧ (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lm σ t).length < 256)
      (relTaintStep [.x3] (fun σ s hp ⟨⟨he, _, h⟩, hm⟩ => by
          subst he; exact WP.mono (VG.Proof.MlDsa.AArch64.Sample.RejBounded.hi_ok hp ht h hm) fun s' h' => ⟨rfl, h'⟩)
        (fun σ₁ σ₂ s₁ s₂ _ _ hq ⟨⟨_, _, h₁⟩, _⟩ ⟨⟨_, _, h₂⟩, _⟩ =>
          ⟨by rw [h₁.base.env.sp, h₂.base.env.sp, hq.2.2.2.2.1],
            fun r hr => by rw [List.mem_singleton.mp hr, h₁.x3, h₂.x3, VG.Proof.MlDsa.AArch64.Sample.RejBounded.lm_eq hq ht, hq.2.2.1]⟩) thi)
      (fun s₁ s₂ ⟨⟨σ₁, σ₂, p₁, p₂, hq, ⟨e₁, l₁, h₁⟩, ⟨e₂, l₂, h₂⟩⟩, hc⟩ => by
        rw [VG.Proof.MlDsa.AArch64.Sample.RejBounded.eval_x4 h₁.x4 (hml σ₁ l₁)] at hc
        have hm : (VG.Proof.MlDsa.AArch64.Sample.RejBounded.Lm σ₁ t).length ≠ 256 := by simpa using hc
        have := hml σ₁ l₁
        exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨⟨e₁, l₁, h₁⟩, by omega⟩, ⟨⟨e₂, l₂, h₂⟩, by rw [← VG.Proof.MlDsa.AArch64.Sample.RejBounded.lm_eq hq ht]; omega⟩⟩)
      fun _ _ h => h)

end

/-- The loop's iterations, in two runs. -/
theorem iters_ct {η : Nat} (hη : η = 2 ∨ η = 4) :
    RelCT isa (Rel2 rbK.pre rbK.pub fun σ s => VG.Proof.MlDsa.AArch64.Sample.etaOf σ = η ∧ VG.Proof.MlDsa.AArch64.Sample.RejBounded.LAt σ 0 s) (.loop (rbBody η) (.nonzero .x .x5))
      (Rel2 rbK.pre rbK.pub fun σ s => VG.Proof.MlDsa.AArch64.Sample.etaOf σ = η ∧ VG.Proof.MlDsa.AArch64.Sample.RejBounded.LAt σ 544 s) := by
  let I : Nat → State → State → Prop := fun n =>
    Rel2 rbK.pre rbK.pub fun σ s => VG.Proof.MlDsa.AArch64.Sample.etaOf σ = η ∧ 0 < n ∧ n ≤ 544 ∧ VG.Proof.MlDsa.AArch64.Sample.RejBounded.LAt σ (544 - n) s
  refine RelCT.mono (RelCT.loop (M := isa) I (fun n => ?_) 544)
    (fun s₁ s₂ ⟨σ₁, σ₂, p₁, p₂, hq, ⟨e₁, h₁⟩, ⟨e₂, h₂⟩⟩ =>
      ⟨σ₁, σ₂, p₁, p₂, hq, ⟨e₁, by decide, Nat.le_refl _, h₁⟩, ⟨e₂, by decide, Nat.le_refl _, h₂⟩⟩) fun _ _ h => h
  by_cases hn : 0 < n ∧ n ≤ 544
  · have ht : 544 - n < 544 := by omega
    refine RelCT.mono (VG.Proof.MlDsa.AArch64.Sample.RejBounded.body_ct hη ht) (fun s₁ s₂ ⟨σ₁, σ₂, p₁, p₂, hq, ⟨e₁, _, _, h₁⟩, ⟨e₂, _, _, h₂⟩⟩ =>
      ⟨σ₁, σ₂, p₁, p₂, hq, ⟨e₁, h₁⟩, ⟨e₂, h₂⟩⟩) ?_
    intro s₁ s₂ ⟨σ₁, σ₂, p₁, p₂, hq, ⟨e₁, h₁⟩, ⟨e₂, h₂⟩⟩
    have c : ∀ {u : State}, (u.gpr .x5).toNat = 544 - (544 - n + 1) →
        isa.eval (.nonzero .x .x5) u = some (decide (n ≠ 1)) := fun h5 => by
      rw [eval_nonzero, ne_zero_iff, h5]
      exact congrArg some (decide_eq_decide.mpr (by omega))
    refine ⟨by rw [c h₁.x5, c h₂.x5], fun hf => ?_, fun htr => ?_⟩
    · rw [c h₁.x5] at hf
      have : n = 1 := by simpa using hf
      subst this
      exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨e₁, h₁⟩, ⟨e₂, h₂⟩⟩
    · rw [c h₁.x5] at htr
      have : n ≠ 1 := by simpa using htr
      refine ⟨n - 1, by omega, σ₁, σ₂, p₁, p₂, hq, ⟨e₁, by omega, by omega, ?_⟩, ⟨e₂, by omega, by omega, ?_⟩⟩
      · rw [show 544 - (n - 1) = 544 - n + 1 by omega]; exact h₁
      · rw [show 544 - (n - 1) = 544 - n + 1 by omega]; exact h₂
  · exact RelCT.of_false fun s₁ s₂ ⟨_, _, _, _, _, ⟨_, h1, h2, _⟩, _⟩ => hn ⟨h1, h2⟩

theorem rbLoop_ct {η : Nat} (hη : η = 2 ∨ η = 4) :
    RelCT isa (Rel2 rbK.pre rbK.pub fun σ s => J6 136 544 (VG.Proof.MlDsa.AArch64.Sample.RejBounded.spOf σ) σ s ∧ VG.Proof.MlDsa.AArch64.Sample.etaOf σ = η) (rbLoop η)
      (Rel2 rbK.pre rbK.pub fun σ s => VG.Proof.MlDsa.AArch64.Sample.RejBounded.LAt σ 544 s) := by
  have ts : ∃ h, (taint.check (Taint.ofRegs [.x25, .x26, .x27]) (.block (rbSetup η)) h).isSome = true := by
    rcases hη with rfl | rfl
    · exact ⟨_, by taint_decide⟩
    · exact ⟨_, by taint_decide⟩
  obtain ⟨_, ts⟩ := ts
  refine RelCT.mono (RelCT.seq (relTaintStep (J' := fun σ s => VG.Proof.MlDsa.AArch64.Sample.etaOf σ = η ∧ VG.Proof.MlDsa.AArch64.Sample.RejBounded.LAt σ 0 s) [.x25, .x26, .x27]
    (fun σ s hp ⟨h, he⟩ => by
      have := VG.Proof.MlDsa.AArch64.Sample.RejBounded.setup_ok hp h
      rw [he] at this
      exact WP.mono this fun s' h' => ⟨he, h'⟩)
    (fun σ₁ σ₂ s₁ s₂ _ _ hq ⟨h₁, _⟩ ⟨h₂, _⟩ => ⟨by rw [h₁.env.sp, h₂.env.sp, hq.2.2.2.2.1], fun r hr => by
      rcases VG.Proof.MlDsa.AArch64.Sample.mem3 hr with rfl | rfl | rfl
      · rw [h₁.env.x25, h₂.env.x25, VG.Proof.MlDsa.AArch64.Sample.RejBounded.pub_eq hq]
      · rw [h₁.env.x26, h₂.env.x26, VG.Proof.MlDsa.AArch64.Sample.RejBounded.pub_eq hq]
      · rw [h₁.env.x27, h₂.env.x27, VG.Proof.MlDsa.AArch64.Sample.RejBounded.pub_eq hq]⟩) ts) (VG.Proof.MlDsa.AArch64.Sample.RejBounded.iters_ct hη)) (fun _ _ h => h)
    fun s₁ s₂ ⟨σ₁, σ₂, p₁, p₂, hq, ⟨_, h₁⟩, ⟨_, h₂⟩⟩ => ⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩

theorem ctWith (v : Proof.Sha3.AArch64.Permutation) : ConstantTime isa rbK.pre rbK.pub (rejBoundedWith v.callee) := by
  obtain ⟨hint, hhint⟩ := v.mldsaBoundedTaint
  refine RelCT.constantTime (Q := fun _ _ => True) (RelCT.mono (Q := fun _ _ => True)
    (P := Rel2 rbK.pre rbK.pub fun σ s => s = σ)
    ?_ (fun s₁ s₂ h => ⟨s₁, s₂, h.1, h.2.1, h.2.2, rfl, rfl⟩) fun _ _ _ => trivial)
  refine RelCT.seq (relTaintStep (J' := fun σ => J0 (VG.Proof.MlDsa.AArch64.Sample.RejBounded.spOf σ) σ) [.x0, .x2, .x3]
    (fun σ s hp h => by subst h; exact VG.Proof.MlDsa.AArch64.Sample.RejBounded.pro_ok hp) (fun σ₁ σ₂ s₁ s₂ _ _ hq h₁ h₂ => by
      subst h₁ h₂
      exact ⟨hq.2.2.2.2.1, RejNtt.regs3 hq.1 hq.2.2.1 hq.2.2.2.1⟩) (by taint_decide)) ?_
  refine RelCT.seq (vectorRelTaintStep (J' := fun σ => J6 136 544 (VG.Proof.MlDsa.AArch64.Sample.RejBounded.spOf σ) σ) [.x25, .x26, .x27, .x3, .x4]
    (fun σ s hp h => spongeWith_ok (v := v) (VG.Proof.MlDsa.AArch64.Sample.RejBounded.spOk hp) (by decide) (by decide) h) (fun σ₁ σ₂ s₁ s₂ _ _ hq h₁ h₂ => by
      refine ⟨by rw [h₁.env.sp, h₂.env.sp, hq.2.2.2.2.1], fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h₁.env.x25, h₂.env.x25, VG.Proof.MlDsa.AArch64.Sample.RejBounded.pub_eq hq]
      · rw [h₁.env.x26, h₂.env.x26, VG.Proof.MlDsa.AArch64.Sample.RejBounded.pub_eq hq]
      · rw [h₁.env.x27, h₂.env.x27, VG.Proof.MlDsa.AArch64.Sample.RejBounded.pub_eq hq]
      · rw [h₁.x3, h₂.x3, VG.Proof.MlDsa.AArch64.Sample.RejBounded.pub_eq hq]
      · exact toNat_inj h₁.x4 h₂.x4) hhint) ?_
  refine RelCT.seq (RelCT.seq (relTaintStep (J' := fun σ s => J6 136 544 (VG.Proof.MlDsa.AArch64.Sample.RejBounded.spOf σ) σ s ∧
      isa.eval (.zero .x .x9) s = some (decide (VG.Proof.MlDsa.AArch64.Sample.etaOf σ = 2))) []
      (fun σ s hp h => wp_subImm (by decide) fun s₁ o₁ e₁ => wp_nil ⟨⟨h.env.keep o₁.keep o₁.mem,
        by rw [o₁.mem]; exact h.out⟩, by
          rw [VG.Proof.MlKem.AArch64.eval_zero, eq_zero_iff, e₁, VG.Proof.MlDsa.AArch64.Sample.RejBounded.x27_eq h.env]
          rcases VG.Proof.MlDsa.AArch64.Sample.RejBounded.eta hp with he | he <;> rw [he] <;> rfl⟩)
      (fun σ₁ σ₂ s₁ s₂ _ _ hq h₁ h₂ => ⟨by rw [h₁.env.sp, h₂.env.sp, hq.2.2.2.2.1],
        fun r hr => absurd hr List.not_mem_nil⟩) (by taint_decide))
    (RelCT.ite (fun s₁ s₂ ⟨σ₁, σ₂, _, _, hq, ⟨_, c₁⟩, ⟨_, c₂⟩⟩ => by rw [c₁, c₂, VG.Proof.MlDsa.AArch64.Sample.RejBounded.eta_eq hq])
      (RelCT.mono (VG.Proof.MlDsa.AArch64.Sample.RejBounded.rbLoop_ct (.inl rfl)) (fun s₁ s₂ ⟨⟨σ₁, σ₂, p₁, p₂, hq, ⟨h₁, c₁⟩, ⟨h₂, _⟩⟩, hc⟩ => by
          rw [c₁] at hc
          have e : VG.Proof.MlDsa.AArch64.Sample.etaOf σ₁ = 2 := by simpa using hc
          exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨h₁, e⟩, ⟨h₂, by rw [← VG.Proof.MlDsa.AArch64.Sample.RejBounded.eta_eq hq]; exact e⟩⟩) fun _ _ h => h)
      (RelCT.mono (VG.Proof.MlDsa.AArch64.Sample.RejBounded.rbLoop_ct (.inr rfl)) (fun s₁ s₂ ⟨⟨σ₁, σ₂, p₁, p₂, hq, ⟨h₁, c₁⟩, ⟨h₂, _⟩⟩, hc⟩ => by
          rw [c₁] at hc
          have e : VG.Proof.MlDsa.AArch64.Sample.etaOf σ₁ ≠ 2 := by simpa using hc
          have e4 : VG.Proof.MlDsa.AArch64.Sample.etaOf σ₁ = 4 := (VG.Proof.MlDsa.AArch64.Sample.RejBounded.eta p₁).resolve_left e
          exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨h₁, e4⟩, ⟨h₂, by rw [← VG.Proof.MlDsa.AArch64.Sample.RejBounded.eta_eq hq]; exact e4⟩⟩) fun _ _ h => h))) ?_
  exact relTaint [.x25] (fun σ₁ σ₂ s₁ s₂ _ _ hq h₁ h₂ => ⟨by rw [h₁.base.env.sp, h₂.base.env.sp, hq.2.2.2.2.1],
    fun r hr => by rw [List.mem_singleton.mp hr, h₁.base.env.x25, h₂.base.env.x25, VG.Proof.MlDsa.AArch64.Sample.RejBounded.pub_eq hq]⟩) (by taint_decide)

theorem ct : ConstantTime isa rbK.pre rbK.pub rejBounded :=
  VG.Proof.MlDsa.AArch64.Sample.RejBounded.ctWith .scalar

end RejBounded

/-- A state satisfying the precondition. -/
def rbSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 2 | .x2 => 0x2000 | .x3 => 0x3000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 66⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

theorem rejBounded_verifiedWith (v : Proof.Sha3.AArch64.Permutation) : Verified AArch64.target (Impl.MlDsa.AArch64.Sample.rejBoundedWith v.callee)
    (Spec.MlDsa.rejBoundedContract AArch64.abi 16) :=
  Verified.of_correct (RejBounded.correctWith v) (RejBounded.ctWith v)
    { pre := by sig_implies_pre [Spec.MlDsa.rejBoundedContract, Spec.MlDsa.rejBoundedSig, VG.Proof.MlDsa.AArch64.Sample.rbK,
        AArch64.abi, AArch64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.MlDsa.rejBoundedContract, Spec.MlDsa.rejBoundedSig, VG.Proof.MlDsa.AArch64.Sample.rbK, AArch64.abi,
          AArch64.argRegs]
        dsimp only [VG.Proof.MlDsa.AArch64.Sample.rbK] at h
        obtain ⟨hr, hp⟩ := h
        by_cases hf : (rbFold (VG.Proof.MlDsa.AArch64.Sample.etaOf s) [] (H (bytesAt s.mem (s.gpr .x0) 66) 544)).length = 256
        · rw [ifT hf] at hr
          obtain ⟨hred, hpoly⟩ := hp hf
          exact ⟨fun _ => hred, .inl ⟨hr, { Spec.MlDsa.minBounds with rejBounded := 544 }, by
            show Option.map _ (Spec.MlDsa.rejBoundedPoly _ 544 _) = _
            rw [rejBounded_some _ hf, hpoly]⟩⟩
        · rw [ifF hf] at hr
          exact ⟨fun h1 => absurd (hr.symm.trans h1) (by decide),
            .inr ⟨hr, by
              show Option.map _ (Spec.MlDsa.rejBoundedPoly _ Spec.MlDsa.minBounds.rejBounded _) = none
              rw [rejBounded_none (B := 544) _ (by decide) hf]; rfl⟩⟩
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.MlDsa.rejBoundedContract, Spec.MlDsa.rejBoundedSig, VG.Proof.MlDsa.AArch64.Sample.rbK, AArch64.abi,
          AArch64.argRegs] at h
        obtain ⟨hsp, hb, hx0, hx1, hx2, hx3⟩ := h
        exact ⟨hx0, hx1, hx2, hx3, hsp, hb⟩
      sat := by sig_implies_sat [Spec.MlDsa.rejBoundedContract, Spec.MlDsa.rejBoundedSig, VG.Proof.MlDsa.AArch64.Sample.rbK,
        AArch64.abi, AArch64.argRegs] [rbSat] using VG.Proof.MlDsa.AArch64.Sample.rbSat }

theorem rejBounded_verified : Verified AArch64.target Impl.MlDsa.AArch64.Sample.rejBounded
    (Spec.MlDsa.rejBoundedContract AArch64.abi 16) :=
  VG.Proof.MlDsa.AArch64.Sample.rejBounded_verifiedWith .scalar

end VG.Proof.MlDsa.AArch64.Sample

end
