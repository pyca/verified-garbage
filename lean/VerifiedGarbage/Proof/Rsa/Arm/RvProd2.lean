module

public import VerifiedGarbage.Proof.Rsa.Arm.RvProd
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # `vg_rsa_recover_primes` on ARMv7: `M = d e` as a piece (`prod_vp`), and the test of `M` (`skip_vp`) -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm

/-- `M = d e`. -/
abbrev Mv (P : RP) (σ : State) : Nat := dv P σ * P.e

/-- The modulus of the product. -/
abbrev mTop (P : RP) : Nat := 2 ^ (32 * P.W - 1)

/-- The arrays with `W` words after the product. -/
def AWp (P : RP) (σ : State) : Nat → Nat := upd (upd (AW1 P σ) wMod (mTop P)) wM (Mv P σ)

section
variable {P : RP}

theorem prod_val {P : RP} {σ : State} (h : In P σ) :
    (0 + P.e % 2 ^ (8 * P.el) * dv P σ) % mTop P = Mv P σ := by
  have he : P.e < 2 ^ (8 * P.el) := by have := bytes_lt σ.mem (State.addr P.eP) P.el; rwa [h.eB] at this
  have hd : dv P σ < 2 ^ (8 * P.dl) := bytes_lt σ.mem (State.addr P.dP) P.dl
  have sz := h.sizes
  have := h.el2; have := h.dl2
  rw [Nat.zero_add, Nat.mod_eq_of_lt he, Nat.mul_comm]
  apply Nat.mod_eq_of_lt
  calc dv P σ * P.e < 2 ^ (8 * P.dl) * 2 ^ (8 * P.el) := Nat.mul_lt_mul'' hd he
    _ = 2 ^ (8 * P.dl + 8 * P.el) := (Nat.pow_add _ _ _).symm
    _ ≤ mTop P := Nat.pow_le_pow_right (by decide) (by simp only [RP.W, RP.w, RP.w6]; omega)

theorem prod_vp {E : State → Prop} :
    VP (fun σ s => E σ ∧ KS P σ (Aload P σ) [aN] (AW1 P σ) [wZ, wE, wD, wM, wMod] (fun _ => 0) [] s) prod
      (fun σ s => E σ ∧ KS P σ (Aload P σ) [aN] (AWp P σ) [wM, wMod, wZ] (fun _ => 0) [] s ∧
        Ws s P.B P.Z P.W 22) := by
  have eP : prod = .seq (.block (ctxW ++ (setTop wMod ++ ([.ldrSp .r6 aoEl] ++
      [.mov .r6 (.shifted .r6 .lsl 3)])))) (mulMod wZ wE wD wM wMod wT) := rfl
  rw [eP]
  -- The stages.
  let K0 := fun σ s => E σ ∧ KS P σ (Aload P σ) [aN] (AW1 P σ) [wZ, wE, wD, wM, wMod] (fun _ => 0) [] s
  let K1 := fun σ s => K0 σ s ∧ Ws s P.B P.Z P.W 22
  let K2 := fun σ s => E σ ∧ KS P σ (Aload P σ) [aN] (upd (AW1 P σ) wMod (mTop P))
    [wMod, wZ, wE, wD, wM, wMod] (fun _ => 0) [] s ∧ Ws s P.B P.Z P.W 22
  let K3 := fun σ s => K2 σ s ∧ s.gpr .r6 = BitVec.ofNat 32 P.el
  let K4 := fun σ s => K2 σ s ∧ s.gpr .r6 = BitVec.ofNat 32 (8 * P.el)
  have ws_regs : ∀ s₁ s₂ : State,
      Ws s₁ P.B P.Z P.W 22 → Ws s₂ P.B P.Z P.W 22 → ∀ r ∈ [Reg.r7, .r8, .r9], s₁.gpr r = s₂.gpr r := by
    intro s₁ s₂ h₁ h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · rw [h₁.r7, h₂.r7]
    · rw [h₁.r8, h₂.r8]
    · rw [h₁.r9, h₂.r9]
  refine VP.seq (G := K4) (VP.block_append (G := K1) ?_ (VP.block_append (G := K2) ?_
    (VP.block_append (G := K3) ?_ ?_))) ?_
  -- `ctxW`.
  · refine VP.taint [.r8] ctxW_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s h => ?_
    · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.r8, h₂.2.r8]
    · exact WP.mono (ctxW_ok h.2.bs h.2.r8 h.2.cnt) fun t ⟨ht, r, m⟩ =>
        ⟨⟨h.1, h.2.of_rest r m (by decide)⟩, ht⟩
  -- The modulus.
  · refine VP.taint [.r7, .r8, .r9] setTop_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ =>
      ws_regs s₁ s₂ h₁.2 h₂.2) fun σ s ⟨⟨e, h⟩, hw⟩ => ?_
    rw [← List.append_nil (setTop wMod)]
    refine setTop_ok hw (j := wMod) (by decide) (by decide) (by show 1 ≤ 2 * P.w + 2; omega)
      fun t ht k v r => WP.block_nil ⟨e, h.write_W k (by decide) (by simp) (h.r8_of r) r.sp r.rd r.wr ?_
        (by simp only [List.mem_singleton]; rintro j rfl; decide) (by simp), ht⟩
    have z : val32 s.mem (State.addr P.B) (arr P.W wMod) (P.W - 1) = 0 := by
      have e0 : num s.mem P.B P.W wMod = 0 := by rw [h.arrsW wMod (by simp)]; rfl
      have e1 := val32_succ s.mem (State.addr P.B) (arr P.W wMod) (P.W - 1)
      rw [show P.W - 1 + 1 = P.W by simp only [RP.W]; omega] at e1
      change val32 _ _ _ _ = 0 at e0
      omega
    rw [v, z, Nat.zero_add, ← Nat.pow_add]
    congr 1
  -- `e_len`.
  · show VP _ (.block ([(Reg.r6, aoEl)].map fun p => Instr.ldrSp p.1 p.2)) _
    refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨e, h, hw⟩ => ?_
    · rw [h₁.2.1.bs.sp, h₁.2.1.bs.pre.sp, h₂.2.1.bs.sp, h₂.2.1.bs.pre.sp]
    · exact h.bs.ldrSp (o := aoEl) (by decide) (by decide) (by decide) fun t u => WP.block_nil
        ⟨⟨e, h.of_rest (u.rest (ws := [.r6]) (by simp)) u.mem (by decide), hw.of_upd u (by decide) (by decide)
          (by decide)⟩, u.gpr.trans h.bs.pre.aEl⟩
  -- `8 e_len`.
  · refine VP.taint [] shl3_taint (fun _ _ _ _ _ _ r hr => absurd hr (List.not_mem_nil)) fun σ s ⟨⟨e, h, hw⟩, r6⟩ => ?_
    refine wp_mov (op2_lsl (by decide)) fun t u => WP.block_nil ⟨⟨e, h.of_rest (u.rest (ws := [.r6]) (by simp))
      u.mem (by decide), hw.of_upd u (by decide) (by decide) (by decide)⟩, ?_⟩
    rw [u.gpr, r6]
    have := h.bs.pre.el2; have := h.bs.pre.k2
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  -- `mulMod`.
  · refine VP.taint [.r6, .r7, .r8, .r9] mulMod_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_)
      fun σ s ⟨⟨e, h, hw⟩, r6⟩ => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | hr
      · rw [h₁.2, h₂.2]
      · exact ws_regs s₁ s₂ h₁.1.2.2 h₂.1.2.2 r (by simpa using hr)
    have el1 := h.bs.pre.el1; have el2 := h.bs.pre.el2; have k2 := h.bs.pre.k2
    have sz := h.sizes
    refine WP.mono (mulMod_ok hw (by decide) (by decide) (by omega) (by omega) r6)
      fun t ⟨ht, k, r, v⟩ => ⟨e, ?_, ht⟩
    have g : ∀ j, j ∈ [wMod, wZ, wE, wD, wM, wMod] → num s.mem P.B P.W j = upd (AW1 P σ) wMod (mTop P) j :=
      fun j hj => h.arrsW j hj
    have gZ : num s.mem P.B P.W wZ = 0 := by rw [g wZ (by simp)]; simp [AW1, upd, wZ, wMod, wD, wE]
    have gE : num s.mem P.B P.W wE = P.e := by rw [g wE (by simp)]; simp [AW1, upd, wMod, wD, wE]
    have gD : num s.mem P.B P.W wD = dv P σ := by rw [g wD (by simp)]; simp [AW1, upd, wMod, wD]
    have gA : num s.mem P.B P.W wM = 0 := by rw [g wM (by simp)]; simp [AW1, upd, wM, wMod, wD, wE]
    have gM : num s.mem P.B P.W wMod = mTop P := by rw [g wMod (by simp)]; simp [upd]
    have dl2 := h.bs.pre.dl2
    have hmt : 0 < mTop P := Nat.two_pow_pos _
    have hd : dv P σ < mTop P := by
      have hb := bytes_lt σ.mem (State.addr P.dP) P.dl
      exact Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) (by simp only [RP.W, RP.w, RP.w6]; omega))
    have vM := v gZ (by rw [gA, gM]; exact hmt) (by rw [gD, gM]; exact hd)
      (by rw [gM, show 2 * mTop P = 2 ^ (32 * P.W - 1 + 1) by rw [Nat.pow_succ, Nat.mul_comm],
          show 32 * P.W - 1 + 1 = 32 * P.W by simp only [RP.W]; omega])
    rw [gA, gE, gD, gM, prod_val h.bs.pre] at vM
    refine h.core k (fun j hj => by
        simp only [mulArrs, List.mem_cons, List.not_mem_nil, or_false] at hj
        exact fitZ_W sz (by rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro d (rfl | rfl) <;> decide)
      (by rw [r.gpr _ (by decide), h.r8]) r.sp r.rd r.wr
      (h.arrs_W k (by simp only [List.mem_singleton]; rintro j rfl; decide) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro d (rfl | rfl) <;> decide))
      h.live_lt ?_ (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro j (rfl | rfl | rfl) <;> decide)
      (by simp) (by simp)
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl
    · rw [vM]; simp [AWp, upd]
    · rw [k.num (by decide) (by decide) (fit_W sz (by decide)), gM]; simp [AWp, upd, wM, wMod]
    · rw [k.num (by decide) (by decide) (fit_W sz (by decide)), gZ]; simp [AWp, AW1, upd, wM, wMod, wZ, wE, wD]

end

end VG.Proof.Rsa.Arm.Recover
