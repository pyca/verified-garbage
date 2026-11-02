module

public import VerifiedGarbage.Impl.Ed25519.RISCV64.Scalar
import VerifiedGarbage.Proof.Ed25519.Scalar
import VerifiedGarbage.Proof.X25519.RISCV64.AddSub
import VerifiedGarbage.Proof.X25519.RISCV64.Cswap
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ed25519.RISCV64.Base
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.X25519.RISCV64.Field
public import VerifiedGarbage.Spec.Ed25519

/-!
# Ed25519 on RISCV64: whether a scalar is below `L`

`vg_ed25519_verify_equation` checks that the scalar at `SR` is below `L`:
`SR + (2^256 - 1 - L) + 1` goes to `SD`, whose carry out is 1 exactly when
`SR ≥ L` (`subtract_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64 VG.Proof.X25519.RISCV64
open VG.Impl.X25519.RISCV64 (pass)
open VG.Proof.X25519
open VG.Spec.Ed25519 (L)

theorem SR_eq : SR = 160 := rfl
theorem SD_eq : SD = 192 := rfl

theorem L_lt : L < 2 ^ 253 := by decide

theorem scalarComplement_lt (k : Nat) : scalarComplement k < 2 ^ 32 := by
  unfold scalarComplement; omega_arith

/-- The complement's words are those of `2^256 - 1 - L`. -/
theorem val32_complement : val32 scalarComplement 8 = 2 ^ 256 - 1 - L := by decide

/-- A pass's output, as a number: below `2^256`, and with the carry out it is the sum. -/
theorem pass_value {c : Nat → Nat} {cin : Nat} :
    val32 (out c cin) 8 + 2 ^ 256 * chain c cin 8 = val32 c 8 + cin ∧ val32 (out c cin) 8 < 2 ^ 256 :=
  ⟨chain_val c cin 8, val32_lt fun k _ => Nat.mod_lt _ (by decide)⟩

section
variable {b : Addr}

/-- The pass from `SR` to `SD` adding the complement of `L` and 1: its carry out says whether
`SR ≥ L`. -/
theorem subtract_ok {s : State} (hc : Ctx b s) (h8 : s.gpr .a5 = 1) :
    WP isa (.block (pass .a3 SD scalarSubtractSrc)) s fun t =>
      Rest [.a2, .a4, .a5] s t ∧ Frame [⟨b + BitVec.ofNat 64 SD, 32⟩] s.mem t.mem ∧
      (∀ k < 8, limb t.mem b SR k = limb s.mem b SR k) ∧
      (t.gpr .a5).toNat = (if L ≤ V s.mem b SR then 1 else 0) ∧
      (L ≤ V s.mem b SR → V t.mem b SD = V s.mem b SR - L) := by
  have hS := SR_eq
  have hD := SD_eq
  have hl : ∀ k < 8, limb s.mem b SR k < 2 ^ 32 := fun k _ => limb_lt _ _ _ _
  let c : Nat → Nat := fun k => limb s.mem b SR k + scalarComplement k
  refine WP.mono (pass_ok (s0 := s) (c := c) (cin := 1) (by decide)
    (by omega_arith) (fun k hk => by rw [hc.a3]; exact hc.inW (by omega_arith))
    (fun _ _ => by rw [hc.a3]; exact al4 hc.al (by omega_arith)) (by rw [h8]; rfl)
    (fun k hk => by have := hl k hk; have := scalarComplement_lt k; simp only [c]; omega_arith) (by decide) ?_)
    fun t hp => ?_
  · intro k hk s' hp
    have hc' : Ctx b s' := hc.of_rest hp.rest (by decide)
    simp only [scalarSubtractSrc]
    refine lw0_ok hc' (d := SR + 4 * k) (by omega_arith) (by omega_arith) fun t1 v1 =>
      WP.append (ByteLoad.li32_ok (d := .a2) _) fun t2 e2 => ?_
    have v2 : Upd t1 t2 .a2 (sext32 (BitVec.ofNat 32 (scalarComplement k))) := by
      rw [e2]; exact Upd.write _ _ _
    refine wp_sll (by decide) fun t3 v3 => wp_srl (by decide) fun t4 v4 => wp_add fun t5 v5 =>
      WP.block_nil ⟨?_, ?_, ?_⟩
    · have ex : wd s'.mem b (SR + 4 * k) = limb s.mem b SR k := by
        rw [wd_pass hc hp.frame (by omega_arith) (by omega_arith) (by omega_arith)]; rfl
      have e5 : (t4.gpr .a2).toNat = scalarComplement k := by
        rw [v4.gpr, v3.gpr, v2.gpr, li32_zext, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (scalarComplement_lt k)]
      have e7 : (t4.gpr .a4).toNat = limb s.mem b SR k := by
        rw [v4.other _ (by decide), v3.other _ (by decide), v2.other _ (by decide), v1.gpr, toNat_ext32]
        exact ex
      have := hl k hk; have := scalarComplement_lt k
      rw [v5.gpr, toNat_add_lt (by rw [e7, e5]; omega_arith), e7, e5]
    · exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
        ((v4.rest (by decide)).trans (v5.rest (by decide)))))
    · rw [v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]
  · have hf : Frame [⟨b + BitVec.ofNat 64 SD, 32⟩] s.mem t.mem := by have := hp.frame; rwa [hc.a3] at this
    have hpo : ∀ j < 8, limb t.mem b SD j = out c 1 j := fun j hj => by
      have := hp.outs j hj; rwa [hc.a3] at this
    obtain ⟨hv, hlt⟩ := pass_value (c := c) (cin := 1)
    have hcv : val32 c 8 = V s.mem b SR + (2 ^ 256 - 1 - L) := by
      simp only [c]; rw [val32_add, val32_complement]; rfl
    have hVlt := V_lt s.mem b SR
    have := L_lt
    rw [hcv] at hv
    have hch : chain c 1 8 = if L ≤ V s.mem b SR then 1 else 0 := by
      split
      · have : chain c 1 8 ≤ 1 := by
          rcases Nat.lt_or_ge (chain c 1 8) 2 with h | h
          · omega_arith
          · exfalso; have := Nat.mul_le_mul_left (2 ^ 256) h; omega_arith
        rcases Nat.eq_zero_or_pos (chain c 1 8) with h | h
        · rw [h] at hv; omega_arith
        · omega_arith
      · rcases Nat.eq_zero_or_pos (chain c 1 8) with h | h
        · exact h
        · exfalso; have := Nat.mul_le_mul_left (2 ^ 256) h; omega_arith
    refine ⟨hp.rest, hf, fun k hk => ?_, by rw [hp.a5, hch], fun hge => ?_⟩
    · refine wd_frame hf fun r hr => ?_
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
    · rw [V, val32_congr hpo]
      rw [hch, ite_eq_left_iff.mpr (fun h => absurd hge h)] at hv
      omega_arith

end

end VG.Proof.Ed25519.RISCV64
