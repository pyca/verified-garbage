module

public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Stage
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Ops
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Taint5
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.St
import VerifiedGarbage.Proof.Rsa.Arm.RvHalving

/-! # A candidate on ARMv7: the exponent of 2 in `c − 1` (`halving_vp`)

`HS P E k`: after `k` halvings of `c − 1`, the array `aHm` holds the first
of `halveStep^[k] (c − 1, 0)`, the header word `sTc` its second and `sCnt`
the halvings left, `8 out_len − k`. After `8 out_len` of them, `sTc` is the
exponent of 2 in `c − 1` (`hv_done`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa (b2n halveStep)
open VG.Impl.RsaKeyGen.Arm.Key (notS)

/-- `(m, t)` after `k` halvings of `c − 1`. -/
def hv (P : CP) (σ : State) (k : Nat) : Nat × Nat := halveStep^[k] (cv P σ - 1, 0)

def AH (P : CP) (k : Nat) (σ : State) : Nat → Nat := upd (A3 P σ) aHm (hv P σ k).1
abbrev LH : List Nat := aHm :: L3
def VH (P : CP) (k : Nat) (σ : State) : Nat → Nat :=
  upd (upd (V3 P σ) sTc (hv P σ k).2) sCnt (8 * P.L - k)
abbrev LSH : List Nat := sCnt :: sTc :: LS3

/-- After `k` halvings. -/
abbrev HS (P : CP) (E : State → Prop) (k : Nat) : State → State → Prop := St P E (AH P k) LH (VH P k) LSH

section
variable {P : CP}

theorem hv_le (σ : State) (k : Nat) : (hv P σ k).2 ≤ k := by
  induction k with
  | zero => exact Nat.le_of_eq rfl
  | succ k ih =>
    show (halveStep^[k + 1] (cv P σ - 1, 0)).2 ≤ k + 1
    rw [Function.iterate_succ_apply']
    have ih' : (halveStep^[k] (cv P σ - 1, 0)).2 ≤ k := ih
    generalize halveStep^[k] (cv P σ - 1, 0) = st at ih' ⊢
    unfold halveStep
    split
    · show st.2 + 1 ≤ k + 1; omega
    · show st.2 ≤ k + 1; omega

theorem hv_succ (σ : State) (k : Nat) : hv P σ (k + 1) = halveStep (hv P σ k) := by
  rw [hv, Function.iterate_succ_apply']; rfl

theorem hv_lt (σ : State) (pre : In P σ) (k : Nat) : (hv P σ k).1 < 2 ^ (32 * P.W) := by
  have sh := cv_shape (σ := σ) pre
  have p8 : 2 ^ (8 * P.L) ≤ 2 ^ (32 * P.W) := Nat.pow_le_pow_right (by decide) (by simp only [CP.W]; omega)
  have : (hv P σ k).1 ≤ cv P σ - 1 := by
    induction k with
    | zero => exact Nat.le_refl _
    | succ k ih =>
      rw [hv_succ]
      unfold halveStep
      split
      · exact Nat.le_trans (Nat.div_le_self _ _) ih
      · exact ih
  have := sh.2.2
  omega

/-- After `8 out_len` halvings: `(m, t)` with `c − 1 = 2^t m`, `m` odd. -/
theorem hv_done (σ : State) (pre : In P σ) :
    hv P σ (8 * P.L) = ((Spec.Rsa.splitTwos (cv P σ - 1)).2, (Spec.Rsa.splitTwos (cv P σ - 1)).1) := by
  obtain ⟨hodd, hlo, hhi⟩ := cv_shape (σ := σ) pre
  have sz := pre.sizes
  have : 2 ^ 1 ≤ 2 ^ (P.bits - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  exact VG.Proof.Rsa.halve_done (by omega) (by omega)

/-- `m := c − 1`, `t := 0` and the count `8 out_len`. -/
theorem halfInit_vp {E : State → Prop} : VP (S3 P E) halfInit (HS P E 0) := by
  have eI : halfInit = .seq (copy aHm aCm1) (.block (setS sTc 0 ++ ([.ldrSp .r1 foL] ++
      [.mov .r1 (.shifted .r1 .lsl 3), .str .r1 .r8 sCnt]))) := rfl
  rw [eI]
  refine VP.seq (St.pcopy copyHm_taint (by decide) (by simp) (by decide)) ?_
  refine VP.block_append (St.psetS tc0_taint (by decide) (by decide) (by decide)) ?_
  refine VP.block_append (G := fun σ s => St P E (fun σ => upd (A3 P σ) aHm (A3 P σ aCm1)) (aHm :: L3)
      (fun σ => upd (V3 P σ) sTc 0) (sTc :: LS3) σ s ∧ s.gpr .r1 = BitVec.ofNat 32 P.L) ?_ ?_
  · show VP _ (.block ([(Reg.r1, foL)].map fun p => Instr.ldrSp p.1 p.2)) _
    refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨e, h, hw⟩ => ?_
    · rw [h₁.2.1.sp, h₁.2.1.pre.sp, h₂.2.1.sp, h₂.2.1.pre.sp]
    · refine h.ldrSp (o := foL) (by decide) fun t u => WP.block_nil ?_
      have r := u.rest (ws := [.r1]) (by simp)
      exact ⟨⟨e, h.of_rest r u.mem, hw.rest r⟩, by rw [u.gpr, h.pre.wL]⟩
  · refine VP.kv cnt8Tail_taint (fun _ _ h => h.1.2.2) fun σ s ⟨⟨e, h, hw⟩, r1⟩ => ?_
    have pre := h.pre
    have k2 := pre.k2
    refine wp_mov (op2_lsl (by decide)) fun s1 u1 => ?_
    have h1 := h.of_rest (u1.rest (ws := [.r1]) (by simp)) u1.mem
    have hw1 := hw.of_upd u1 (by decide) (by decide) (by decide)
    refine h1.str hw1 (d := sCnt) (by decide) fun t ht hwt _ => WP.block_nil ⟨e, ?_, hwt⟩
    have c : (s1.gpr .r1).toNat = 8 * P.L := by
      rw [u1.gpr, r1, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]; omega
    rw [c] at ht
    refine ht.mono (fun j hj => ⟨by mem_sub, ?_⟩) fun j hj => ⟨by mem_sub, ?_⟩
    · dsimp only
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      have : A3 P σ aCm1 = cv P σ - 1 := by simp (config := {decide := true}) only [A3, upd, ↓reduceIte]
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [upd_self, this]; simp only [AH, upd_self, hv]; rfl
      all_goals simp (config := {decide := true}) only [AH, upd, ↓reduceIte]
    · dsimp only
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [upd_self]; simp only [VH, upd_self]; omega
      · rw [upd_ne _ _ (by decide), upd_self]; simp (config := {decide := true}) only [VH, upd, ↓reduceIte, hv]; rfl
      all_goals simp (config := {decide := true}) only [VH, upd, ↓reduceIte]

end

end VG.Proof.Dsa.Arm.Prime
