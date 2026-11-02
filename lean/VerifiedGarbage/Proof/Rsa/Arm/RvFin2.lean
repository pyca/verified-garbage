module

public import VerifiedGarbage.Proof.Rsa.Arm.RvFin1
import VerifiedGarbage.Proof.Rsa.Arm.InverseCT
import VerifiedGarbage.Proof.Rsa.Arm.RvTaint4
public import VerifiedGarbage.Proof.Rsa.Arm.InvLaw
import VerifiedGarbage.Proof.Rsa.RecoverSubtract

/-! # `vg_rsa_recover_primes` on ARMv7: `p = gcd(y - 1, n)` (`gcd_vp`) -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa (b2n)

/-- `y - 1` modulo `2^(32 w)`, and the factor `gcd(y - 1, n)`. -/
abbrev ym1 (P : RP) (σ : State) (F : FinishInputs P := legacyFinish P) : Nat := sub32 P.w (yF (F := F) P σ) 1
abbrev pF (P : RP) (σ : State) (F : FinishInputs P := legacyFinish P) : Nat := Nat.gcd (ym1 (F := F) P σ) P.n

/-- `inverse`'s start. -/
def AG (P : RP) (σ : State) (F : FinishInputs P := legacyFinish P) : Nat → Nat :=
  upd (upd (upd (upd (upd (upd (upd (upd (fun _ => 0) aN P.n) 0 (ym1 (F := F) P σ)) 1 P.n) aM P.n) 2 1) 3 0) aZero 0)
    aNM (sub32 P.w 0 P.n)
abbrev LG : List Nat := [aNM, aZero, 3, 2, aM, 1, 0, aN]

/-- After `p`. -/
abbrev Fp (P : RP) (E : State → Prop) (F : FinishInputs P := legacyFinish P) : State → State → Prop :=
  Sk P E (fun σ => upd (upd (fun _ => 0) aN P.n) 1 (pF (F := F) P σ)) [1, aN] (fun _ _ => 0) []
    (fun σ => upd (fun _ => 0) sMask (b2n (okF (F := F) P σ))) [sMask] P.w nArr

section
variable {P : RP}

/-- `inverse`'s start. -/
theorem gcdSet_vp (hn : P.n % 2 = 1 ∧ 1 < P.n) (nl : P.n < 2 ^ (32 * P.w)) {E : State → Prop} (F : FinishInputs P := legacyFinish P) :
    VP (Fy (F := F) P E) gcdSet (Sk P E (AG (F := F) P) LG (fun _ _ => 0) [] (fun σ => upd (fun _ => 0) sMask (b2n (okF (F := F) P σ))) [sMask]
      P.w nArr) := by
  have hn0 : 0 < P.n := by omega_arith
  have w1 : 1 < 2 ^ (32 * P.w) := Nat.one_lt_two_pow (by simp only [RP.w]; omega_arith)
  simp only [gcdSet, seqs]
  refine VP.seq ((Sk.psub3 ym1_taint (o := 0) (a := mY) (b := aOne) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) fun σ _ => ⟨?_, ?_⟩).mono (fun _ _ h => h) fun _ _ h => h.1) ?_
  · have e : (upd (upd (AY (F := F) P σ) aZ 0) aOne 1) mY = yF (F := F) P σ := by simp [AY, upd, mY, aZ, aOne]
    rw [e]; exact Nat.lt_trans (F.bounded σ hn0) nl
  · have e : (upd (upd (AY (F := F) P σ) aZ 0) aOne 1) aOne = 1 := by simp [upd, aOne]
    rw [e]; exact w1
  refine VP.seq (Sk.pcopy oneN_taint (o := 1) (a := aN) (by decide) (by decide) (by decide) (by decide)) ?_
  refine VP.seq (Sk.pcopy mN_taint (o := aM) (a := aN) (by decide) (by decide) (by decide) (by decide)) ?_
  refine VP.seq (Sk.pcopy twoZ_taint (o := 2) (a := aZ) (by decide) (by decide) (by decide) (by decide)) ?_
  refine VP.seq (Sk.psetOne setOne2_taint (j := 2) (by decide) (by decide)) ?_
  refine VP.seq (Sk.pcopy threeZ_taint (o := 3) (a := aZ) (by decide) (by decide) (by decide) (by decide)) ?_
  refine VP.seq (Sk.pcopy zeroZ'_taint (o := aZero) (a := aZ) (by decide) (by decide) (by decide)
    (by decide)) ?_
  refine (Sk.psub3 nm_taint (o := aNM) (a := aZero) (b := aM) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) fun σ _ => ⟨?_, ?_⟩).mono (fun _ _ h => h) fun σ s h => Sk.mono h.1 h.1.1 ?_ ?_ ?_
  · exact Nat.lt_of_le_of_lt (Nat.le_of_eq (by simp [upd, aZero, aZ, aM, aOne])) (Nat.two_pow_pos _)
  · exact Nat.lt_of_le_of_lt (Nat.le_of_eq (by simp [upd, aZero, aZ, aM, aN, aOne, AY, mY])) nl
  · intro x hx
    refine ⟨by simp only [LG, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; omega_arith, ?_⟩
    simp only [LG, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [AG, AY, upd, aNM, aZero, aM, aZ, aOne, aN, mY, sub32]
  · intro x hx; simp at hx
  · intro d hd; exact ⟨hd, rfl⟩

/-- `inverse`: `[1] = gcd([0], n)`. -/
theorem inverse_vp [VG.Proof.Rsa.Arm.Keys.InvLaw] (hn : P.n % 2 = 1 ∧ 1 < P.n) (nl : P.n < 2 ^ (32 * P.w)) {E : State → Prop} (F : FinishInputs P := legacyFinish P) :
    VP (Sk P E (AG (F := F) P) LG (fun _ _ => 0) [] (fun σ => upd (fun _ => 0) sMask (b2n (okF (F := F) P σ))) [sMask] P.w nArr)
      inverse (Fp (F := F) P E) := by
  refine VP.of_ct (fun σ₁ σ₂ s t tr1 tr2 u v h e1 e2 =>
    ⟨inverse_ct s t tr1 tr2 u v trivial trivial
      ⟨by rw [h.1.2.2.r7, h.2.2.2.r7], by rw [h.1.2.2.r8, h.2.2.2.r8], by rw [h.1.2.2.r9, h.2.2.2.r9]⟩ e1 e2,
      trivial⟩) fun σ s ⟨e, h, hw⟩ => ?_
  have sz := h.sizes
  refine WP.mono (inverse_ok hw (by decide) (by decide)) fun t ⟨hwt, k, r, f⟩ => ⟨e, ?_, hwt⟩
  have g : ∀ j ∈ LG, num s.mem P.B P.w j = AG (F := F) P σ j := fun j hj => h.arrs j hj
  have vNM : num s.mem P.B P.w aNM = sub32 P.w 0 P.n := by rw [g aNM (by simp)]; simp [AG, upd]
  have vM : num s.mem P.B P.w aM = P.n := by rw [g aM (by simp)]; simp [AG, upd, aM, aZero, aNM]
  have vZ : num s.mem P.B P.w aZero = 0 := by rw [g aZero (by simp)]; simp [AG, upd, aZero, aNM]
  have v0 : num s.mem P.B P.w 0 = ym1 (F := F) P σ := by rw [g 0 (by simp)]; simp [AG, upd, aZero, aNM, aM]
  have v1 : num s.mem P.B P.w 1 = P.n := by rw [g 1 (by simp)]; simp [AG, upd, aZero, aNM, aM]
  have v2 : num s.mem P.B P.w 2 = 1 := by rw [g 2 (by simp)]; simp [AG, upd, aZero, aNM]
  have v3 : num s.mem P.B P.w 3 = 0 := by rw [g 3 (by simp)]; simp [AG, upd, aZero, aNM]
  have hp := (f (by rw [vNM, vM]; unfold sub32; rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega_arith)]; omega_arith) vZ
    (by rw [vM]; exact hn.1) (by rw [vM]; exact hn.2) (by simp only [bank, v0, v1, v2, v3, vM])).1
  rw [v0, vM] at hp
  have fitI : ∀ j ∈ invArrs, arr P.w j + S P.w ≤ P.Z := fun j hj => by
    refine fitZ_w sz ?_
    simp only [invArrs, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  refine h.core k fitI (by decide) (by rw [r.gpr _ (by decide), h.r8]) r.sp r.rd r.wr (fun j hj => ?_) (by decide) (fun j hj => by simp at hj)
    (by decide) (fun d hd => ?_) (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · rw [hp]; simp [upd]
    · rw [k.num (by decide) (by decide) (fit_w sz (by decide)), g aN (by simp)]; simp [AG, upd, aN, aNM, aZero, aM]
  · simp only [List.mem_singleton] at hd; subst hd
    rw [k.slot (by decide) (by decide), h.sl sMask (by simp)]

end

end VG.Proof.Rsa.Arm.Recover
