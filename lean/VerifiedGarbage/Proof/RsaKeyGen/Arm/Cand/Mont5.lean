module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Mont4
public import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeState
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Mont1
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeInverse
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeCT
import VerifiedGarbage.Proof.Bignum.Arm.R2CT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Seqs
import VerifiedGarbage.Proof.Rsa.Arm.RvMont4

/-! # A candidate on ARMv7: `−c⁻¹` and `R² mod c`

`precomputeInverse` (`pinv_vp`) and `r2` (`r2_vp`), from `c` in the key
array `mBase`, which is Montgomery multiplication's array 0.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)
open VG.Proof.Rsa.Arm.Recover (VP)

/-- The arrays of the exponent's stage but `c`. -/
abbrev LXm : List Nat := [mBase + 27, aCm1, aTwo, aOne]

/-- After `precomputeInverse`. -/
abbrev SD (P : CP) (E : State → Prop) (σ s : State) : Prop :=
  KX P E LXm σ s ∧ ArithmeticReady P.M0 P.lenM P.w s ∧ numAt s.mem (State.addr P.M0) P.w 0 = cv P σ

/-- After `r2`. -/
abbrev SE (P : CP) (E : State → Prop) (σ s : State) : Prop :=
  SD P E σ s ∧ numAt s.mem (State.addr P.M0) P.w 4 = r2v P σ

section
variable {P : CP}

theorem cv_lt {σ : State} (pre : In P σ) : cv P σ < 2 ^ (64 * P.w) := by
  have := (cv_shape (σ := σ) pre).2.2
  rwa [show 8 * P.L = 64 * P.w by have := pre.L_eq; omega] at this

theorem cv_gt {σ : State} (pre : In P σ) : 1 < cv P σ := by
  have := (cv_shape (σ := σ) pre).2.1
  have : 1 ≤ 2 ^ (8 * P.L - 2) := Nat.one_le_two_pow
  omega

/-- The number of Montgomery multiplication's array 0 is `c`. -/
theorem n0_of {σ s : State} (h : KS P σ (AX P σ) LX (V3 P σ) [sUsed] s) :
    numAt s.mem (State.addr P.M0) P.w 0 = cv P σ := by
  have pre := h.pre
  have e := h.arrs aC (by simp)
  have v : AX P σ aC = cv P σ := by simp (config := {decide := true}) only [AX, A3, A0, upd, ↓reduceIte]
  rw [v] at e
  have e' : num s.mem P.B P.W (mBase + 0) = cv P σ := e
  rw [pre.numAt_eq (by rw [e']; exact cv_lt pre), e']

theorem pmod_of {E : State → Prop} {σ s : State} (h : SC P E σ s) : PrecomputeModulus P.M0 P.lenM P.w s := by
  obtain ⟨⟨e, k⟩, lay, wd, r0, sv⟩ := h
  have pre := k.pre
  have sp : s.sp = P.sp := k.sp.trans pre.sp
  have n0 := n0_of k
  refine ⟨⟨pre.workspaceM k.wr, lay, wd, r0, ⟨P.rFr, by rw [k.rd, k.wr, pre.wr]; simp, ?_⟩, by rw [sp]; exact pre.rW0_rM,
    by rw [sp]; exact sv⟩, by rw [n0]; exact cv_gt pre, by rw [n0]; exact (cv_shape (σ := σ) pre).1⟩
  rw [sp]; simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide

/-- `precomputeInverse`. -/
theorem pinv_vp {E : State → Prop} : VP (SC P E) VG.Impl.Bignum.Arm.precomputeInverse (SD P E) := by
  refine VP.of_ct (fun σ₁ σ₂ => precomputeInverse_ct.mono (fun s t h => ⟨pmod_of h.1, pmod_of h.2⟩)
    fun _ _ _ => trivial) fun σ s h => ?_
  have i := pmod_of h
  obtain ⟨⟨e, k⟩, lay, wd, r0, sv⟩ := h
  have pre := k.pre
  refine WP.mono (precomputeInverse_ok s i.workspace i.layout i.width i.ptr i.odd i.large i.stackRead i.stackSep
    i.saved) fun t ⟨ar, n0, f, rest⟩ => ⟨⟨e, ?_⟩, ar, by rw [n0]; exact n0_of k⟩
  have k' : KS P σ (AX P σ) LXm (V3 P σ) [sUsed] s :=
    k.mono (fun j hj => ⟨by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega, rfl⟩)
      fun d hd => ⟨hd, rfl⟩
  have kp := keep_of_frameM pre f
  refine k'.core kp (by simp only [List.mem_range'_1]; intro j hj; simp only [nArr]; omega) (by simp) rest.sp rest.rd
    rest.wr (k'.arrs_keep kp (fun j hj hj' => by
      simp only [List.mem_range'_1] at hj'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl <;> simp [mBase, aCm1, aTwo, aOne] at hj' <;> omega) (by simp))
    (k'.sl_keep kp (by simp) (by simp)) k'.live_lt k'.ls_ok

theorem countFits {σ : State} (pre : In P σ) : 128 * P.w < 2 ^ 32 := by have := pre.w4; omega

/-- `r2`. -/
theorem r2_vp {E : State → Prop} : VP (SD P E) VG.Impl.Bignum.Arm.r2 (SE P E) := by
  refine VP.ofImp (p := 128 * P.w < 2 ^ 32) (fun σ s h => countFits h.1.2.pre) fun cf => ?_
  refine VP.of_ct (fun σ₁ σ₂ => (r2_ct cf).mono (fun s t h => ⟨h.1.2.1, h.2.2.1, ?_⟩) fun _ _ _ => trivial)
    fun σ s h => ?_
  · rw [h.1.1.2.sp, h.1.1.2.pre.sp, h.2.1.2.sp, h.2.1.2.pre.sp]
  obtain ⟨⟨e, k⟩, ar, n0⟩ := h
  have pre := k.pre
  refine WP.mono (r2_ok s ar cf) fun t ⟨dl, v4, n0', f, rest⟩ => ⟨⟨⟨e, ?_⟩, ?_, by rw [n0', n0]⟩, by rw [v4, n0]⟩
  · have kp := keep_of_frameM pre f
    refine k.core kp (by simp only [List.mem_range'_1]; intro j hj; simp only [nArr]; omega) (by simp) rest.sp
      rest.rd rest.wr (k.arrs_keep kp (fun j hj hj' => by
        simp only [List.mem_range'_1] at hj'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl <;> simp [mBase, aCm1, aTwo, aOne] at hj' <;> omega) (by simp))
      (k.sl_keep kp (by simp) (by simp)) k.live_lt k.ls_ok
  · exact ⟨dl.workspace, dl.layout, dl.width, dl.ptr, dl.inverse, by rw [n0', n0]; exact cv_gt pre, dl.stackRead,
      dl.stackSep, dl.saved⟩

end

end VG.Proof.RsaKeyGen.Arm.Cand
