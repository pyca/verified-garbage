module

public import VerifiedGarbage.Proof.Ed25519.AArch64.Inv.Math
public import VerifiedGarbage.Proof.Divstep.BatchBasic
import VerifiedGarbage.Proof.Divstep.Tc
import VerifiedGarbage.Proof.Divstep.Batch

/-! # The inversion modulo `p` on AArch64: the batches' invariant

After `i` batches from `x < p`, the working space holds `d`, `f`, `g` of
`59 i` divsteps from `(1, p, x)` (`dsI`), and `u`, `v` below `2²⁵⁶` with
`2^(59 i) f ≡ x 2⁵⁹⁰ u` and `2^(59 i) g ≡ x 2⁵⁹⁰ v` modulo `p` (`RInv`;
`u ≡ 0` if `x = 0`). A batch's rows, as the code computes them (five words
`≡` the matrix's combination modulo `2³²⁰`, then shifted, or reduced modulo
`p`), keep it (`step_inv`). -/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64.Inv

open VG.Spec.X25519 VG.Proof.Divstep VG.Proof.Ed25519.Word64

/-- The divsteps' `(d, f, g)` after `i` batches from `x`. -/
def dsI (x i : Nat) : Int × Int × Int := divsteps (59 * i) (1, P, x)

/-- The matrix of batch `i + 1`. -/
abbrev dsM (x i : Nat) : MSt := msteps 59 (MSt.init (dsI x i).1 (dsI x i).2.1 (dsI x i).2.2)

/-- What the working space holds after `i` batches. -/
structure RInv (x i : Nat) (D : Word) (F G U V : Nat) : Prop where
  D : D = BitVec.ofInt 64 (dsI x i).1
  f : sv F = (dsI x i).2.1
  g : sv G = (dsI x i).2.2
  fl : F < 2 ^ 256
  gl : G < 2 ^ 256
  ul : U < 2 ^ 256
  vl : V < 2 ^ 256
  cu : 2 ^ (59 * i) * (dsI x i).2.1 ≡ x * 2 ^ 590 * U [ZMOD P]
  cv : 2 ^ (59 * i) * (dsI x i).2.2 ≡ x * 2 ^ 590 * V [ZMOD P]
  z : x = 0 → (U : Int) ≡ 0 [ZMOD P]

theorem P_odd : (P : Int) % 2 = 1 := by rw [P_val]; norm_num

theorem P_lt : (P : Int) < 2 ^ 255 := by rw [P_val]; norm_num

theorem dsI_odd (x i : Nat) : (dsI x i).1 % 2 = 1 ∧ (dsI x i).2.1 % 2 = 1 :=
  divsteps_odd (by decide) P_odd _

theorem dsI_le {x : Nat} (hx : x < P) (i : Nat) : |(dsI x i).2.1| ≤ P ∧ |(dsI x i).2.2| ≤ P :=
  divsteps_le (by decide) P_odd (by rw [abs_of_nonneg (by positivity)]) (by
    rw [abs_of_nonneg (by positivity)]; exact_mod_cast hx.le) _

theorem dsI_d (x i : Nat) : |(dsI x i).1| ≤ 1 + 2 * (59 * i) := by
  have := divsteps_d (1, (P : Int), (x : Int)) (59 * i)
  simp only [abs_one] at this
  exact_mod_cast this

theorem dsI_succ (x i : Nat) : dsI x (i + 1) = divsteps 59 (dsI x i) := by
  unfold dsI; rw [show 59 * (i + 1) = 59 * i + 59 by ring, divsteps_add]

theorem dsI_zero {x i : Nat} (h : x = 0) : (dsI x i).2.2 = 0 := by
  unfold dsI; rw [h]; exact (divsteps_zero (t := (1, (P : Int), ((0 : Nat) : Int))) (by simp) _).1

/-- The bounds of a batch's matrix. -/
theorem dsM_bnd (x i : Nat) :
    |(dsM x i).u| ≤ 2 ^ 59 ∧ |(dsM x i).v| ≤ 2 ^ 59 ∧ |(dsM x i).q| ≤ 2 ^ 59 ∧
      |(dsM x i).r| ≤ 2 ^ 59 := by
  obtain ⟨b1, b2⟩ := msteps_bnd (dsI x i).1 (dsI x i).2.1 (dsI x i).2.2 59
  exact ⟨le_trans (le_add_of_nonneg_right (abs_nonneg _)) b1,
    le_trans (le_add_of_nonneg_left (abs_nonneg _)) b1,
    le_trans (le_add_of_nonneg_right (abs_nonneg _)) b2,
    le_trans (le_add_of_nonneg_left (abs_nonneg _)) b2⟩

/-- A batch keeps the invariant, given its rows: `WF`, `WG` the five words of
the rows of `f` and `g` (`≡` the matrix's combination modulo `2³²⁰`), and
`U'`, `V'` the rows of `u` and `v` modulo `p`. -/
theorem step_inv {x i : Nat} (hx : x < P) {D : Word} {F G U V : Nat} (h : RInv x i D F G U V)
    {WF WG U' V' : Nat}
    (hWF : (WF : Int) % 2 ^ 320 = ((dsM x i).u * (dsI x i).2.1 + (dsM x i).v * (dsI x i).2.2) % 2 ^ 320)
    (hWG : (WG : Int) % 2 ^ 320 = ((dsM x i).q * (dsI x i).2.1 + (dsM x i).r * (dsI x i).2.2) % 2 ^ 320)
    (hU : (U' : Int) % P = ((dsM x i).u * U + (dsM x i).v * V) % P) (hUl : U' < 2 ^ 256)
    (hV : (V' : Int) % P = ((dsM x i).q * U + (dsM x i).r * V) % P) (hVl : V' < 2 ^ 256) :
    RInv x (i + 1) (BitVec.ofInt 64 (dsM x i).d) (WF / 2 ^ 59 % 2 ^ 256) (WG / 2 ^ 59 % 2 ^ 256)
      U' V' := by
  obtain ⟨_, hF, hG, _, _, _, _, hcu, hcv, hz⟩ := h
  have hodd := (dsI_odd x i).2
  have hm := msteps_mat (d := (dsI x i).1) (g := (dsI x i).2.2) hodd 59
  have hdfg := msteps_dfg 59 (MSt.init (dsI x i).1 (dsI x i).2.1 (dsI x i).2.2)
  have e : dsI x (i + 1) = ((dsM x i).d, (dsM x i).f, (dsM x i).g) := (dsI_succ x i).trans hdfg.symm
  obtain ⟨m1, m2⟩ := hm
  obtain ⟨l1, l2⟩ := dsI_le hx (i + 1)
  rw [e] at l1 l2
  have hP := P_lt
  rw [abs_le] at l1 l2
  have hg0 : x = 0 → (dsM x i).v = 0 := fun hx0 => by
    have hg := dsI_zero (i := i) hx0
    simp only [dsM, MSt.init]
    rw [hg, msteps_g0]
    simp
  generalize hK : (2 : Int) ^ 590 = K at hcu hcv ⊢
  refine ⟨by rw [e], ?_, ?_, Nat.mod_lt _ (by positivity), Nat.mod_lt _ (by positivity), hUl, hVl,
    ?_, ?_, fun hx0 => ?_⟩
  · rw [e]
    exact (shift_rep (by rw [hWF, ← m1]) ⟨by omega, by omega⟩).1
  · rw [e]
    exact (shift_rep (by rw [hWG, ← m2]) ⟨by omega, by omega⟩).1
  · rw [e]
    have hP2 : (2 : Int) ^ (59 * (i + 1)) = 2 ^ (59 * i) * 2 ^ 59 := by rw [← pow_add]; ring_nf
    dsimp only
    rw [hP2, mul_assoc, m1]
    calc 2 ^ (59 * i) * ((dsM x i).u * (dsI x i).2.1 + (dsM x i).v * (dsI x i).2.2)
        = (dsM x i).u * (2 ^ (59 * i) * (dsI x i).2.1) + (dsM x i).v * (2 ^ (59 * i) * (dsI x i).2.2) := by
          ring
      _ ≡ (dsM x i).u * (x * K * U) + (dsM x i).v * (x * K * V) [ZMOD P] :=
          (hcu.mul_left _).add (hcv.mul_left _)
      _ = x * K * ((dsM x i).u * U + (dsM x i).v * V) := by ring
      _ ≡ x * K * U' [ZMOD P] := (Int.ModEq.mul_left _ hU.symm)
      _ = x * 2 ^ 590 * U' := by rw [hK]
  · rw [e]
    have hP2 : (2 : Int) ^ (59 * (i + 1)) = 2 ^ (59 * i) * 2 ^ 59 := by rw [← pow_add]; ring_nf
    dsimp only
    rw [hP2, mul_assoc, m2]
    calc 2 ^ (59 * i) * ((dsM x i).q * (dsI x i).2.1 + (dsM x i).r * (dsI x i).2.2)
        = (dsM x i).q * (2 ^ (59 * i) * (dsI x i).2.1) + (dsM x i).r * (2 ^ (59 * i) * (dsI x i).2.2) := by
          ring
      _ ≡ (dsM x i).q * (x * K * U) + (dsM x i).r * (x * K * V) [ZMOD P] :=
          (hcu.mul_left _).add (hcv.mul_left _)
      _ = x * K * ((dsM x i).q * U + (dsM x i).r * V) := by ring
      _ ≡ x * K * V' [ZMOD P] := (Int.ModEq.mul_left _ hV.symm)
      _ = x * 2 ^ 590 * V' := by rw [hK]
  · have hv := hg0 hx0
    have h0 := (hz hx0).mul_left (dsM x i).u
    rw [mul_zero] at h0
    refine (show (U' : Int) ≡ _ [ZMOD P] from hU).trans ?_
    rw [hv, zero_mul, add_zero]
    exact h0

end VG.Proof.Ed25519.AArch64.Inv
